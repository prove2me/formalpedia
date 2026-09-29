-- Prove2me | Definitions.Def_M4aHerbrand_SIdeleClassGroup
-- name    : M4aHerbrand_SIdeleClassGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2a4f4459-7df8-5419-b441-4b401366ae39
-- title:
--   T-idèle class groups: unit idèles trivial on T
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $F$, the idèle group is $(\mathbb{A}_{R,F})^\times$ for Mathlib's adèle ring (infinite adèles times finite adèles), and $T$ is an arbitrary set of height-one primes of $R$. Two coordinate homomorphisms are introduced: `infPart`, the map on units induced by the first projection to the infinite adèles, and `finPart w`, the map on units induced by evaluation at $w$ of the finite-adèle component, landing in $(F_w)^\times$ for the $w$-adic completion. The subgroup `idelesTrivialOn R F T` consists of those units $x$ with $\mathrm{infPart}(x)=1$ and $\mathrm{finPart}_w(x)=1$ for all $w\in T$; intersecting it with the project's [`NumberField.AdeleRing.unitIdelesOutside R F T`](../def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) (the units whose finite components at every $w\notin T$, and those of the inverse, lie in the valuation ring $\mathcal{O}_w$) gives `unitIdelesTrivialOn R F T`. It is antitone in $T$ and is trivial for $T$ the set of all primes. The $T$-class kernel `sClassKernel R F T` is the join of `principalIdeles R F` (the image of $F^\times$) with `unitIdelesTrivialOn R F T`, and `SIdeleClassGroup R F T` is the quotient of the idèle group by it, a commutative group, equal to the idèle class group when $T$ is everything. The surjection `toSIdeleClass` from the idèle class group has kernel `sUnitClasses R F T`, the image of `unitIdelesTrivialOn R F T`; for $T\subseteq T'$ there are compatible surjections `ofLE` from the $T'$- to the $T$-version, functorial in inclusions. On the descent side, for a Galois descent datum $D$ on the adèles the predicate `StabilizesUnitIdeles D T` says that each $g\in\mathrm{Gal}(F/E)$ maps `unitIdelesTrivialOn R F T` into itself; under it the descended action passes to `SIdeleClassGroup R F T` as a `MulDistribMulAction`, compatibly with `toSIdeleClass`. Finally `repHomOfMulEquivariant` turns an equivariant group homomorphism into a morphism of the associated $\mathbb{Z}$-linear representations, specialised to `toSIdeleClass` and `ofLE`, and `placesOver`, `placesOverPrimes` describe the primes of $\mathcal{O}_F$ lying over a given set of primes of $\mathcal{O}_E$, respectively over a set of rational primes.
--
--   **Relation to Mathlib.** Mathlib supplies the adèle and finite adèle rings, adic completions and their valuation rings, and `Rep.ofMulDistribMulAction`; the idèle class group, the $S$-unit idèle subgroups and the $T$-idèle class group here are the project's own notions, built on the project's `principalIdeles`, `unitIdelesOutside` and adelic Galois descent data.
--
--   **Where it is used.** These quotients provide the Galois modules $C_{F,T}$ used in the cohomological input to class field theory: the projection from the full idèle class group and the change-of-$T$ maps let Tate cohomology computations for $C_F$ be transferred to the $T$-truncated modules, and `placesOver`/`placesOverPrimes` are how the set $T$ is instantiated from a set of places of a subfield or of rational primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_SIdeleClassGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace M4aHerbrand

section comm

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

instance isMulCommutative_ideleClassGroup : IsMulCommutative (IdeleClassGroup R F) := ⟨⟨fun a b => mul_comm a b⟩⟩

end comm

section Carrier

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def infPart : (AdeleRing R F)ˣ →* (InfiniteAdeleRing F)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing R F)).toMonoidHom

def finPart (w : HeightOneSpectrum R) : (AdeleRing R F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map ((RestrictedProduct.evalMonoidHom (fun v : HeightOneSpectrum R => v.adicCompletion F) w).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing R F)).toMonoidHom)

@[simp] lemma coe_infPart_apply (x : (AdeleRing R F)ˣ) : (infPart x : InfiniteAdeleRing F) = (x : AdeleRing R F).1 := rfl

@[simp] lemma coe_finPart_apply (w : HeightOneSpectrum R) (x : (AdeleRing R F)ˣ) :
    (finPart w x : w.adicCompletion F) = (x : AdeleRing R F).2 w := rfl

variable (R F)

def idelesTrivialOn (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ where
  carrier := {x | infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1}
  one_mem' := ⟨map_one _, fun w _ => map_one _⟩
  mul_mem' {x y} hx hy := ⟨by rw [map_mul, hx.1, hy.1, one_mul], fun w hw => by rw [map_mul, hx.2 w hw, hy.2 w hw, one_mul]⟩
  inv_mem' {x} hx := ⟨by rw [map_inv, hx.1, inv_one], fun w hw => by rw [map_inv, hx.2 w hw, inv_one]⟩

variable {R F} in
lemma mem_idelesTrivialOn_iff (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    x ∈ idelesTrivialOn R F T ↔ infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1 := Iff.rfl

lemma idelesTrivialOn_antitone : Antitone (idelesTrivialOn R F) :=
  fun _ _ h _ hx => ⟨hx.1, fun w hw => hx.2 w (h hw)⟩

def unitIdelesTrivialOn (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ :=
  NumberField.AdeleRing.unitIdelesOutside R F T ⊓ idelesTrivialOn R F T

lemma unitIdelesTrivialOn_le_unitIdelesOutside (T : Set (HeightOneSpectrum R)) :
    unitIdelesTrivialOn R F T ≤ NumberField.AdeleRing.unitIdelesOutside R F T := inf_le_left

lemma unitIdelesTrivialOn_le_idelesTrivialOn (T : Set (HeightOneSpectrum R)) :
    unitIdelesTrivialOn R F T ≤ idelesTrivialOn R F T := inf_le_right

variable {R F}

lemma mem_unitIdelesTrivialOn_iff (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    x ∈ unitIdelesTrivialOn R F T ↔
      (∀ w : HeightOneSpectrum R, w ∉ T → (x : AdeleRing R F).2 w ∈ w.adicCompletionIntegers F ∧
        ((x⁻¹ : (AdeleRing R F)ˣ) : AdeleRing R F).2 w ∈ w.adicCompletionIntegers F) ∧
      infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1 := Iff.rfl

lemma unitIdelesTrivialOn_antitone : Antitone (unitIdelesTrivialOn R F) := by
  intro T T' hTT' x hx
  refine ⟨fun w hw => ?_, idelesTrivialOn_antitone R F hTT' hx.2⟩
  by_cases hw' : w ∈ T'
  · have h1 : (x : AdeleRing R F).2 w = 1 := congrArg Units.val (hx.2.2 w hw')
    have h2 : ((x⁻¹ : (AdeleRing R F)ˣ) : AdeleRing R F).2 w = 1 :=
      congrArg Units.val (show finPart w x⁻¹ = 1 by rw [map_inv, hx.2.2 w hw', inv_one])
    exact ⟨h1 ▸ one_mem _, h2 ▸ one_mem _⟩
  · exact hx.1 w hw'

lemma unitIdelesTrivialOn_univ : unitIdelesTrivialOn R F Set.univ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have h1 : (x : AdeleRing R F).1 = 1 := congrArg Units.val hx.2.1
  have h2 : ∀ w, (x : AdeleRing R F).2 w = 1 := fun w => congrArg Units.val (hx.2.2 w (Set.mem_univ w))
  exact Units.ext (Prod.ext h1 (DFunLike.ext _ _ h2))

end Carrier

section SClass

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def sClassKernel (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ :=
  principalIdeles R F ⊔ unitIdelesTrivialOn R F T

def sUnitClasses (T : Set (HeightOneSpectrum R)) : Subgroup (IdeleClassGroup R F) :=
  (unitIdelesTrivialOn R F T).map (QuotientGroup.mk' (principalIdeles R F))

abbrev SIdeleClassGroup (T : Set (HeightOneSpectrum R)) : Type _ := (AdeleRing R F)ˣ ⧸ sClassKernel R F T

instance isMulCommutative_sIdeleClassGroup (T : Set (HeightOneSpectrum R)) :
    IsMulCommutative (SIdeleClassGroup R F T) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

lemma principalIdeles_le_sClassKernel (T : Set (HeightOneSpectrum R)) : principalIdeles R F ≤ sClassKernel R F T := le_sup_left

lemma unitIdelesTrivialOn_le_sClassKernel (T : Set (HeightOneSpectrum R)) : unitIdelesTrivialOn R F T ≤ sClassKernel R F T :=
  le_sup_right

lemma sClassKernel_antitone : Antitone (sClassKernel R F) :=
  fun _ _ h => sup_le_sup_left (unitIdelesTrivialOn_antitone h) _

lemma sClassKernel_univ : sClassKernel R F Set.univ = principalIdeles R F := by
  rw [sClassKernel, unitIdelesTrivialOn_univ, sup_bot_eq]

def toSIdeleClass (T : Set (HeightOneSpectrum R)) : IdeleClassGroup R F →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ (MonoidHom.id _) (principalIdeles_le_sClassKernel R F T)

@[simp] lemma toSIdeleClass_mk (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    toSIdeleClass R F T (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

lemma toSIdeleClass_surjective (T : Set (HeightOneSpectrum R)) : Function.Surjective (toSIdeleClass R F T) :=
  fun c => by obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; exact ⟨QuotientGroup.mk x, toSIdeleClass_mk R F T x⟩

lemma toSIdeleClass_mk_eq_one_iff (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    toSIdeleClass R F T (QuotientGroup.mk x) = 1 ↔ x ∈ sClassKernel R F T :=
  QuotientGroup.eq_one_iff x

lemma ker_toSIdeleClass (T : Set (HeightOneSpectrum R)) : (toSIdeleClass R F T).ker = sUnitClasses R F T := by
  rw [toSIdeleClass, QuotientGroup.ker_map, Subgroup.comap_id, sClassKernel, Subgroup.map_sup,
    QuotientGroup.map_mk'_self, bot_sup_eq, sUnitClasses]

lemma sUnitClasses_antitone : Antitone (sUnitClasses R F) :=
  fun _ _ h => Subgroup.map_mono (unitIdelesTrivialOn_antitone h)

lemma sUnitClasses_univ : sUnitClasses R F Set.univ = ⊥ := by
  rw [sUnitClasses, unitIdelesTrivialOn_univ, Subgroup.map_bot]

namespace SIdeleClassGroup

variable {R F}

def ofLE {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') : SIdeleClassGroup R F T' →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by simpa using sClassKernel_antitone R F h)

@[simp] lemma ofLE_mk {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') (x : (AdeleRing R F)ˣ) :
    ofLE h (QuotientGroup.mk x : SIdeleClassGroup R F T') = QuotientGroup.mk x := rfl

@[simp] lemma ofLE_toSIdeleClass {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') (c : IdeleClassGroup R F) :
    ofLE h (toSIdeleClass R F T' c) = toSIdeleClass R F T c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; rfl

lemma ofLE_surjective {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') : Function.Surjective (ofLE (R := R) (F := F) h) :=
  fun c => by obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; exact ⟨QuotientGroup.mk x, ofLE_mk h x⟩

lemma ofLE_refl (T : Set (HeightOneSpectrum R)) : ofLE (subset_refl T) = MonoidHom.id (SIdeleClassGroup R F T) :=
  QuotientGroup.map_id _

lemma ofLE_comp_ofLE {T T' T'' : Set (HeightOneSpectrum R)} (h : T ⊆ T') (h' : T' ⊆ T'') :
    (ofLE h).comp (ofLE (R := R) (F := F) h') = ofLE (h.trans h') :=
  MonoidHom.ext fun c => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [MonoidHom.comp_apply, ofLE_mk]

end SIdeleClassGroup

end SClass

section Descent

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

namespace IdeleGaloisDescent

@[simp] lemma classAct_mk (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) (x : (AdeleRing R F)ˣ) :
    D.classAct g (QuotientGroup.mk x) = QuotientGroup.mk (D.unitsAct g x) := rfl

lemma classAct_one (D : IdeleGaloisDescent R E F) (c : IdeleClassGroup R F) : D.classAct 1 c = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [classAct_mk, map_one]; rfl

lemma classAct_mul (D : IdeleGaloisDescent R E F) (g h : F ≃ₐ[E] F) (c : IdeleClassGroup R F) :
    D.classAct (g * h) c = D.classAct g (D.classAct h c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [classAct_mk, classAct_mk, classAct_mk, map_mul]; rfl

@[reducible] def classMulDistribMulAction (D : IdeleGaloisDescent R E F) :
    MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup R F) where
  smul g c := D.classAct g c
  one_smul c := D.classAct_one c
  mul_smul g h c := D.classAct_mul g h c
  smul_one g := map_one (D.classAct g)
  smul_mul g x y := map_mul (D.classAct g) x y

lemma classMulDistribMulAction_smul (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F) :
    (letI := D.classMulDistribMulAction; g • c) = D.classAct g c := rfl

def StabilizesUnitIdeles (D : IdeleGaloisDescent R E F) (T : Set (HeightOneSpectrum R)) : Prop :=
  ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing R F)ˣ), x ∈ unitIdelesTrivialOn R F T → D.unitsAct g x ∈ unitIdelesTrivialOn R F T

variable {T : Set (HeightOneSpectrum R)}

lemma sClassKernel_le_comap_unitsAct (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F) :
    sClassKernel R F T ≤ (sClassKernel R F T).comap (D.unitsAct g).toMonoidHom := by
  refine sup_le ?_ fun x hx => unitIdelesTrivialOn_le_sClassKernel R F T (hD g x hx)
  rw [← Subgroup.map_le_iff_le_comap, D.map_principalIdeles g]
  exact principalIdeles_le_sClassKernel R F T

def sClassAct (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F) :
    SIdeleClassGroup R F T →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ (D.unitsAct g).toMonoidHom (D.sClassKernel_le_comap_unitsAct hD g)

@[simp] lemma sClassAct_mk (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F)
    (x : (AdeleRing R F)ˣ) : D.sClassAct hD g (QuotientGroup.mk x) = QuotientGroup.mk (D.unitsAct g x) := rfl

@[simp] lemma sClassAct_toSIdeleClass (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F)
    (c : IdeleClassGroup R F) : D.sClassAct hD g (toSIdeleClass R F T c) = toSIdeleClass R F T (D.classAct g c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; rfl

lemma sClassAct_one (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (c : SIdeleClassGroup R F T) :
    D.sClassAct hD 1 c = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [sClassAct_mk, map_one]; rfl

lemma sClassAct_mul (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g h : F ≃ₐ[E] F)
    (c : SIdeleClassGroup R F T) : D.sClassAct hD (g * h) c = D.sClassAct hD g (D.sClassAct hD h c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [sClassAct_mk, sClassAct_mk, sClassAct_mk, map_mul]; rfl

@[reducible] def sClassMulDistribMulAction (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) :
    MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T) where
  smul g c := D.sClassAct hD g c
  one_smul c := D.sClassAct_one hD c
  mul_smul g h c := D.sClassAct_mul hD g h c
  smul_one g := map_one (D.sClassAct hD g)
  smul_mul g x y := map_mul (D.sClassAct hD g) x y

lemma sClassMulDistribMulAction_smul_toSIdeleClass (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T)
    (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F) :
    (letI := D.sClassMulDistribMulAction hD; g • toSIdeleClass R F T c) = toSIdeleClass R F T (D.classAct g c) :=
  D.sClassAct_toSIdeleClass hD g c

end IdeleGaloisDescent

end Descent

section RepHoms

universe u

variable {G : Type u} [Group G] {M N : Type u} [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]

def repHomOfMulEquivariant (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    Rep.ofMulDistribMulAction G M ⟶ Rep.ofMulDistribMulAction G N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun g => LinearMap.ext fun x => by
    change Additive.ofMul (f (g • Additive.toMul x)) = Additive.ofMul (g • f (Additive.toMul x))
    rw [hf]⟩

@[simp] lemma repHomOfMulEquivariant_hom_apply (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (x : Additive M) : (repHomOfMulEquivariant f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

variable {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {Γ : Type} [Group Γ]

def toSIdeleClassRepHom (T : Set (HeightOneSpectrum R)) [MulDistribMulAction Γ (IdeleClassGroup R F)]
    [MulDistribMulAction Γ (SIdeleClassGroup R F T)]
    (h : ∀ (g : Γ) (c : IdeleClassGroup R F), toSIdeleClass R F T (g • c) = g • toSIdeleClass R F T c) :
    Rep.ofMulDistribMulAction Γ (IdeleClassGroup R F) ⟶ Rep.ofMulDistribMulAction Γ (SIdeleClassGroup R F T) :=
  repHomOfMulEquivariant (toSIdeleClass R F T) h

def SIdeleClassGroup.ofLERepHom {T T' : Set (HeightOneSpectrum R)} (hTT' : T ⊆ T')
    [MulDistribMulAction Γ (SIdeleClassGroup R F T')] [MulDistribMulAction Γ (SIdeleClassGroup R F T)]
    (h : ∀ (g : Γ) (c : SIdeleClassGroup R F T'), SIdeleClassGroup.ofLE hTT' (g • c) = g • SIdeleClassGroup.ofLE hTT' c) :
    Rep.ofMulDistribMulAction Γ (SIdeleClassGroup R F T') ⟶ Rep.ofMulDistribMulAction Γ (SIdeleClassGroup R F T) :=
  repHomOfMulEquivariant (SIdeleClassGroup.ofLE hTT') h

lemma toSIdeleClass_smul_of_descent {E : Type} [Field E] [Algebra E F] (D : IdeleGaloisDescent R E F)
    (T : Set (HeightOneSpectrum R)) [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup R F)]
    [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • c = D.classAct g c)
    (hactS : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T c = toSIdeleClass R F T (D.classAct g c))
    (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F) : toSIdeleClass R F T (g • c) = g • toSIdeleClass R F T c := by
  rw [hact, hactS]

lemma SIdeleClassGroup.ofLE_smul_of_descent {E : Type} [Field E] [Algebra E F] (D : IdeleGaloisDescent R E F)
    {T T' : Set (HeightOneSpectrum R)} (hTT' : T ⊆ T')
    [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T')] [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T)]
    (hactS' : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T' c = toSIdeleClass R F T' (D.classAct g c))
    (hactS : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T c = toSIdeleClass R F T (D.classAct g c))
    (g : F ≃ₐ[E] F) (c : SIdeleClassGroup R F T') :
    SIdeleClassGroup.ofLE hTT' (g • c) = g • SIdeleClassGroup.ofLE hTT' c := by
  obtain ⟨c, rfl⟩ := toSIdeleClass_surjective R F T' c
  rw [hactS', SIdeleClassGroup.ofLE_toSIdeleClass, SIdeleClassGroup.ofLE_toSIdeleClass, hactS]

end RepHoms

end M4aHerbrand

namespace NumberField

variable (E F : Type*) [Field E] [Field F] [Algebra E F]

def placesOver (S : Set (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 F)) :=
  {w | ∃ v ∈ S, w.asIdeal.under (𝓞 E) = v.asIdeal}

variable {E} in
lemma placesOver_mono {S S' : Set (HeightOneSpectrum (𝓞 E))} (h : S ⊆ S') : placesOver E F S ⊆ placesOver E F S' :=
  fun _ ⟨v, hv, hw⟩ => ⟨v, h hv, hw⟩

lemma mem_placesOver_iff (S : Set (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOver E F S ↔ ∃ v ∈ S, w.asIdeal.under (𝓞 E) = v.asIdeal := Iff.rfl

def placesOverPrimes (S : Set Nat.Primes) : Set (HeightOneSpectrum (𝓞 F)) :=
  {w | ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal}

lemma placesOverPrimes_mono {S S' : Set Nat.Primes} (h : S ⊆ S') : placesOverPrimes F S ⊆ placesOverPrimes F S' :=
  fun _ ⟨p, hp, hw⟩ => ⟨p, h hp, hw⟩

lemma mem_placesOverPrimes_iff (S : Set Nat.Primes) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOverPrimes F S ↔ ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := Iff.rfl

end NumberField

end


