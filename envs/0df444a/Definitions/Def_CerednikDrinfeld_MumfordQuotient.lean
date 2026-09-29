-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordQuotient
-- name    : CerednikDrinfeld_MumfordQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3f156340-5f94-5b03-9531-4159c825fac1
-- title:
--   Invariant function fields for group actions on fraction fields
-- statement:
--   The standing context is a field $K$, a group $G$, and a commutative $K$-algebra $M$ carrying an action of $G$ by ring automorphisms that commute with the scalars from $K$; when $M$ is a domain the action is transported to the fraction field. `fracAct` sends $g \in G$ to the automorphism of $\mathrm{Frac}(M)$ induced by $m \mapsto g \cdot m$; it is multiplicative and unital, hence assembles into a (scoped) `MulSemiringAction` of $G$ on $\mathrm{Frac}(M)$ fixing the image of $K$, with the corresponding commutation of the $G$- and $K$-actions. On this the module defines $\mathrm{Frac}(M)^{G}$ in two guises, `invariantIntermediateField` (Mathlib's fixed field, viewed as an intermediate field of $\mathrm{Frac}(M)/K$) and `invariantField` (the same set as a subfield), together with the relative version `invariantFieldOf K G M Γ` $= \{x \mid \gamma \cdot x = x \text{ for all } \gamma \in Γ\}$ for a subgroup $Γ \le G$, again as an intermediate field over $K$; it is antitone in $Γ$, lies above $\mathrm{Frac}(M)^{G}$, and equals it at $Γ = \top$. For a normal subgroup $N$, `residualAct` is the monoid homomorphism from $G$ to the $K$-algebra automorphisms of $\mathrm{Frac}(M)^{N}$ given by $x \mapsto g \cdot x$; it is trivial on $N$, and an element of $\mathrm{Frac}(M)^{N}$ lies in $\mathrm{Frac}(M)^{G}$ exactly when it is fixed by all of these automorphisms.
--
--   `AmbientSemilinearAut K G M` is a structure whose data are a ring automorphism `base` of $K$ and a ring automorphism `map` of $M$, and whose two further fields are the requirements that `map` carry $\iota(c)$ to $\iota(\mathrm{base}\,c)$ for $c \in K$ and that `map` commute with the $G$-action; these form a group under composition. Such an $s$ induces an automorphism `fracMap` of $\mathrm{Frac}(M)$ commuting with $G$ and acting on $K$-constants through `base`, hence restricts to each $\mathrm{Frac}(M)^{Γ}$ (`invMap`, `invMapOf`) and yields `coeffAct` and `coeffActOf Γ`, elements of the project's group [`AlgebraicCurve.SemilinearAut K`](../def/AlgebraicCurve_BaseChangeGalois.html#L15) of pairs (automorphism of the field, automorphism of $K$) compatible with the structure map; `coeffActHom` and `coeffActOfHom` are the resulting group homomorphisms, and this coefficientwise action commutes with the residual action of $G$.
--
--   The final section specialises the notation: `mumfordField` is $\mathrm{Frac}(M)^{G}$; given a $G$-set $W$, a graph $\mathcal{T}$ on $W$ and a base vertex $w_0$, `HasTypeExchanger` asserts the existence of some $g \in G$ outside the subgroup `typePreserving G 𝒯 w₀` of elements preserving the parity $\mathrm{dist}(w_0, w) \bmod 2$ of every vertex; `mumfordFieldPlus` is the field of invariants of that type-preserving subgroup, which contains `mumfordField`, and `exchangerAct` is the residual action of $G$ on it, trivial on type-preserving elements.
--
--   **Relation to Mathlib.** `invariantIntermediateField` is Mathlib's `FixedPoints.intermediateField` under a project name, and the extension of the action to the fraction field is built from Mathlib's `IsFractionRing.ringEquivOfRingEquiv`; the group of semilinear automorphisms used as the target of the coefficientwise action is the project's own [`AlgebraicCurve.SemilinearAut`](../def/AlgebraicCurve_BaseChangeGalois.html#L15), as is the structure `AmbientSemilinearAut`.
--
--   **Where it is used.** This is the generic algebraic layer of the Mumford/Čerednik–Drinfel'd quotient construction: the invariant field of a group acting on a ring of rigid-analytic functions plays the role of the function field of the quotient curve, the semilinear automorphisms supply the descent data and Galois action on it, and the type-preserving subgroup and its exchanger govern the bipartite structure of the associated tree quotient for Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordQuotient.lean

import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Ring.Action.Group
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

section Generic

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

def fracAct [IsDomain M] (g : G) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv (MulSemiringAction.toRingEquiv G M g)

theorem fracAct_algebraMap [IsDomain M] (g : G) (m : M) :
    fracAct G M g (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (g • m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m

theorem fracAct_one [IsDomain M] : fracAct G M 1 = RingEquiv.refl _ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [fracAct_algebraMap, one_smul]; rfl

theorem fracAct_mul [IsDomain M] (g h : G) : fracAct G M (g * h) = (fracAct G M h).trans (fracAct G M g) := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.coe_trans]
  rw [fracAct_algebraMap, fracAct_algebraMap, fracAct_algebraMap, mul_smul]

scoped instance fracMulSemiringAction [IsDomain M] : MulSemiringAction G (FractionRing M) where
  smul g x := fracAct G M g x
  one_smul x := by show fracAct G M 1 x = x; rw [fracAct_one]; rfl
  mul_smul g h x := by show fracAct G M (g * h) x = fracAct G M g (fracAct G M h x); rw [fracAct_mul]; rfl
  smul_zero g := map_zero (fracAct G M g)
  smul_add g x y := map_add (fracAct G M g) x y
  smul_one g := map_one (fracAct G M g)
  smul_mul g x y := map_mul (fracAct G M g) x y

theorem frac_smul_def [IsDomain M] (g : G) (x : FractionRing M) : g • x = fracAct G M g x := rfl

theorem frac_smul_algebraMap [IsDomain M] (g : G) (m : M) :
    g • algebraMap M (FractionRing M) m = algebraMap M (FractionRing M) (g • m) :=
  fracAct_algebraMap G M g m

theorem smul_algebraMap_const_M (g : G) (c : K) : g • algebraMap K M c = algebraMap K M c := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem smul_algebraMap_const [IsDomain M] (g : G) (c : K) :
    g • algebraMap K (FractionRing M) c = algebraMap K (FractionRing M) c := by
  rw [IsScalarTower.algebraMap_apply K M (FractionRing M), frac_smul_algebraMap, smul_algebraMap_const_M]

scoped instance fracSMulCommClass [IsDomain M] : SMulCommClass G K (FractionRing M) :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_const]⟩

def invariantIntermediateField [IsDomain M] : IntermediateField K (FractionRing M) :=
  FixedPoints.intermediateField G

def invariantField [IsDomain M] : Subfield (FractionRing M) := (invariantIntermediateField K G M).toSubfield

theorem mem_invariantField_iff [IsDomain M] (x : FractionRing M) :
    x ∈ invariantField K G M ↔ ∀ g : G, g • x = x := Iff.rfl

theorem mem_invariantIntermediateField_iff [IsDomain M] (x : FractionRing M) :
    x ∈ invariantIntermediateField K G M ↔ ∀ g : G, g • x = x := Iff.rfl

theorem invariantField_eq_fixedPoints [IsDomain M] :
    invariantField K G M = FixedPoints.subfield G (FractionRing M) := rfl

theorem coe_invariantIntermediateField [IsDomain M] :
    (invariantIntermediateField K G M : Set (FractionRing M)) = invariantField K G M := rfl

instance invariantFieldAlgebra [IsDomain M] : Algebra K ↥(invariantField K G M) :=
  (invariantIntermediateField K G M).algebra

def invariantIntermediateFieldOf [IsDomain M] (Γ : Subgroup G) : IntermediateField K (FractionRing M) where
  carrier := {x | ∀ γ : G, γ ∈ Γ → γ • x = x}
  mul_mem' {x y} hx hy := fun γ hγ => by rw [smul_mul', hx γ hγ, hy γ hγ]
  one_mem' := fun γ _ => smul_one γ
  add_mem' {x y} hx hy := fun γ hγ => by rw [smul_add, hx γ hγ, hy γ hγ]
  zero_mem' := fun γ _ => smul_zero γ
  algebraMap_mem' c := fun γ _ => smul_algebraMap_const K G M γ c
  inv_mem' x hx := fun γ hγ => by rw [smul_inv'', hx γ hγ]

def invariantFieldOf [IsDomain M] (Γ : Subgroup G) : Subfield (FractionRing M) :=
  (invariantIntermediateFieldOf K G M Γ).toSubfield

theorem mem_invariantFieldOf_iff [IsDomain M] (Γ : Subgroup G) (x : FractionRing M) :
    x ∈ invariantFieldOf K G M Γ ↔ ∀ γ : G, γ ∈ Γ → γ • x = x := Iff.rfl

instance invariantFieldOfAlgebra [IsDomain M] (Γ : Subgroup G) : Algebra K ↥(invariantFieldOf K G M Γ) :=
  (invariantIntermediateFieldOf K G M Γ).algebra

theorem algebraMap_invariantFieldOf_coe [IsDomain M] (Γ : Subgroup G) (c : K) :
    ((algebraMap K ↥(invariantFieldOf K G M Γ) c : ↥(invariantFieldOf K G M Γ)) : FractionRing M) =
      algebraMap K (FractionRing M) c := rfl

theorem invariantFieldOf_top [IsDomain M] : invariantFieldOf K G M ⊤ = invariantField K G M :=
  Subfield.ext fun _ => ⟨fun h g => h g trivial, fun h g _ => h g⟩

theorem algebraMap_invariantField_coe [IsDomain M] (c : K) :
    ((algebraMap K ↥(invariantField K G M) c : ↥(invariantField K G M)) : FractionRing M) =
      algebraMap K (FractionRing M) c := rfl

theorem invariantFieldOf_mono_of_le [IsDomain M] {Γ Γ' : Subgroup G} (h : Γ' ≤ Γ) :
    invariantFieldOf K G M Γ ≤ invariantFieldOf K G M Γ' := fun _ hx γ hγ => hx γ (h hγ)

theorem invariantField_le_invariantFieldOf [IsDomain M] (Γ : Subgroup G) :
    invariantField K G M ≤ invariantFieldOf K G M Γ := fun _ hx γ _ => hx γ

def residualActRingEquiv [IsDomain M] (N : Subgroup G) [hN : N.Normal] (g : G) :
    ↥(invariantFieldOf K G M N) ≃+* ↥(invariantFieldOf K G M N) where
  toFun x := ⟨g • (x : FractionRing M), fun n hn => by
    rw [← mul_smul, show n * g = g * (g⁻¹ * n * g) from by group, mul_smul]
    congr 1
    exact x.2 (g⁻¹ * n * g) (by simpa using hN.conj_mem n hn g⁻¹)⟩
  invFun x := ⟨g⁻¹ • (x : FractionRing M), fun n hn => by
    rw [← mul_smul, show n * g⁻¹ = g⁻¹ * (g * n * g⁻¹) from by group, mul_smul]
    congr 1
    exact x.2 (g * n * g⁻¹) (hN.conj_mem n hn g)⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv x := Subtype.ext (smul_inv_smul g (x : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

theorem coe_residualActRingEquiv [IsDomain M] (N : Subgroup G) [N.Normal] (g : G) (x : ↥(invariantFieldOf K G M N)) :
    ((residualActRingEquiv K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • (x : FractionRing M) := rfl

def residualAct [IsDomain M] (N : Subgroup G) [N.Normal] :
    G →* (↥(invariantFieldOf K G M N) ≃ₐ[K] ↥(invariantFieldOf K G M N)) where
  toFun g := AlgEquiv.ofRingEquiv (f := residualActRingEquiv K G M N g) (fun c => Subtype.ext (by
    rw [coe_residualActRingEquiv]
    exact smul_algebraMap_const K G M g c))
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' g h := AlgEquiv.ext fun x => Subtype.ext (mul_smul g h (x : FractionRing M))

theorem coe_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (g : G) (x : ↥(invariantFieldOf K G M N)) :
    ((residualAct K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) = g • (x : FractionRing M) := rfl

theorem residualAct_eq_one_of_mem [IsDomain M] (N : Subgroup G) [N.Normal] {g : G} (hg : g ∈ N) :
    residualAct K G M N g = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 g hg)

theorem mem_invariantField_iff_forall_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (x : ↥(invariantFieldOf K G M N)) :
    (x : FractionRing M) ∈ invariantField K G M ↔ ∀ g : G, residualAct K G M N g x = x :=
  ⟨fun h g => Subtype.ext (h g), fun h g => congrArg Subtype.val (h g)⟩

structure AmbientSemilinearAut where

  base : K ≃+* K

  map : M ≃+* M
  map_algebraMap : ∀ c : K, map (algebraMap K M c) = algebraMap K M (base c)
  map_smul : ∀ (g : G) (m : M), map (g • m) = g • map m

namespace AmbientSemilinearAut

variable {K G M}

section Transport

omit [SMulCommClass G K M]

def fracMap [IsDomain M] (s : AmbientSemilinearAut K G M) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv s.map

theorem fracMap_algebraMap [IsDomain M] (s : AmbientSemilinearAut K G M) (m : M) :
    s.fracMap (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (s.map m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m

theorem fracMap_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G) (x : FractionRing M) :
    s.fracMap (g • x) = g • s.fracMap x := by
  have h : (s.fracMap.toRingHom.comp (fracAct G M g).toRingHom) =
      ((fracAct G M g).toRingHom.comp s.fracMap.toRingHom) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracAct_algebraMap, fracMap_algebraMap, fracMap_algebraMap, fracAct_algebraMap, s.map_smul]
  exact congrArg (fun φ : FractionRing M →+* FractionRing M => φ x) h

theorem fracMap_algebraMap_const [IsDomain M] (s : AmbientSemilinearAut K G M) (c : K) :
    s.fracMap (algebraMap K (FractionRing M) c) = algebraMap K (FractionRing M) (s.base c) := by
  rw [IsScalarTower.algebraMap_apply K M (FractionRing M), fracMap_algebraMap, s.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

@[ext] theorem ext {s t : AmbientSemilinearAut K G M} (hb : s.base = t.base) (hm : s.map = t.map) : s = t := by
  cases s; cases t; congr

instance instGroup : Group (AmbientSemilinearAut K G M) where
  mul s t :=
    { base := t.base.trans s.base
      map := t.map.trans s.map
      map_algebraMap := fun c => by
        rw [RingEquiv.coe_trans, Function.comp_apply, t.map_algebraMap, s.map_algebraMap]; rfl
      map_smul := fun g m => by
        rw [RingEquiv.coe_trans, Function.comp_apply, t.map_smul, s.map_smul]; rfl }
  one :=
    { base := RingEquiv.refl K
      map := RingEquiv.refl M
      map_algebraMap := fun _ => rfl
      map_smul := fun _ _ => rfl }
  inv s :=
    { base := s.base.symm
      map := s.map.symm
      map_algebraMap := fun c => by
        apply s.map.injective
        rw [RingEquiv.apply_symm_apply, s.map_algebraMap, RingEquiv.apply_symm_apply]
      map_smul := fun g m => by
        apply s.map.injective
        rw [RingEquiv.apply_symm_apply, s.map_smul, RingEquiv.apply_symm_apply] }
  mul_assoc s t u := ext rfl rfl
  one_mul s := ext (RingEquiv.ext fun _ => rfl) (RingEquiv.ext fun _ => rfl)
  mul_one s := ext (RingEquiv.ext fun _ => rfl) (RingEquiv.ext fun _ => rfl)
  inv_mul_cancel s := ext (RingEquiv.ext fun x => s.base.symm_apply_apply x) (RingEquiv.ext fun x => s.map.symm_apply_apply x)

@[simp] theorem base_mul (s t : AmbientSemilinearAut K G M) : (s * t).base = t.base.trans s.base := rfl
@[simp] theorem map_mul_eq (s t : AmbientSemilinearAut K G M) : (s * t).map = t.map.trans s.map := rfl
@[simp] theorem base_one : (1 : AmbientSemilinearAut K G M).base = RingEquiv.refl K := rfl
@[simp] theorem map_one_eq : (1 : AmbientSemilinearAut K G M).map = RingEquiv.refl M := rfl

theorem fracMap_one [IsDomain M] : (1 : AmbientSemilinearAut K G M).fracMap = RingEquiv.refl _ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [fracMap_algebraMap]; rfl

theorem fracMap_mul [IsDomain M] (s t : AmbientSemilinearAut K G M) :
    (s * t).fracMap = t.fracMap.trans s.fracMap := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.coe_trans]
  rw [fracMap_algebraMap, fracMap_algebraMap, fracMap_algebraMap]; rfl

end Transport

section Coeff

def invMap [IsDomain M] (s : AmbientSemilinearAut K G M) : ↥(invariantField K G M) ≃+* ↥(invariantField K G M) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g => by rw [← fracMap_smul, x.2 g]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

def coeffAct [IsDomain M] (s : AmbientSemilinearAut K G M) : AlgebraicCurve.SemilinearAut K ↥(invariantField K G M) :=
  ⟨(s.invMap, s.base), fun c => Subtype.ext (by
    show s.fracMap (algebraMap K (FractionRing M) c) = ((algebraMap K ↥(invariantField K G M) (s.base c) : _) : FractionRing M)
    rw [fracMap_algebraMap_const]; rfl)⟩

theorem coeffAct_baseAut [IsDomain M] (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffAct s) = s.base := rfl

theorem coe_coeffAct_toRingAut [IsDomain M] (s : AmbientSemilinearAut K G M) (x : ↥(invariantField K G M)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x : ↥(invariantField K G M)) : FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

def coeffActHom [IsDomain M] : AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K ↥(invariantField K G M) where
  toFun := coeffAct
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (1 : AmbientSemilinearAut K G M).fracMap (x : FractionRing M) = x
    rw [fracMap_one]; rfl)) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (s * t).fracMap (x : FractionRing M) = s.fracMap (t.fracMap (x : FractionRing M))
    rw [fracMap_mul]; rfl)) rfl)

@[simp] theorem coeffActHom_apply [IsDomain M] (s : AmbientSemilinearAut K G M) : coeffActHom s = coeffAct s := rfl

theorem coeffAct_comm_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G) (x : ↥(invariantField K G M)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x : ↥(invariantField K G M)) : FractionRing M) =
      s.fracMap (x : FractionRing M) ∧
    s.fracMap (g • (x : FractionRing M)) = g • s.fracMap (x : FractionRing M) :=
  ⟨rfl, fracMap_smul s g x⟩

theorem fracMap_comm_residualAct [IsDomain M] (s : AmbientSemilinearAut K G M) (N : Subgroup G) [N.Normal] (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    s.fracMap ((residualAct K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • s.fracMap (x : FractionRing M) := by
  rw [coe_residualAct, fracMap_smul]

def invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    ↥(invariantFieldOf K G M Γ) ≃+* ↥(invariantFieldOf K G M Γ) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g hg => by rw [← fracMap_smul, x.2 g hg]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g hg => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g hg]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

theorem coe_invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) (x : ↥(invariantFieldOf K G M Γ)) :
    ((invMapOf Γ s x : ↥(invariantFieldOf K G M Γ)) : FractionRing M) = s.fracMap (x : FractionRing M) := rfl

def coeffActOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut K ↥(invariantFieldOf K G M Γ) :=
  ⟨(invMapOf Γ s, s.base), fun c => Subtype.ext (by
    show s.fracMap (algebraMap K (FractionRing M) c) =
      ((algebraMap K ↥(invariantFieldOf K G M Γ) (s.base c) : _) : FractionRing M)
    rw [fracMap_algebraMap_const]; rfl)⟩

theorem coeffActOf_baseAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffActOf Γ s) = s.base := rfl

theorem coe_coeffActOf_toRingAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M)
    (x : ↥(invariantFieldOf K G M Γ)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf Γ s) x : ↥(invariantFieldOf K G M Γ)) : FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

def coeffActOfHom [IsDomain M] (Γ : Subgroup G) :
    AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K ↥(invariantFieldOf K G M Γ) where
  toFun := coeffActOf Γ
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (1 : AmbientSemilinearAut K G M).fracMap (x : FractionRing M) = x
    rw [fracMap_one]; rfl)) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (s * t).fracMap (x : FractionRing M) = s.fracMap (t.fracMap (x : FractionRing M))
    rw [fracMap_mul]; rfl)) rfl)

@[simp] theorem coeffActOfHom_apply [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    coeffActOfHom Γ s = coeffActOf Γ s := rfl

theorem coeffActOf_comm_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (s : AmbientSemilinearAut K G M) (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) (residualAct K G M N g x) =
      residualAct K G M N g (AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) x) :=
  Subtype.ext (by
    rw [coe_coeffActOf_toRingAut, coe_residualAct, coe_residualAct, coe_coeffActOf_toRingAut, fracMap_smul])

end Coeff

end AmbientSemilinearAut

end Generic

section MumfordLayer

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [IsDomain M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

abbrev mumfordField : Subfield (FractionRing M) := invariantField K G M

variable {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W)

def HasTypeExchanger : Prop := ∃ g : G, g ∉ typePreserving G 𝒯 w₀

abbrev mumfordFieldPlus : Subfield (FractionRing M) := invariantFieldOf K G M (typePreserving G 𝒯 w₀)

theorem mumfordField_le_mumfordFieldPlus : mumfordField K G M ≤ mumfordFieldPlus K G M 𝒯 w₀ :=
  invariantField_le_invariantFieldOf K G M _

abbrev exchangerAct [(typePreserving G 𝒯 w₀).Normal] :
    G →* (↥(mumfordFieldPlus K G M 𝒯 w₀) ≃ₐ[K] ↥(mumfordFieldPlus K G M 𝒯 w₀)) :=
  residualAct K G M (typePreserving G 𝒯 w₀)

theorem exchangerAct_eq_one_of_mem [(typePreserving G 𝒯 w₀).Normal] {g : G} (hg : g ∈ typePreserving G 𝒯 w₀) :
    exchangerAct K G M 𝒯 w₀ g = 1 :=
  residualAct_eq_one_of_mem K G M _ hg

end MumfordLayer

end CerednikDrinfeld.Mumford

end


