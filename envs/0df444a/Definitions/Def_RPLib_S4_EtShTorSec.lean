-- Prove2me | Definitions.Def_RPLib_S4_EtShTorSec
-- name    : RPLib_S4_EtShTorSec
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:34:38.768721+00:00
-- url     : https://prove2.me/theorems/71668446-fb72-4457-87d4-2fafb636ae6a
-- title:
--   Sections of an etale sheaf over $T \times_X Y$ for a Galois cover
-- statement:
--   Let $Y = \mathrm{Spec}\,B \to X = \mathrm{Spec}\,A$ be a Galois cover with group $G$ (a finite group acting on $B$ with $A = B^G$ and trivial inertia) and $T$ etale over $Y$. The maps $T \to T \times_X Y$, $t \mapsto (t, \sigma_Y t)$ for $\sigma \in G$ cover $T \times_X Y$ by pairwise disjoint sections, so for every etale sheaf $F$ on $X$ restriction is a bijection $$F(T \times_X Y) \cong \prod_{\sigma \in G} F(T),$$ natural in $T$. The file also proves gluing for sheaves of modules along covering families, that two $A$-algebra maps $B \to K$ to a field differ by a unique element of $G$, and surjectivity of the projection.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V; S. U. Chase, D. K. Harrison, A. Rosenberg, Galois theory and Galois cohomology of commutative rings, Mem. Amer. Math. Soc. 52 (1965), Theorem 1.3; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5

import Mathlib
import Definitions.Def_RPLib_S4_EtShClosed
import Definitions.Def_RPLib_S4_EtShGalEt

/-!
# S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover

For a Galois cover `C : GalCover A`, `π : Y = Spec B → X = Spec A` and `T` etale over `Y`, the maps
`ι σ : T → T ×_X Y`, `t ↦ (t, σ_Y t)` (`σ ∈ G`, `σ_Y = Spec σ`) cover `T ×_X Y` by pairwise disjoint sections, so for
every etale sheaf `F` on `X`, restriction is a bijection `F(T ×_X Y) ≅ Π_G F(T)` (`secEquiv`).

* `existsUnique_glue`: gluing for sheaves of modules along a covering family of arrows.
* `exists_eq_comp`: two maps `B → K` to a field that agree on `A` differ by some `σ ∈ G` (from `B ⊗_A B ≅ Π_G B`).
* `eq_of_comp_eq`: `φ ∘ σ = φ ∘ τ` for `φ : B → K` forces `σ = τ` (trivial inertia).
* `sec_cover`, `isEmpty_of_sec`, `existsUnique_sec`, `secEquiv`, `sec_naturality`, `pr_surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section Glue

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

/-- The element `m` as a map `Λ ⟶ M`. -/
abbrev elt {M : ModuleCat.{u} Λ} (m : M) : ModuleCat.of Λ Λ ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M m)

theorem elt_one {M : ModuleCat.{u} Λ} (m : M) : (elt m).hom 1 = m := by
  simp [elt]

theorem elt_comp {M N : ModuleCat.{u} Λ} (m : M) (f : M ⟶ N) : elt m ≫ f = elt (f.hom m) := by
  ext
  simp [elt]

/-- **Gluing** for sheaves of modules on the small etale site along a covering family of arrows. -/
theorem existsUnique_glue (F : EtSh Λ Z) {U : Z.Etale} {I : Type*} {V : I → Z.Etale} (f : ∀ i, V i ⟶ U)
    (hR : Sieve.ofArrows V f ∈ Z.smallEtaleTopology U) (x : ∀ i, F.obj.obj (op (V i)))
    (hx : ∀ i j (W : Z.Etale) (gi : W ⟶ V i) (gj : W ⟶ V j), gi ≫ f i = gj ≫ f j →
      (F.obj.map gi.op).hom (x i) = (F.obj.map gj.op).hom (x j)) :
    ∃! s, ∀ i, (F.obj.map (f i).op).hom s = x i := by
  have h := (Presieve.isSheafFor_arrows_iff (P := F.obj ⋙ coyoneda.obj (op (ModuleCat.of Λ Λ))) f).1
    ((Presieve.isSheafFor_iff_generate _).2 (F.cond (ModuleCat.of Λ Λ) _ hR))
  obtain ⟨t, ht, hu⟩ := h (fun i => elt (x i)) (fun i j W gi gj e => by
    change elt (x i) ≫ F.obj.map gi.op = elt (x j) ≫ F.obj.map gj.op
    rw [elt_comp, elt_comp, hx i j W gi gj e])
  let t' : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) := t
  refine ⟨t'.hom 1, fun i => ?_, fun s hs => ?_⟩
  · have h1 : t' ≫ F.obj.map (f i).op = elt (x i) := ht i
    have h2 := congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op (V i)) => φ.hom 1) h1
    simpa [elt] using h2
  · have e : elt s = t := hu _ fun i => by
      change elt s ≫ F.obj.map (f i).op = elt (x i)
      rw [elt_comp, hs i]
    change s = t'.hom 1
    rw [← elt_one s]
    exact congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) => φ.hom 1) e

end Glue

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- `σ` as a ring endomorphism of `B`. -/
abbrev rh (σ : C.G) : C.B →+* C.B := MulSemiringAction.toRingHom C.G C.B σ

/-- **Points of `Y` over one point of `X` differ by `G`** (ring form, from `B ⊗_A B ≅ Π_G B`). -/
theorem exists_eq_comp {K : Type} [Field K] (γ β : C.B →+* K)
    (h : γ.comp (algebraMap A C.B) = β.comp (algebraMap A C.B)) : ∃ σ : C.G, β = γ.comp (rh C σ) := by
  classical
  have := Fintype.ofFinite C.G
  letI : Algebra A K := (γ.comp (algebraMap A C.B)).toAlgebra
  let γ' : C.B →ₐ[A] K := { γ with commutes' := fun _ => rfl }
  let β' : C.B →ₐ[A] K := { β with commutes' := fun a => (RingHom.congr_fun h a).symm }
  let ψ : (C.G → C.B) →ₐ[A] K :=
    (Algebra.TensorProduct.lift γ' β' fun _ _ => Commute.all _ _).comp C.torsorEquiv.symm.toAlgHom
  have hψ : ∀ b b' : C.B, ψ (fun σ => b * σ • b') = γ b * β b' := by
    intro b b'
    have e : (fun σ => b * σ • b') = C.torsorEquiv (b ⊗ₜ[A] b') :=
      funext fun σ => (C.torsorEquiv_tmul b b' σ).symm
    rw [e]
    show (Algebra.TensorProduct.lift γ' β' (fun _ _ => Commute.all _ _)) (C.torsorEquiv.symm (C.torsorEquiv (b ⊗ₜ[A] b'))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul]
    rfl
  have hone : ∑ σ : C.G, (Pi.single σ (1 : C.B) : C.G → C.B) = 1 := by
    simpa using Finset.univ_sum_single (1 : C.G → C.B)
  have hsum : ∑ σ : C.G, ψ (Pi.single σ 1) = 1 := by
    rw [← map_sum, hone, map_one]
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun σ => ψ (Pi.single σ 1)) (by rw [hsum]; exact one_ne_zero)
  have he : ψ (Pi.single σ 1) = 1 := by
    have h2 : ψ (Pi.single σ 1) * ψ (Pi.single σ 1) = ψ (Pi.single σ 1) * 1 := by
      rw [← map_mul, ← Pi.single_mul, mul_one, mul_one]
    exact mul_left_cancel₀ hσ h2
  have hloc : ∀ x x' : C.G → C.B, x σ = x' σ → ψ x = ψ x' := by
    intro x x' hxx
    have hx : ∀ y : C.G → C.B, ψ y = ψ (y * Pi.single σ 1) := fun y => by rw [map_mul, he, mul_one]
    rw [hx x, hx x']
    congr 1
    funext τ
    by_cases hτ : τ = σ
    · subst hτ
      simp [hxx]
    · simp [hτ]
  refine ⟨σ, RingHom.ext fun b' => ?_⟩
  have h1 := hψ 1 b'
  have h2 := hψ (σ • b') 1
  rw [map_one, one_mul] at h1
  rw [map_one, mul_one] at h2
  show β b' = γ (σ • b')
  rw [← h1, ← h2]
  exact hloc _ _ (by simp)

/-- **Disjointness** (trivial inertia): `φ ∘ σ = φ ∘ τ` for a map `φ : B → K` to a field forces `σ = τ`. -/
theorem eq_of_comp_eq {K : Type} [Field K] (φ : C.B →+* K) {σ τ : C.G}
    (h : φ.comp (rh C σ) = φ.comp (rh C τ)) : σ = τ := by
  have hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmem : σ * τ⁻¹ ∈ (RingHom.ker φ).inertia C.G := fun x => by
    show (σ * τ⁻¹) • x - x ∈ RingHom.ker φ
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, mul_smul]
    have := RingHom.congr_fun h (τ⁻¹ • x)
    simpa [smul_inv_smul] using this
  rw [C.inertia_eq_bot (RingHom.ker φ), Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

/-- `X = Spec A`. -/
abbrev SX (A : Type) [CommRing A] : Scheme := Spec (CommRingCat.of A)

/-- `Y = Spec B`. -/
abbrev SY : Scheme := Spec (CommRingCat.of C.B)

/-- The cover `π : Y → X`. -/
abbrev pr : SY C ⟶ SX A := Spec.map (CommRingCat.ofHom (algebraMap A C.B))

instance : Etale (pr C) := C.etale_spec

/-- `σ_Y = Spec σ : Y → Y`. -/
def act (σ : C.G) : SY C ⟶ SY C := Spec.map (CommRingCat.ofHom (rh C σ))

@[reassoc (attr := simp)]
theorem act_pr (σ : C.G) : act C σ ≫ pr C = pr C := by
  rw [act, ← Spec.map_comp]
  congr 1
  ext a
  exact smul_algebraMap σ a

theorem act_mul (σ τ : C.G) : act C σ ≫ act C τ = act C (σ * τ) := by
  rw [act, act, act, ← Spec.map_comp]
  congr 1
  ext b
  simp [mul_smul]

theorem act_one : act C 1 = 𝟙 _ := by
  rw [act, ← Spec.map_id]
  congr 1
  ext b
  simp

/-- `π` is surjective (lying over). -/
theorem pr_surjective : Function.Surjective (pr C) := by
  intro x
  let x' : PrimeSpectrum A := x
  have := x'.isPrime
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C.B) x'.asIdeal ⊥
    (Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective A C.B))
  exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum C.B), PrimeSpectrum.ext hQx⟩

variable {C}

/-- `T` as an etale `X`-scheme. -/
abbrev tx (T : (SY C).Etale) : (SX A).Etale := (etComp (pr C)).obj T

/-- `T ×_X Y` as an etale `X`-scheme. -/
abbrev tp (T : (SY C).Etale) : (SX A).Etale := (etComp (pr C)).obj ((etPull (pr C)).obj (tx T))

/-- `T ×_X Y` as a scheme. -/
abbrev tpL (T : (SY C).Etale) : Scheme := pullback (T.hom ≫ pr C) (pr C)

/-- The section `ι σ : T → T ×_X Y`, `t ↦ (t, σ_Y t)`, on schemes. -/
def secL (T : (SY C).Etale) (σ : C.G) : T.left ⟶ tpL T :=
  pullback.lift (𝟙 T.left) (T.hom ≫ act C σ) (by simp)

@[reassoc (attr := simp)]
theorem secL_fst (T : (SY C).Etale) (σ : C.G) :
    secL T σ ≫ pullback.fst (T.hom ≫ pr C) (pr C) = 𝟙 T.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem secL_snd (T : (SY C).Etale) (σ : C.G) :
    secL T σ ≫ pullback.snd (T.hom ≫ pr C) (pr C) = T.hom ≫ act C σ :=
  pullback.lift_snd _ _ _

/-- The section `ι σ` as a morphism of etale `X`-schemes. -/
def sec (T : (SY C).Etale) (σ : C.G) : tx T ⟶ tp T :=
  MorphismProperty.Over.homMk (secL T σ) (by
    show secL T σ ≫ pullback.snd (T.hom ≫ pr C) (pr C) ≫ pr C = T.hom ≫ pr C
    rw [secL_snd_assoc, act_pr]) trivial

theorem sec_left (T : (SY C).Etale) (σ : C.G) : (sec T σ).left = secL T σ := rfl

/-- Every point of `T ×_X Y` lies on some section `ι σ`. -/
theorem exists_secL_apply (T : (SY C).Etale) (p : tpL T) :
    ∃ (σ : C.G) (q : T.left), secL T σ q = p := by
  let P := tpL T
  let fp := P.fromSpecResidueField p
  let a : Spec (P.residueField p) ⟶ T.left := fp ≫ pullback.fst (T.hom ≫ pr C) (pr C)
  let b : Spec (P.residueField p) ⟶ SY C := fp ≫ pullback.snd (T.hom ≫ pr C) (pr C)
  have hab : (a ≫ T.hom) ≫ pr C = b ≫ pr C := by
    simp only [a, b, Category.assoc]
    rw [pullback.condition]
  obtain ⟨σ, hσ⟩ := exists_eq_comp C (Spec.preimage (a ≫ T.hom)).hom (Spec.preimage b).hom (by
    rw [← Spec.map_preimage (a ≫ T.hom), ← Spec.map_preimage b] at hab
    dsimp only [pr] at hab
    rw [← Spec.map_comp, ← Spec.map_comp] at hab
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective hab))
  have hb : b = (a ≫ T.hom) ≫ act C σ := by
    rw [← Spec.map_preimage b, ← Spec.map_preimage (a ≫ T.hom), act, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (by rw [hσ]; rfl)
  have hfp : fp = a ≫ secL T σ := by
    refine pullback.hom_ext (f := T.hom ≫ pr C) (g := pr C) ?_ ?_
    · rw [Category.assoc, secL_fst, Category.comp_id]
    · rw [Category.assoc, secL_snd, ← Category.assoc, ← hb]
  refine ⟨σ, a (IsLocalRing.closedPoint (P.residueField p)), ?_⟩
  have := P.fromSpecResidueField_apply p (IsLocalRing.closedPoint (P.residueField p))
  rw [show P.fromSpecResidueField p = fp from rfl, hfp] at this
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans this

/-- The sections `ι σ` cover `T ×_X Y`. -/
theorem sec_cover (T : (SY C).Etale) :
    Sieve.ofArrows (fun _ : C.G => tx T) (sec T) ∈ (SX A).smallEtaleTopology (tp T) := by
  rw [mem_smallEtale_iff]
  intro p
  obtain ⟨σ, q, hq⟩ := exists_secL_apply T p
  exact ⟨tx T, sec T σ, q, Sieve.ofArrows_mk _ _ σ, hq⟩

theorem sec_left_eq {T : (SY C).Etale} {W : (SX A).Etale} {σ τ : C.G} (gi gj : W ⟶ tx T)
    (h : gi ≫ sec T σ = gj ≫ sec T τ) : gi = gj := by
  let gl : W.left ⟶ T.left := gi.left
  let gl' : W.left ⟶ T.left := gj.left
  have h0 : gl ≫ secL T σ = gl' ≫ secL T τ := congrArg (fun φ : W ⟶ tp T => φ.left) h
  have h1 := congrArg (· ≫ pullback.fst (T.hom ≫ pr C) (pr C)) h0
  simp only [Category.assoc, secL_fst, Category.comp_id] at h1
  exact MorphismProperty.Over.Hom.ext h1

/-- **The sections are disjoint**: two of them agree only over the empty scheme. -/
theorem isEmpty_of_sec {T : (SY C).Etale} {W : (SX A).Etale} {σ τ : C.G} (hστ : σ ≠ τ) (g : W ⟶ tx T)
    (h : g ≫ sec T σ = g ≫ sec T τ) : IsEmpty W.left := by
  let gl : W.left ⟶ T.left := g.left
  have h0 : gl ≫ secL T σ = gl ≫ secL T τ := congrArg (fun φ : W ⟶ tp T => φ.left) h
  have h2 := congrArg (· ≫ pullback.snd (T.hom ≫ pr C) (pr C)) h0
  simp only [Category.assoc, secL_snd] at h2
  refine ⟨fun z => hστ ?_⟩
  let k := W.left.fromSpecResidueField z ≫ gl ≫ T.hom
  have hk : k ≫ act C σ = k ≫ act C τ := by
    simp only [k, Category.assoc, h2]
  apply eq_of_comp_eq C (Spec.preimage k).hom
  rw [← Spec.map_preimage k, act, act, ← Spec.map_comp, ← Spec.map_comp] at hk
  simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective hk)

variable (Λ : Type) [CommRing Λ]

/-- **Sections over `T ×_X Y`**: every family over the sections `ι σ` glues uniquely. -/
theorem existsUnique_sec (F : EtSh Λ (SX A)) (T : (SY C).Etale) (x : C.G → F.obj.obj (op (tx T))) :
    ∃! s, ∀ σ, (F.obj.map (sec T σ).op).hom s = x σ := by
  classical
  refine existsUnique_glue F (sec T) (sec_cover T) x fun i j W gi gj e => ?_
  have hg := sec_left_eq gi gj e
  subst hg
  by_cases hij : i = j
  · subst hij
    rfl
  · have hz := isZero_obj_of_isEmpty Λ F W (isEmpty_of_sec hij gi e)
    exact (ModuleCat.subsingleton_of_isZero hz).elim _ _

/-- Restriction to the sections `ι σ`. -/
def secMap (F : EtSh Λ (SX A)) (T : (SY C).Etale) :
    F.obj.obj (op (tp T)) →ₗ[Λ] (C.G → F.obj.obj (op (tx T))) :=
  LinearMap.pi fun σ => (F.obj.map (sec T σ).op).hom

theorem secMap_bijective (F : EtSh Λ (SX A)) (T : (SY C).Etale) : Function.Bijective (secMap Λ F T) := by
  refine ⟨fun s t hst => ?_, fun x => ?_⟩
  · obtain ⟨u, -, hu⟩ := existsUnique_sec Λ F T (secMap Λ F T s)
    exact (hu s fun σ => rfl).trans (hu t fun σ => (congrFun hst σ).symm).symm
  · obtain ⟨s, hs, -⟩ := existsUnique_sec Λ F T x
    exact ⟨s, funext hs⟩

/-- **`F(T ×_X Y) ≅ Π_G F(T)`** for every etale sheaf `F` on `X`. -/
def secEquiv (F : EtSh Λ (SX A)) (T : (SY C).Etale) :
    F.obj.obj (op (tp T)) ≃ₗ[Λ] (C.G → F.obj.obj (op (tx T))) :=
  LinearEquiv.ofBijective (secMap Λ F T) (secMap_bijective Λ F T)

@[simp] theorem secEquiv_apply (F : EtSh Λ (SX A)) (T : (SY C).Etale) (s : F.obj.obj (op (tp T))) (σ : C.G) :
    secEquiv Λ F T s σ = (F.obj.map (sec T σ).op).hom s := rfl

/-- The sections are natural in `T` (scheme form). -/
theorem secL_naturality {T' T : (SY C).Etale} (h : T' ⟶ T) (σ : C.G) :
    secL T' σ ≫ pullback.lift (pullback.fst (T'.hom ≫ pr C) (pr C) ≫ h.left) (pullback.snd _ _) (by
      rw [Category.assoc, ← Category.assoc h.left, MorphismProperty.Over.w h]
      exact pullback.condition) = h.left ≫ secL T σ := by
  refine pullback.hom_ext (f := T.hom ≫ pr C) (g := pr C) ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, secL_fst_assoc, Category.assoc, secL_fst,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, secL_snd, Category.assoc, secL_snd, ← Category.assoc,
      MorphismProperty.Over.w h]

/-- The sections are natural in `T`. -/
theorem sec_naturality {T' T : (SY C).Etale} (h : T' ⟶ T) (σ : C.G) :
    sec T' σ ≫ (etComp (pr C)).map ((etPull (pr C)).map ((etComp (pr C)).map h)) =
      (etComp (pr C)).map h ≫ sec T σ :=
  MorphismProperty.Over.Hom.ext (secL_naturality h σ)

end TorSec

end RamanujanPetersson.EtSheaves


