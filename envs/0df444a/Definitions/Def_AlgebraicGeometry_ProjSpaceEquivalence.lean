-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
-- name    : AlgebraicGeometry_ProjSpaceEquivalence
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:54.560757+00:00
-- url     : https://prove2.me/theorems/6b280486-b9ad-4efc-b3c9-6014af1ae380
-- title:
--   Scheme points of projective space as vectors modulo scaling
-- statement:
--   For a field $K$ and $N≥0$, the file defines the equivalence $$P^N(K)≃(K^{N+1}∖\{0\})/K^×,$$ expressed as an equivalence between scheme-theoretic $K$-points and projectivized nonzero coordinate vectors. The construction is compatible with the usual homogeneous ratios on every standard affine chart. This connects geometric morphisms to the coordinate classes used by height theory.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
set_option autoImplicit false
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

/-! ### Coordinates of chart points

The equivalence below needs that `kPointOfVec` is constant exactly on scaling classes and
reaches every point; these facts are proved here, from the chart description of
`kPointOfVec`, because the definition depends on them. -/

section

namespace AlgebraicGeometry

/-- The scheme point associated with a vector has the usual homogeneous
coordinate ratios on each standard affine chart. -/
private theorem ProjSpace.kPointOfVec_chart (K : Type) [Field K] (N : ℕ) (v : Fin (N + 1) → K) (hv : v ≠ 0)
    (i : Fin (N + 1)) (hi : v i ≠ 0) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K,
      (∀ j, φ (ProjSpace.ratio K N i j) = v j / v i) ∧
      (ProjSpace.kPointOfVec K N v hv).1 = Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
          (ProjSpace.X_mem_one K N i) one_pos := by
  exact ProjSpace.kPointOfVec_has_charts K N v hv i hi

end AlgebraicGeometry

namespace AlgebraicGeometry.ProjSpace

private theorem chart_map_scalars {K : Type} [Field K] {N : ℕ}
    (x : Scheme.KPoint (π K N)) (i : Fin (N + 1))
    (φ : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K)
    (hx : x.1 = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) (X_mem_one K N i) one_pos) :
    ∀ r : K, φ (algebraMap K _ r) = r := by
  have h := x.2
  rw [hx, Category.assoc, awayι_comp_π, ← Spec.map_comp, Spec.map_eq_id] at h
  intro r
  have hr := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom r) h
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] using hr

private theorem chart_ringHom_ext {K : Type} [Field K] {N : ℕ} (i : Fin (N + 1))
    (φ ψ : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K)
    (hφ : ∀ r : K, φ (algebraMap K _ r) = r)
    (hψ : ∀ r : K, ψ (algebraMap K _ r) = r)
    (hgen : ∀ j, φ (ratio K N i j) = ψ (ratio K N i j)) : φ = ψ := by
  ext a
  have ha : a ∈ Algebra.adjoin K (Set.range (ratio K N i)) := by
    rw [adjoin_range_ratio]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hgen j
  | algebraMap r => rw [hφ, hψ]
  | add a b ha hb h₁ h₂ => simp only [map_add, h₁, h₂]
  | mul a b ha hb h₁ h₂ => simp only [map_mul, h₁, h₂]

/-- A scheme point in a standard chart is the point of its homogeneous ratios. -/
private theorem kPointOfVec_eq_of_chart {K : Type} [Field K] {N : ℕ}
    (x : Scheme.KPoint (π K N)) (v : Fin (N + 1) → K) (hv : v ≠ 0)
    (i : Fin (N + 1)) (hi : v i ≠ 0)
    (φ : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K)
    (hφ : ∀ j, φ (ratio K N i j) = v j / v i)
    (hx : x.1 = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) (X_mem_one K N i) one_pos) :
    kPointOfVec K N v hv = x := by
  obtain ⟨ψ, hψ, hpoint⟩ := kPointOfVec_chart K N v hv i hi
  have heq : ψ = φ := chart_ringHom_ext i ψ φ
    (chart_map_scalars _ i ψ hpoint) (chart_map_scalars x i φ hx)
    (fun j => (hψ j).trans (hφ j).symm)
  apply Subtype.ext
  rw [hpoint, hx, heq]

end AlgebraicGeometry.ProjSpace

open CategoryTheory AlgebraicGeometry NeronModelInfra HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

/-- A homogeneous coordinate is nonzero precisely on its standard chart. -/
private theorem kPointOfVec_mem_basicOpen_iff (K : Type) [Field K] (N : ℕ)
    (v : Fin (N + 1) → K) (hv : v ≠ 0) (i : Fin (N + 1)) :
    (kPointOfVec K N v hv).1 (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) ↔ v i ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    exact not_ne_iff.mp (fun hj => h ⟨j, hj⟩)
  obtain ⟨φ, hφ, hpoint⟩ := kPointOfVec_chart K N v hv j hj
  have helem : Away.isLocalizationElem (X_mem_one K N j) (X_mem_one K N i) =
      ratio K N j i := by
    apply HomogeneousLocalization.val_injective
    simp [ratio, Away.val_mk]
  have hpre := Proj.awayι_preimage_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (X_mem_one K N j) one_pos (X_mem_one K N i) one_pos
  rw [helem] at hpre
  change IsLocalRing.closedPoint K ∈ (kPointOfVec K N v hv).1 ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i) ↔ v i ≠ 0
  rw [hpoint, Scheme.Hom.comp_preimage, hpre]
  change φ (ratio K N j i) ∉ IsLocalRing.maximalIdeal K ↔ v i ≠ 0
  simp [hφ, IsLocalRing.mem_maximalIdeal, hj]

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry

private theorem ProjSpace.kPointOfVec_eq_iff (K : Type) [Field K] (N : ℕ)
    (v w : Fin (N + 1) → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ProjSpace.kPointOfVec K N v hv = ProjSpace.kPointOfVec K N w hw ↔
      ∃ c : K, c ≠ 0 ∧ w = c • v := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
  constructor
  · intro h
    have hp := congrArg Subtype.val h
    have hmem := (ProjSpace.kPointOfVec_mem_basicOpen_iff K N v hv i).mpr hi
    rw [hp] at hmem
    have hwi := (ProjSpace.kPointOfVec_mem_basicOpen_iff K N w hw i).mp hmem
    obtain ⟨φ, hφ, hxv⟩ := ProjSpace.kPointOfVec_chart K N v hv i hi
    obtain ⟨ψ, hψ, hxw⟩ := ProjSpace.kPointOfVec_chart K N w hw i hwi
    have hmaps : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) := by
      apply (cancel_mono (Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) (ProjSpace.X_mem_one K N i) one_pos)).mp
      rw [← hxv, ← hxw, hp]
    have hφψ : φ = ψ := congrArg CommRingCat.Hom.hom (Spec.map_injective hmaps)
    have hratio : ∀ j, v j / v i = w j / w i := by
      intro j
      rw [← hφ j, ← hψ j, hφψ]
    refine ⟨w i / v i, div_ne_zero hwi hi, ?_⟩
    funext j
    change w j = (w i / v i) * v j
    apply mul_right_cancel₀ hi
    calc
      w j * v i = v j * w i := ((div_eq_div_iff hi hwi).mp (hratio j)).symm
      _ = (w i / v i * v j) * v i := by field_simp
  · rintro ⟨c, hc, hwv⟩
    have hwi : w i ≠ 0 := by
      rw [hwv]
      exact mul_ne_zero hc hi
    obtain ⟨φ, hφ, hx⟩ := ProjSpace.kPointOfVec_chart K N w hw i hwi
    apply ProjSpace.kPointOfVec_eq_of_chart (ProjSpace.kPointOfVec K N w hw) v hv i hi φ
    · intro j
      rw [hφ j, hwv]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [hc, hi]
    · exact hx

end AlgebraicGeometry

namespace AlgebraicGeometry

private theorem ProjSpace.kPointOfVec_surjective (K : Type) [Field K] (N : ℕ)
    (x : Scheme.KPoint (ProjSpace.π K N)) :
    ∃ (v : Fin (N + 1) → K) (hv : v ≠ 0), ProjSpace.kPointOfVec K N v hv = x := by
  classical
  let p : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hcover := Proj.iSup_basicOpen_eq_top
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun i : Fin (N + 1) => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X K N)
  have hp : x.1 p ∈ (⨆ i : Fin (N + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  let ι := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (MvPolynomial.X i) (ProjSpace.X_mem_one K N i) one_pos
  have hrange : Set.range x.1.base ⊆ Set.range ι.base := by
    rintro y ⟨q, rfl⟩
    have hq : q = p := Subsingleton.elim _ _
    subst q
    change x.1 p ∈ ι.opensRange
    rw [Proj.opensRange_awayι]
    exact hi
  let g := IsOpenImmersion.lift ι x.1 hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hx : x.1 = Spec.map φ ≫ ι := by
    rw [hφ]
    exact (IsOpenImmersion.lift_fac ι x.1 hrange).symm
  let v : Fin (N + 1) → K := fun j => φ.hom (ProjSpace.ratio K N i j)
  have hvi : v i = 1 := by simp [v, ProjSpace.ratio_self]
  have hv : v ≠ 0 := by
    intro h
    have : (0 : K) = 1 := by simp [h] at hvi
    exact zero_ne_one this
  refine ⟨v, hv, ProjSpace.kPointOfVec_eq_of_chart x v hv i ?_ φ.hom ?_ hx⟩
  · rw [hvi]
    exact one_ne_zero
  · intro j
    simp only [hvi, div_one]
    rfl

end AlgebraicGeometry

end

namespace AlgebraicGeometry.ProjSpace

/-- Scheme points of projective space are nonzero coordinate tuples modulo scaling. -/
noncomputable def kPointEquivProjectivization (K : Type) [Field K] (N : ℕ) :
    Scheme.KPoint (π K N) ≃ Projectivization K (Fin (N + 1) → K) := by
  let g : Projectivization K (Fin (N + 1) → K) → Scheme.KPoint (π K N) :=
    Projectivization.lift
      (fun v => kPointOfVec K N v.1 v.2)
      (by
        intro a b t hab
        have ht : t ≠ 0 := by
          intro ht
          apply a.2
          rw [hab, ht, zero_smul]
        exact ((kPointOfVec_eq_iff K N b.1 a.1 b.2 a.2).mpr ⟨t, ht, hab⟩).symm)
  refine (Equiv.ofBijective g ⟨?_, ?_⟩).symm
  · intro z w
    induction z using Projectivization.ind with
    | h v hv =>
        induction w using Projectivization.ind with
        | h w hw =>
            intro h
            change kPointOfVec K N v hv = kPointOfVec K N w hw at h
            obtain ⟨c, hc, hwv⟩ := (kPointOfVec_eq_iff K N v w hv hw).mp h
            exact ((Projectivization.mk_eq_mk_iff' K w v hw hv).mpr ⟨c, hwv.symm⟩).symm
  · intro x
    obtain ⟨v, hv, hx⟩ := kPointOfVec_surjective K N x
    exact ⟨Projectivization.mk K v hv, hx⟩

end AlgebraicGeometry.ProjSpace


