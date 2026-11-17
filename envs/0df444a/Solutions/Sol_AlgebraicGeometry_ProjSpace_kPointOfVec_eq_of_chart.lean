-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointOfVec_eq_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:49.674829+00:00
-- url     : https://prove2.me/submissions/59549465-b0a2-4076-8180-2ced35109a5d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_chart
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

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
theorem _root_.solution {K : Type} [Field K] {N : ℕ}
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
