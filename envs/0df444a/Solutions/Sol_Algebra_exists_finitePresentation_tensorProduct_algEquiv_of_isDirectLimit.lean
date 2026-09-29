-- Prove2me | solution 1 for Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b4a52626-48ba-5bcf-a4dc-bbc40e4c80cb

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit

set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

namespace AlgSpreadDirected

theorem range_mono {ι : Type u} [Preorder ι]
    {G : ι → Type v} [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    {R : Type w} [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    {i j : ι} (hij : i ≤ j) :
    Set.range (algebraMap (G i) R) ⊆ Set.range (algebraMap (G j) R) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f i j hij x, hR.compatibility i j hij x⟩

theorem exists_subset_range_of_finite {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {G : ι → Type v} [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    {R : Type w} [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    {s : Set R} (hs : s.Finite) :
    ∃ i : ι, s ⊆ Set.range (algebraMap (G i) R) := by
  classical

  let idx : R → ι := fun r => (hR.surj r).choose
  have hidx : ∀ r : R, r ∈ Set.range (algebraMap (G (idx r)) R) := fun r =>
    let ⟨x, hx⟩ := (hR.surj r).choose_spec
    ⟨x, hx⟩
  obtain ⟨M, hM⟩ := Finset.exists_le (hs.toFinset.image idx)
  refine ⟨M, fun r hr => ?_⟩
  have hle : idx r ≤ M := hM _ (Finset.mem_image_of_mem idx (hs.mem_toFinset.mpr hr))
  exact range_mono f hR hle (hidx r)

end AlgSpreadDirected

open AlgSpreadDirected in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀), Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by
  classical

  let P := Algebra.Presentation.ofFinitePresentation R A

  obtain ⟨i, hi⟩ := exists_subset_range_of_finite f hR (s := P.coeffs) Algebra.Presentation.finite_coeffs

  letI : Algebra (G i) A := ((algebraMap R A).comp (algebraMap (G i) R)).toAlgebra
  haveI : IsScalarTower (G i) R A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : P.HasCoeffs (G i) := ⟨hi⟩
  exact ⟨i, P.ModelOfHasCoeffs (G i), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (G i)⟩⟩

end S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
end P2MW
export P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit (solution)
