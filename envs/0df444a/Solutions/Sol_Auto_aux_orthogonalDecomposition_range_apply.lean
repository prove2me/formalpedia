-- Prove2me | solution 1 for Auto.aux_orthogonalDecomposition_range_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:37.108399+00:00
-- url     : https://prove2.me/submissions/dd310cd5-8782-44a5-80cc-140030fe74f7

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (π : E →L[ℝ] F) (x : E) :
    let s : Submodule ℝ F := π.range
    let e : F ≃L[ℝ] s × sᗮ :=
      s.orthogonalDecomposition.toContinuousLinearEquiv.trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ)
    e (π x) = (π.rangeRestrict x, 0) := by
  dsimp only
  rw [ContinuousLinearEquiv.trans_apply]
  change (WithLp.prodContinuousLinearEquiv 2 ℝ π.range (π.range)ᗮ)
      ((π.range).orthogonalDecomposition (π x)) = (π.rangeRestrict x, 0)
  rw [Submodule.orthogonalDecomposition_apply, WithLp.prodContinuousLinearEquiv_apply]
  change ((π.range).orthogonalProjectionOnto (π x),
    (π.range)ᗮ.orthogonalProjectionOnto (π x)) = (π.rangeRestrict x, 0)
  have hx : π x ∈ π.range := π.mem_range_self x
  apply Prod.ext
  · calc
      (π.range).orthogonalProjectionOnto (π x) = (⟨π x, hx⟩ : π.range) :=
        (π.range).orthogonalProjectionOnto_mem_subspace_eq_self ⟨π x, hx⟩
      _ = π.rangeRestrict x := Subtype.ext (by rfl)
  · exact (π.range).orthogonalProjectionOnto_orthogonal_apply_eq_zero hx
end Auto
