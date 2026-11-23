-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
-- name    : GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:18.548845+00:00
-- url     : https://prove2.me/theorems/5322c8ac-6266-4c12-a077-3beded2ad074
-- title:
--   Lattice Poisson Basic
-- statement:
--   Definitions and structural lemmas for Lattice Poisson Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
section DualLattice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem innerₗ_nondegenerate : (innerₗ E : LinearMap.BilinForm ℝ E).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun y hy => inner_self_eq_zero.mp (hy y)⟩
def dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L
theorem dualLattice_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    dualLattice (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ
      (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis _ _ b
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
theorem dualLattice_eq_span : dualLattice L = Submodule.span ℤ
    (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate
      ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  classical
  conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  exact dualLattice_span_eq _
instance : DiscreteTopology (dualLattice L) := by
  rw [dualLattice_eq_span L]; infer_instance
instance : IsZLattice ℝ (dualLattice L) :=
  ⟨by rw [dualLattice_eq_span L]; exact ZSpan.span_top _⟩
end DualLattice
section Summability
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end Summability
end
end GroundTheory.Global


