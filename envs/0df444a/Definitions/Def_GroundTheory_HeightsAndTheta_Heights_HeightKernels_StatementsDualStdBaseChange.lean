-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualStdBaseChange
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualStdBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:57.042463+00:00
-- url     : https://prove2.me/theorems/60641acd-2023-42ad-8095-8276a9dd97fa
-- title:
--   Statements Dual Std Base Change
-- statement:
--   Definitions and structural lemmas for Statements Dual Std Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsDualStdBaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField
noncomputable section
def DualStdBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) * II Unit (PBlk i) ⊥ i (fun _ => fsMulti (PBlk i))
example : ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl⟩
example : HermLine (dualBlocks Unit) × HermLine (PBlk 1) :=
  ⟨dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective, fsMulti (PBlk 1)⟩
example : (fsMulti (PBlk 1)).h (fun _ => 1) = 1 := by
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]
end
end GroundTheory.Heights₂.Heights


