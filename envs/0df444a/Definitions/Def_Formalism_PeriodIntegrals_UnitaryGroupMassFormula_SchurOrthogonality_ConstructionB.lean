-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:16.611798+00:00
-- url     : https://prove2.me/theorems/faf33fed-6029-4fbd-82b3-63e813a5ada2
-- title:
--   Construction B
-- statement:
--   Definitions and structural lemmas for Construction B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix
theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · have e : (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) =
        {A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff
    rw [e]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hA i j
instance compactSpace_unitaryGroup (N : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)
end PI.WSF


