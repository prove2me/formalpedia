-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:23.431551+00:00
-- url     : https://prove2.me/theorems/425b92b2-1e73-4ee5-9a4b-52f1629548e8
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
instance unitaryGroup_compactSpace (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi univ fun _ : Fin m => Set.pi univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)
instance matrix_secondCountable (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
instance unitaryGroup_secondCountable (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _
def tr (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ → Matrix.unitaryGroup (Fin m) ℂ :=
  Matrix.UnitaryGroup.transpose
end PI.UMultOne.UnitaryGroupMassFormula


