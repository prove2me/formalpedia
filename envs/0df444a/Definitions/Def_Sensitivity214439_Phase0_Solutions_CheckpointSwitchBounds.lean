-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointSwitchBounds
-- name    : Sensitivity214439_Phase0_Solutions_CheckpointSwitchBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:32:47.06041+00:00
-- url     : https://prove2.me/theorems/149b0bba-da20-451e-9ad9-60c0488f2cc2
-- title:
--   Phase-zero switching cutoff and target functions
-- statement:
--   The switching guard rank for the unary phase is its effective forbidden cutoff: the hard cutoff when it is below $12$, and the soft cutoff otherwise. The switching target rank is the phase-zero target at zero failures:
--   $$
--   g_j=\begin{cases}h_j,&h_j<12,\\s_j,&h_j\ge12,\end{cases}
--   \qquad
--   t_j=\operatorname{phase0Target}(j,0).
--   $$
--   Both are represented as elements of the twelve-rank finite type.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/CheckpointSwitchBounds.lean lines 13–16; SHA256 a03b4c5d4b1895877cdcb2eede49aebcbb3ee94f4ec5e5b5305b59adc6de4cbb; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointRankMapConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGateSwitchBounds
end SensitivityGateSwitchBounds
namespace SensitivityGateSwitchNumeric
end SensitivityGateSwitchNumeric
namespace SensitivityLocalNumeric
end SensitivityLocalNumeric
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



namespace SensitivityRankMapCheckpoint

open SensitivityRankedConstruction SensitivityProfile456 SensitivityGateSwitchBounds
open SensitivityGateSwitchNumeric SensitivityLocalNumericSemantics
open SensitivityLocalNumeric
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def phase0SwitchGuard (j : Fin 12) : Fin 12 :=
  Fin.ofNat 12 (if phase0Hard j < 12 then phase0Hard j else phase0Soft j)

def phase0SwitchTarget (j : Fin 12) : Fin 12 := phase0Target j 0













































































































end SensitivityRankMapCheckpoint


