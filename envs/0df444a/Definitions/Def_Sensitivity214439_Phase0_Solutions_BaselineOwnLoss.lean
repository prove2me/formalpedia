-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineOwnLoss
-- name    : Sensitivity214439_Phase0_Solutions_BaselineOwnLoss
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T17:59:23.286379+00:00
-- url     : https://prove2.me/theorems/bc9a7fdf-29b9-4738-aa78-9bc305c11543
-- title:
--   Own-socket row-loss events
-- statement:
--   For a parent row $v$, side $s$, rank $j$, and input $x$, the own-loss set consists of child coordinates whose flip in socket $(v,s)$ makes that row reject:
--   $$
--   \operatorname{ownLossEvents}(v,j,x,s)
--   =\{b:\neg G_v(j,\operatorname{flip}_{((v,s),b)}x)\}.
--   $$
--   The set is defined independently of old acceptance; the loss-bound theorems supply acceptance hypotheses when using it.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineOwnLoss.lean lines 13–17; SHA256 32eeda0752cfeba61409839ec0b750bfff19c1f9dda514a678b0c153df7d9045; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_SensitivitySeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityBaselineOwnLoss
end SensitivityBaselineOwnLoss
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityTargetEvents
end SensitivityTargetEvents



/-! Exact own-socket contributions to the baseline B/M transfer, at every rank. -/
namespace SensitivityBaselineOwnLoss

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityTargetEvents SensitivityOwnTargetBounds

variable {V S I Color : Type} {L core : ℕ}

def ownLossEvents [Fintype I]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) (s : S) : Finset I :=
  Finset.univ.filter fun i => ¬ gateRow row guards recipe v j
    (OAI.Paper320.flip x {((v,s),i)})












end
end SensitivityBaselineOwnLoss


