-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossAggregation
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossAggregation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:11:53.836699+00:00
-- url     : https://prove2.me/theorems/6959937d-ff84-42a4-b3f1-5b2702bdc346
-- title:
--   Guard-supported row-loss events
-- statement:
--   For a colored child family, a gate recipe, a parent row $v$, weak rank $i$, and input $x$, define the loss events supported on a check $Q$ by
--   $$
--   \operatorname{guardLossEvents}(v,i,x,Q)
--   =\{b\in\operatorname{rowLossEvents}(v,i,x):\operatorname{socket}(b)\in Q\}.
--   $$
--   The support restriction keeps the full parent bit coordinate, so these sets can be combined directly with the own-target loss sets.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossAggregation.lean lines 32–35; SHA256 e6597115f50299a975b027f60b313a3075379554d0c8622031646fff530578f7; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

namespace SensitivityBaselineGuardFees
end SensitivityBaselineGuardFees
namespace SensitivityBaselineLossAggregation
end SensitivityBaselineLossAggregation
namespace SensitivityBaselineOwnLoss
end SensitivityBaselineOwnLoss
namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport



/-! Assemble baseline loss fees on the actual independent socket family. -/
namespace SensitivityBaselineLossAggregation

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivitySocketEventSupport SensitivityBaselineOwnLoss
open SensitivityFiniteRanks SensitivityLocalNumericSemantics
open SensitivityBaselineGuardFees

variable {V S I Color : Type} {L : ℕ}



def guardLossEvents [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (weak : Fin L) (x : ((V × S) × I) → Bool) (check : Finset (V × S)) :=
  (rowLossEvents (gateRow row guards recipe) v weak x).filter fun bit => bit.1 ∈ check










end
end SensitivityBaselineLossAggregation


