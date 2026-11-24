-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketEventSupport
-- name    : Sensitivity214439_Phase0_Solutions_SocketEventSupport
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:33:18.385798+00:00
-- url     : https://prove2.me/theorems/8fece68e-06df-49e8-8c06-c6738e095998
-- title:
--   Weighted guard count with one check erased
-- statement:
--   For a selected check $Q$, define the remaining weighted guard count of row $v$ at rank $j$ by
--   $$
--   W_j^{\setminus Q}(v,x)
--   =\sum_{R\in\mathcal G_v\setminus\{Q\}}
--   \operatorname{guardWeight}_j\bigl(h_R(x)\bigr).
--   $$
--   This holds all other checks fixed when analyzing a flip inside the selected check.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/SocketEventSupport.lean lines 137–140; SHA256 130fe497348703de4239bb018f369361b0f106607f6b96d96ba8a7df66968208; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_StrictGateStates
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

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-! Actual one-bit support and decomposition of local gate events. -/
namespace SensitivitySocketEventSupport

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}















def erasedWeightCount (row : RowFamily I Color L) (guards : GuardFamily V S)
    (recipe : GateRecipe S L) (v : V) (j : Fin L)
    (x : ((V × S) × I) → Bool) (selected : Finset (V × S)) : ℕ :=
  ∑ check ∈ (guards v).erase selected, guardWeight recipe j (guardHeight row x check)









end
end SensitivitySocketEventSupport


