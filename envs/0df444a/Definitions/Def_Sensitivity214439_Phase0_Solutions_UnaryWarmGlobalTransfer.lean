-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalTransfer
-- name    : Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalTransfer
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:52:41.729448+00:00
-- url     : https://prove2.me/theorems/cf8e5da7-ac89-4bfa-85d6-e44e59746764
-- title:
--   Donor-specific cutoffs and unions of warm repair events
-- statement:
--   For a warm context and a guard head $v$ inspecting donor $w$, the donor cutoff is the largest height accepted at both weak and strong ranks when the guard at $w$ is replaced. The donor-head set of $w$ contains all operative guard heads with an arc to $w$.
--
--   The event set charged to donor $w$ is
--   $$
--   \bigcup_{\substack{v\in G\\v\to w}}
--   \operatorname{droppingCoordinates}
--   \bigl(\operatorname{donorCut}(v,w),\{(w,\ast)\},x\bigr).
--   $$
--   This groups repairs affecting the same physical child socket even when that socket is inspected by several heads.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryWarmGlobalTransfer.lean lines 22–27; SHA256 2bdb7b40d4229968243434a3dc852c17f5d28b460b9bf61cba8f43124bbbfa3d; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmContext
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric
namespace SensitivityUnaryGainSemantics
end SensitivityUnaryGainSemantics
namespace SensitivityUnaryPopulationSupport
end SensitivityUnaryPopulationSupport
namespace SensitivityUnaryTournamentEvents
end SensitivityUnaryTournamentEvents
namespace SensitivityUnaryWarmContext
end SensitivityUnaryWarmContext
namespace SensitivityUnaryWarmContext.Context
end SensitivityUnaryWarmContext.Context
namespace SensitivityUnaryWarmDonorCharges
end SensitivityUnaryWarmDonorCharges
namespace SensitivityUnaryWarmGlobalNumeric
end SensitivityUnaryWarmGlobalNumeric
namespace SensitivityUnaryWarmLocalPrices
end SensitivityUnaryWarmLocalPrices
namespace SensitivityUnaryWarmSixCases
end SensitivityUnaryWarmSixCases



/-! Global A for a warm unary tournament follows from its actual repair
coordinates, three small population caps, and the checked six-price table. -/
namespace SensitivityUnaryWarmContext

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityOperativeHeads SensitivityOwnTargetBounds
open SensitivityUnaryGainSemantics SensitivityUnaryGainNumeric
open SensitivityUnaryWarmGlobalNumeric SensitivityLocalNumericSemantics
open SensitivityUnaryTournamentEvents SensitivityUnaryPopulationSupport
open SensitivityUnaryWarmLocalPrices SensitivityUnaryWarmDonorCharges
open SensitivityUnaryWarmSixCases
set_option autoImplicit false

variable {V I Color : Type} [Fintype V] [Fintype I]

namespace Context

def donorCut (c : Context V I Color) (v w : V) : ℕ :=
  guardTopFast c.recipe c.weak c.strong (c.state v) (c.height w)
def donorHeads (c : Context V I Color) (w : V) : Finset V :=
  c.guardHeads.filter fun v => c.arc v w
def donorEvents (c : Context V I Color) (w : V) :=
  (c.donorHeads w).biUnion fun v => droppingCoordinates c.row (c.donorCut v w) c.x {(w,())}




















end Context
end
end SensitivityUnaryWarmContext


