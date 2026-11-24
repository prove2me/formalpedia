-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryBaselineSource
-- name    : Sensitivity214439_Phase0_Solutions_UnaryBaselineSource
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:12:19.510729+00:00
-- url     : https://prove2.me/theorems/5fe2819e-248b-407c-bf07-8a6b0298e18d
-- title:
--   An actual unary source realized as a finite baseline state
-- statement:
--   A unary source context links a parent row and interval $i\le j$ to a baseline numerical state. The two stored child ranks coincide; the own child has that exact global rank and a specified accepted color. The weak and strong soft guard counts equal the state's recorded counts, and the state is admissible.
--
--   The context also carries the acceptance equivalence at every parent rank: actual unary gate acceptance is exactly scalar baseline acceptance using the actual soft and hard counts and the stored child rank. This interface permits finite baseline certificates to price actual row-loss events.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryBaselineSource.lean lines 22–35; SHA256 f307d3e995014ec61409b4eb119b808da978eb04feb6e57df7a2a1b956325ea8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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

namespace SensitivityBaselineGuardStates
end SensitivityBaselineGuardStates
namespace SensitivityBaselineLossAggregation
end SensitivityBaselineLossAggregation
namespace SensitivityBaselineOwnLoss
end SensitivityBaselineOwnLoss
namespace SensitivityBaselineSourceCover
end SensitivityBaselineSourceCover
namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityUnaryBaselineSource
end SensitivityUnaryBaselineSource



/-! Unary exact-source coverage and fees for the baseline M transfer. -/
namespace SensitivityUnaryBaselineSource

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityStrictGateStates SensitivityLocalNumericSemantics
open SensitivityBaselineSourceCover SensitivityBaselineLossAggregation
open SensitivityBaselineGuardStates SensitivityBaselineOwnLoss SensitivityOwnTargetBounds

variable {V I Color : Type}



structure UnarySourceContext (row : RowFamily I Color 12) (guards : GuardFamily V Unit)
    (r : SensitivityBaselineLossNumeric.Recipe) (v : V) (i j : Fin 12)
    (x : ((V × Unit) × I) → Bool) where
  state : SensitivityBaselineLossNumeric.State
  same : state.a = state.b
  color : Color
  exact_a : ExactGlobalRank row state.a (socketInput x (v,()))
  color_a : row color state.a (socketInput x (v,()))
  count_i : guardCount row guards v (r.soft i) x = state.fi.val
  count_j : guardCount row guards v (r.soft j) x = state.fj.val
  admissible : SensitivityBaselineLossNumeric.Admissible r i j state
  accepts_iff : ∀ k, gateRow row guards (unaryRecipe r.soft r.hard r.allowance r.lo) v k x ↔
    SensitivityBaselineLossNumeric.accepts r k (guardCount row guards v (r.soft k) x)
      (guardCount row guards v (r.hard k) x) state.a.val state.b.val











end
end SensitivityUnaryBaselineSource


