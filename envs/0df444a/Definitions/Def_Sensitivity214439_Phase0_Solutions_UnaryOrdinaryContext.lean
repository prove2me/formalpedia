-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryContext
-- name    : Sensitivity214439_Phase0_Solutions_UnaryOrdinaryContext
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:40:14.170625+00:00
-- url     : https://prove2.me/theorems/96f4006c-a725-42ed-a92e-4d59f5452a7e
-- title:
--   Actual population context for ordinary phase-zero unary gains
-- statement:
--   An ordinary unary context contains a scaled child profile with nonnegative scale, child nesting, a tournament with disjoint non-self singleton guards, an interval $i\le j<5$, and an input rejecting the weak rank. It also fixes valid ordinary prices and an accepted numerical global bound.
--
--   Derived quantities include the destination and weak allowances, own child heights, and active-check counts at cutoff $5$. Positive rows pass cutoff $5$; high and low rows are the operative rows classified by this positivity. High targets have own height at most $7$, while high guard heads have height above $7$. Donors are positive outgoing neighbors of guard heads, and external donors lie outside the high set.
--
--   The context defines prescribed row gains, donor drops at cutoff $5$, target events augmented by drops when the target is also a donor, and the global destination gain set.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryContext.lean lines 19–64; SHA256 a98ec11491991f2b76881021bd6b9a8b9d55c5798d1003f42ce218d86dd5fb80; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_OperativeHeadSemantics
import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainSemanticBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryTournamentEvents
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
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal.TournamentHighRows
end Sensitivity213981Formal.TournamentHighRows
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
namespace SensitivityUnaryGainSemantics
end SensitivityUnaryGainSemantics
namespace SensitivityUnaryOrdinaryContext
end SensitivityUnaryOrdinaryContext
namespace SensitivityUnaryOrdinaryContext.Context
end SensitivityUnaryOrdinaryContext.Context
namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric
namespace SensitivityUnaryPopulationSupport
end SensitivityUnaryPopulationSupport
namespace SensitivityUnaryTournamentEvents
end SensitivityUnaryTournamentEvents
namespace SensitivityUnaryWarmDonorCharges
end SensitivityUnaryWarmDonorCharges



/-! Actual ordinary unary repair heads have only two height classes. -/
namespace SensitivityUnaryOrdinaryContext

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityOperativeHeads SensitivityOwnTargetBounds
open SensitivityUnaryGainSemantics SensitivityLocalNumericSemantics
open SensitivityUnaryTournamentEvents SensitivityUnaryPopulationSupport
open SensitivityUnaryOrdinaryGlobalNumeric SensitivityUnaryWarmDonorCharges
open Sensitivity213981Formal.TournamentHighRows
set_option autoImplicit false

abbrev recipe := SensitivityUnaryGainNumeric.phase0

structure Context (V I Color : Type) [Fintype V] [Fintype I] where
  row : RowFamily I Color 12
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  values : NumericBounds
  child : Bounds row 5 (scaledProfile scale values)
  nested : Nested row
  arc : V → V → Prop
  tournament : IsTournament arc
  self : NoSelfGuards (unaryTournamentGuards arc)
  disjoint : DisjointChecks (unaryTournamentGuards arc)
  weak : Fin 12
  strong : Fin 12
  order : weak ≤ strong
  ordinary : strong.val < 5
  x : ((V × Unit) × I) → Bool
  source : ¬ accepts (gateRow row (unaryTournamentGuards arc) (actualRecipe recipe)) weak x
  prices : Prices
  price_valid : PriceValid values.profile prices
  aBound : ℕ
  aCheck : check (recipe.allowance strong) (decide (weak = strong)) prices aBound = true

variable {V I Color : Type} [Fintype V] [Fintype I]

namespace Context

def guards (c : Context V I Color) := unaryTournamentGuards c.arc
def q (c : Context V I Color) := recipe.allowance c.strong
def weakQ (c : Context V I Color) := recipe.allowance c.weak
def height (c : Context V I Color) (v : V) := rankHeight c.row (socketInput c.x (v,()))
def count (c : Context V I Color) (v : V) := guardCount c.row c.guards v 5 c.x
def positive (c : Context V I Color) := positiveRows c.row 5 c.x
def high (c : Context V I Color) := operativeHighHeads c.row c.guards (actualRecipe recipe) c.strong 5 c.x
def low (c : Context V I Color) := operativeLowHeads c.row c.guards (actualRecipe recipe) c.strong 5 c.x
def targets (c : Context V I Color) := c.high.filter fun v => c.height v ≤ 7
def guardHeads (c : Context V I Color) := c.high.filter fun v => 7 < c.height v
def donors (c : Context V I Color) := hardDonors c.arc c.positive c.guardHeads
def external (c : Context V I Color) := c.donors \ c.high
def rowEvents (c : Context V I Color) (v : V) :=
  rowGainEvents (gateRow c.row c.guards (actualRecipe recipe)) v c.strong c.x
def dropEvents (c : Context V I Color) (w : V) := droppingCoordinates c.row 5 c.x {(w,())}
def targetEvents (c : Context V I Color) (w : V) :=
  c.rowEvents w ∪ if w ∈ c.donors then c.dropEvents w else ∅
def events (c : Context V I Color) := gainEvents (gateRow c.row c.guards (actualRecipe recipe)) c.strong c.x

















































end Context
end
end SensitivityUnaryOrdinaryContext


