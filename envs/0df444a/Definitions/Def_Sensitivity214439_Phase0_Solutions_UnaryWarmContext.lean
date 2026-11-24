-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmContext
-- name    : Sensitivity214439_Phase0_Solutions_UnaryWarmContext
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:40:14.321624+00:00
-- url     : https://prove2.me/theorems/b5f197ca-2099-4312-abe5-ff4f9ef02577
-- title:
--   Actual context for warm unary global gains
-- statement:
--   A warm unary context contains a scaled nested child profile, tournament singleton guards, a nested unary recipe, compatible weak and strong cutoffs, guard monotonicity, destination allowance at most one, and targets above the destination hard cutoff. It fixes an input rejecting the weak rank, a checked prescribed-row bound, a checked global price vector, and its proposed global bound.
--
--   Each row has an actual height state. Positive rows pass the destination hard cutoff; operative high and low rows are classified at that cutoff. High targets have zero outgoing positive neighbors and high guard heads have one. Donors are the positive destinations of those guard heads.
--
--   The context assigns each row its fast total local fee and its height-indexed loss price, and defines both prescribed destination gain sets and the complete global gain set.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryWarmContext.lean lines 18–71; SHA256 9536432961f1914204afe7dde1c46ad2da22d07a002a24fb0d7fb999f3b87158; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_GateInvariants
import Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_OperativeHeadSemantics
import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainSemanticBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryTournamentEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalNumeric
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



/-! A checked numerical warm recipe evaluated on actual independent children. -/
namespace SensitivityUnaryWarmContext

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityOperativeHeads SensitivityOwnTargetBounds
open SensitivityUnaryGainSemantics SensitivityUnaryGainNumeric
open SensitivityUnaryWarmGlobalNumeric SensitivityLocalNumericSemantics
open SensitivityUnaryTournamentEvents SensitivityUnaryPopulationSupport
open SensitivityUnaryWarmLocalPrices SensitivityUnaryWarmDonorCharges
open Sensitivity213981Formal.TournamentHighRows
set_option autoImplicit false

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
  recipe : Recipe
  nesting : RecipeNesting (actualRecipe recipe)
  weak : Fin 12
  strong : Fin 12
  cutoff : Fin 12
  order : weak ≤ strong
  weak_soft : cutoff.val ≤ recipe.soft weak
  weak_hard : cutoff.val ≤ recipe.hard weak
  strong_soft : recipe.soft strong = cutoff.val
  strong_hard : cutoff.val ≤ recipe.hard strong
  weak_monotone : GuardMonotone recipe weak
  strong_monotone : GuardMonotone recipe strong
  allowance : recipe.allowance strong ≤ 1
  targets_above : TargetsAbove (actualRecipe recipe) strong (recipe.hard strong)
  x : ((V × Unit) × I) → Bool
  source : ¬ accepts (gateRow row (unaryTournamentGuards arc) (actualRecipe recipe)) weak x
  cBound : ℕ
  aBound : ℕ
  prices : Prices
  cCheck : warmCheckFast recipe values.profile weak strong cBound = true
  aCheck : check recipe values.profile weak strong prices aBound = true

variable {V I Color : Type} [Fintype V] [Fintype I]

namespace Context

def guards (c : Context V I Color) := unaryTournamentGuards c.arc
def state (c : Context V I Color) (v : V) := actualState c.row c.guards v c.cutoff c.x
def height (c : Context V I Color) (v : V) := rankHeight c.row (socketInput c.x (v,()))
def positive (c : Context V I Color) := positiveRows c.row (c.recipe.hard c.strong) c.x
def high (c : Context V I Color) :=
  operativeHighHeads c.row c.guards (actualRecipe c.recipe) c.strong (c.recipe.hard c.strong) c.x
def low (c : Context V I Color) :=
  operativeLowHeads c.row c.guards (actualRecipe c.recipe) c.strong (c.recipe.hard c.strong) c.x
def targets (c : Context V I Color) := c.high.filter fun v => (c.positive.filter (c.arc v)).card = 0
def guardHeads (c : Context V I Color) := c.high.filter fun v => (c.positive.filter (c.arc v)).card = 1
def donors (c : Context V I Color) := hardDonors c.arc c.positive c.guardHeads
def fee (c : Context V I Color) (v : V) := totalFeeFast c.recipe c.values.profile c.weak c.strong (c.state v)
def loss (c : Context V I Color) (v : V) := c.prices.loss (c.height v)
def rowEvents (c : Context V I Color) (v : V) :=
  rowGainEvents (gateRow c.row c.guards (actualRecipe c.recipe)) v c.strong c.x
def events (c : Context V I Color) :=
  gainEvents (gateRow c.row c.guards (actualRecipe c.recipe)) c.strong c.x



































end Context
end
end SensitivityUnaryWarmContext


