-- Prove2me | Definitions.Def_Sensitivity213303_SelectedBoolCaps
-- name    : Sensitivity213303_SelectedBoolCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:34:07.973204+00:00
-- url     : https://prove2.me/theorems/28bae949-ee1d-483b-b4de-bcfe29f125db
-- title:
--   Transporting the selected binary labeling to Boolean child positions
-- statement:
--   bit maps a value of Fin 2 to the Boolean test that it equals 1; colorBit maps false and true back to 0 and 1. boolLabel applies this conversion to each edge label. The concrete label is the Boolean version of the selected 10007-vertex jointly avoiding labeling. These conversions identify the labeling predicates used in the finite probabilistic construction with the Boolean child selectors used in the recursive parent.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module SelectedBoolCaps; source SHA256 dee6213e2a8dd8450bb4d5016caae5e4336c0de164e67fc9b71a2c9b839dbf5e.

/- The actual Paley-10007 label satisfies the Bool-valued exclusion interfaces
used by the graded-candidate and residual-cap proofs. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_Endpoint40Recipes
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_MinMaxNesting
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_Selected10007
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
namespace Sensitivity10007Labeling
end Sensitivity10007Labeling


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Sensitivity10007BoolCaps
open Sensitivity10007Labeling
open scoped Classical BigOperators
noncomputable section

def bit (c : Fin 2) : Bool := decide (c = 1)

def colorBit (b : Bool) : Fin 2 := if b then 1 else 0





def boolLabel {V : Type} (ell : V × V → Fin 2) : V → V → Bool :=
  fun v w => bit (ell (v,w))

variable {V : Type} [Fintype V] [DecidableEq V]



















def label : Fin 10007 → Fin 10007 → Bool := boolLabel Labeling10007.selectedLabel











end
end Sensitivity10007BoolCaps


