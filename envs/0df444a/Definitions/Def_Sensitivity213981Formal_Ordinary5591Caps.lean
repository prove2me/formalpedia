-- Prove2me | Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
-- name    : Sensitivity213981Formal_Ordinary5591Caps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:42:17.69168+00:00
-- url     : https://prove2.me/theorems/35e96564-3538-4ad7-9942-81ef0a135b26
-- title:
--   Ordinary5591 Caps — sensitivity certificate definitions
-- statement:
--   The definitions for Ordinary5591 Caps in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundOrdinary5591.guardCap`, `ThreeBoundOrdinary5591.targetCap`, `ThreeBoundOrdinary5591.candidateTotalCap`, `ThreeBoundOrdinary5591.markedCap`, `ThreeBoundOrdinary5591.positiveCaseCost`, `ThreeBoundOrdinary5591.LabelCaps`, `ThreeBoundOrdinary5591.numericCaps`, `ThreeBoundOrdinary5591.cutoff`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Ordinary5591Caps.lean, lines 1–189.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
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

namespace Sensitivity213981Formal
section
/- The exact ordinary caps needed for the third endpoint.  The actual flip
accounting below reuses the proved ordinary transfer argument; only the
exclusion constants change.  Small-tolerance branches are not used here. -/


set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace ThreeBoundOrdinary5591
open ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive.OAI.Paper320
open ThreeBoundOrdinaryArchive.Sensitivity2075
open ThreeBoundOrdinaryArchive.SensitivityQ
open ThreeBoundOrdinaryArchive.ZT
open scoped Classical BigOperators
noncomputable section

def numericCaps : ThreeBoundNumeric.Caps := {
  ordinary := #[21,29,35,41,47,52,57,63,68]
  guard := #[19,26,32,38,44,51,56,62,67]
  target := #[19,27,33,39,45,51,56,62,67]
  marked := #[27,33,39,45,25,31,22,26,29,27,31,25]
  zero := #[20,18,16,18,19,16,17,16]
  pcross := 18 }

def cutoff (q : ℕ) : ℕ := ThreeBoundNumeric.Caps.at numericCaps.ordinary q
def guardCap (q : ℕ) : ℕ := ThreeBoundNumeric.Caps.at numericCaps.guard q
def targetCap (q : ℕ) : ℕ := ThreeBoundNumeric.Caps.at numericCaps.target q

def candidateTotalCap (q m u : ℕ) : ℕ :=
  let t := if 0< m then min (cutoff q-m) (guardCap q) else cutoff q-1
  if 0< u then min t (targetCap q) else t

def markedCap (q m : ℕ) : ℕ := if q=4 ∧ m=6 then 30 else 1000000000

def positiveCaseCost (q m u a b s j : ℕ) : ℕ :=
  let E := m*(q+1)-m.choose 2
  let L := (u*m+u.choose 2)-q*u
  let save := L-u
  let intr := min (m.choose 2) (2*m)
  u*a+deletionCost (markedCap q m) (candidateTotalCap q m u-u)
    (E-save) (intr+min u save) (E-L) b s j

variable {n k : ℕ} {I : Type} [Fintype I]

/-- The only label exclusions used by ordinary rows of tolerance at least four. -/
structure LabelCaps (T : Tournament k) (label : Fin k → Fin k → Fin 2) : Prop where
  ordinary : ∀ q, 4 ≤  q → q ≤  8 → DefectBound T label q (cutoff q)
  one_four : MarkedCardBound T label 4 1 0 5 45
  zero_four_six : MarkedCardBound T label 4 6 0 0 31







end
end ThreeBoundOrdinary5591



end
end Sensitivity213981Formal


