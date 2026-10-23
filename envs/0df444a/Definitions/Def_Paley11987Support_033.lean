-- Prove2me | Definitions.Def_Paley11987Support_033
-- name    : Paley11987Support_033
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:40:22.096289+00:00
-- url     : https://prove2.me/theorems/c5f7502e-da0b-43d6-91bd-d95e1f04ce75
-- title:
--   Counting interface for a tournament core
-- statement:
--   Defines the adjacency relation, orientation and irreflexivity interface, edge sign, out-neighbor counts, common-out-neighbor counts, and reversal of a core.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module CompactDRTCounting.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module CompactDRTCounting, SHA256 351e53a56accd11938d9cabe29c8a1890f194d93a68563ef4a2e310db9a80c12

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
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
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
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018
import Definitions.Def_Paley11987Support_019
import Definitions.Def_Paley11987Support_020
import Definitions.Def_Paley11987Support_021
import Definitions.Def_Paley11987Support_022
import Definitions.Def_Paley11987Support_023
import Definitions.Def_Paley11987Support_024
import Definitions.Def_Paley11987Support_025
import Definitions.Def_Paley11987Support_026
import Definitions.Def_Paley11987Support_027
import Definitions.Def_Paley11987Support_028
import Definitions.Def_Paley11987Support_029
import Definitions.Def_Paley11987Support_030
import Definitions.Def_Paley11987Support_031
import Definitions.Def_Paley11987Support_032

set_option autoImplicit false
set_option Elab.async false
section z49

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Core
variable (C : Core V)

def Adj (x y : V) : Prop := C.sign x y = 1
instance : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ = (1 : ℤ)))

theorem irreflexive (x : V) : ¬ C.Adj x x := by simp [Adj, C.diag]

theorem asymmetric (x y : V) (h : C.Adj x y) : ¬ C.Adj y x := by
  simp only [Adj] at h ⊢
  rw [C.skew, h]
  norm_num

theorem oriented (x y : V) (h : x ≠ y) : C.Adj x y ∨ C.Adj y x := by
  rcases C.off x y h with hh | hh
  · exact Or.inl hh
  · right
    simp [Adj, C.skew x y, hh]

def edge (x y : V) : ℤ := if C.Adj x y then 1 else 0
def outCount (x : V) : ℕ := (univ.filter (C.Adj x)).card
def commonOutCount (x y : V) : ℕ := (univ.filter fun z => C.Adj x z ∧ C.Adj y z).card











def reverse : Core V where
  sign x y := -C.sign x y
  diag x := by simp [C.diag]
  skew x y := by rw [C.skew]
  off x y hxy := by
    rcases C.off x y hxy with h | h <;> simp [h]
  row x := by simp [Finset.sum_neg_distrib, C.row]
  gram x y := by simpa using C.gram x y







end Core

end
end CompactDRT
end z49


