-- Prove2me | Definitions.Def_Paley11987Support_009
-- name    : Paley11987Support_009
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:44:50.62461+00:00
-- url     : https://prove2.me/theorems/ca51be0e-1d36-401d-852d-4442e0f13c8c
-- title:
--   Marked assignment enumeration
-- statement:
--   Defines marked rows, their remaining row budgets, and the marked assignment family used in the weighted count.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingMarkedCounting.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingMarkedCounting, SHA256 67f3fd091cae11026c4e288efda89adc577045a89681bb973285e98a8a0b9883

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

set_option autoImplicit false
set_option Elab.async false
section z11

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

def markedRows (A M : Finset V) : A ⊕ M → Finset (V × V) :=
  Sum.elim (fun i => outgoingRow R A i.val) (fun i => outgoingRow R A i.val)



def markedRowBudget (A M P : Finset V) (q B : ℕ) : A ⊕ M → ℕ :=
  Sum.elim (fun x => q - (outOn R M x.val).card)
    (fun _y => if B=0 then 0 else q+1)



def markedAssignments (A M P : Finset V) (q B : ℕ) : Finset ((V × V) → Fin 2) :=
  Finset.univ.filter (fun ell => MarkedBad R ell A M P q B)







end
end ZL
end
end z11


