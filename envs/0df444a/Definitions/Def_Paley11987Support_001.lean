-- Prove2me | Definitions.Def_Paley11987Support_001
-- name    : Paley11987Support_001
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:36:49.31737+00:00
-- url     : https://prove2.me/theorems/a7bab4a3-9f5d-4305-8176-a8dc27bf6834
-- title:
--   Finite row patterns
-- statement:
--   Defines bounded-size subsets, permitted row patterns, unions of row patterns, and the corresponding row-good predicate.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingRowCounting.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingRowCounting, SHA256 2a5441e5f5e15b76573ac26bb563ea47b7dffba04cb78e0746f8e96adbe6a086

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

set_option autoImplicit false
set_option Elab.async false
section z1

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.RowCounting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]

def smallSubsets (R : Finset Ω) (q : ℕ) : Finset (Finset Ω) :=
  R.powerset.filter (fun s => s.card ≤ q)

def rowPatterns (q d : ℕ) : ℕ :=
  ∑ j : Fin (q + 1), d.choose j.val



def rowUnion (R : ι → Finset Ω) : Finset Ω :=
  Finset.univ.biUnion R

def rowGood (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    Finset (Ω → Fin 2) :=
  Finset.univ.filter (fun a =>
    ∀ i, ((R i).filter (fun e => a e ≠ c e)).card ≤ q i)









end
end ZL.RowCounting
end
end z1


