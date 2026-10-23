-- Prove2me | Definitions.Def_Paley11987Support_031
-- name    : Paley11987Support_031
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:33:58.960756+00:00
-- url     : https://prove2.me/theorems/172fe7df-a0c3-4a6c-a8a3-f54ecd0c3f4c
-- title:
--   Doubly regular tournament cores
-- statement:
--   Defines the diagonal correction and core structure used to represent a doubly regular tournament, with the structural identities required by the interface.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module CompactDRTCore.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module CompactDRTCore, SHA256 0d9333be96eda50cd88285c6d70465413598ed135aa7f35625add296ffbb6d1a

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

set_option autoImplicit false
set_option Elab.async false
section z47

namespace CompactDRT
open Finset
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

def delta (x y : V) : ℤ := if x = y then 1 else 0

@[simp] theorem delta_self (x : V) : delta x x = 1 := by simp [delta]

@[simp] theorem sum_delta (x : V) : ∑ z : V, delta x z = 1 := by simp [delta]



structure Core (V : Type*) [Fintype V] [DecidableEq V] where
  sign : V → V → ℤ
  diag : ∀ x, sign x x = 0
  skew : ∀ x y, sign y x = -sign x y
  off : ∀ x y, x ≠ y → sign x y = 1 ∨ sign x y = -1
  row : ∀ x, ∑ z, sign x z = 0
  gram : ∀ x y, ∑ z, sign x z * sign y z = (Fintype.card V : ℤ) * delta x y - 1

namespace Core




















end Core
end CompactDRT
end z47


