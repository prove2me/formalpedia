-- Prove2me | Definitions.Def_Paley11987Support_034
-- name    : Paley11987Support_034
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:44:31.664263+00:00
-- url     : https://prove2.me/theorems/4e233973-f8fa-4aa6-aa68-b03cff7a7bf6
-- title:
--   The selected core of order 11987
-- statement:
--   Provides the prime-field instance for $11987$, the characteristic facts, the vertex type and its cardinality, and the selected Paley core and adjacency relation.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module CompactDRT11987.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module CompactDRT11987, SHA256 bd4d6dbe96272f9f57c010290522bbc391ec77845b63db80ec79e96b60ade6eb

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
import Definitions.Def_Paley11987Support_033

set_option autoImplicit false
set_option Elab.async false
section z50

namespace CompactDRT
noncomputable section
open Finset

instance : Fact (Nat.Prime 11987) := ⟨by norm_num⟩

theorem char11987_ne_two : ringChar (ZMod 11987) ≠ 2 := by
  norm_num [ZMod.ringChar_zmod_n]

theorem char11987_neg_one : quadraticChar (ZMod 11987) (-1) = -1 := by
  rw [quadraticChar_neg_one char11987_ne_two, ZMod.card]
  decide +kernel

abbrev Vertex11987 := ZMod 11987
def core11987 : Core Vertex11987 := paleyCore char11987_ne_two char11987_neg_one
attribute [local irreducible] core11987
abbrev Adj11987 := core11987.Adj

theorem vertex11987_card : Fintype.card Vertex11987 = 11987 := ZMod.card 11987









end
end CompactDRT
end z50


