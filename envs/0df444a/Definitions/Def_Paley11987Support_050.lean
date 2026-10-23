-- Prove2me | Definitions.Def_Paley11987Support_050
-- name    : Paley11987Support_050
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T03:20:35.010184+00:00
-- url     : https://prove2.me/theorems/fc845c7c-f5fc-4b0c-949b-0871cafe488a
-- title:
--   Validity of the recorded recipes
-- statement:
--   Provides the structural validity proofs needed to use each of the four fixed recipe arrays as a typed stage recipe.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfile11987ExtraFacts.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987ExtraFacts, SHA256 71222e3cba2dd952d06a6e275c45ff0a20474d5483ef9f067f5e3b5d1101addc

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
import Definitions.Def_Paley11987Support_034
import Definitions.Def_Paley11987Support_035
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_037
import Definitions.Def_Paley11987Support_038
import Definitions.Def_Paley11987Support_039
import Definitions.Def_Paley11987Support_040
import Definitions.Def_Paley11987Support_041
import Definitions.Def_Paley11987Support_042
import Definitions.Def_Paley11987Support_043
import Definitions.Def_Paley11987Support_044
import Definitions.Def_Paley11987Support_045
import Definitions.Def_Paley11987Support_046
import Definitions.Def_Paley11987Support_047
import Definitions.Def_Paley11987Support_048
import Definitions.Def_Paley11987Support_049

set_option autoImplicit false
set_option Elab.async false
section z78
namespace ZP
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000
theorem recipe0_valid : RecipeValid recipe0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem recipe1_valid : RecipeValid recipe1 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem recipe2_valid : RecipeValid recipe2 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem recipe3_valid : RecipeValid recipe3 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel



























end ZP
end z78


