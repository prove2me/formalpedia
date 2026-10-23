-- Prove2me | Definitions.Def_Paley11987Support_051
-- name    : Paley11987Support_051
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T03:24:49.24961+00:00
-- url     : https://prove2.me/theorems/714d6cd6-d23c-48a2-bf2a-0812fbf9c7a6
-- title:
--   Four-stage cycles and transported witnesses
-- statement:
--   Defines the period-certificate structure, typed stage recipes, one-level and cycle coordinate types, the four-stage cycle family, and transport of block and sensitivity witnesses through a cycle.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfile11987SeedCycle.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987SeedCycle, SHA256 d0305e4ae9902217ed6df6e96798ee654e5b25ebb83fd749bbb8eb26b71dad32

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
import Definitions.Def_Paley11987Support_050

set_option autoImplicit false
set_option Elab.async false
section z79

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileSeeds
namespace ZP

structure PeriodCertificate : Prop where
  step0 : TransitionCertificate witness recipe0 stage1
  step1 : TransitionCertificate stage1 recipe1 stage2
  step2 : TransitionCertificate stage2 recipe2 stage3
  step3 : TransitionCertificate stage3 recipe3 stage4

def typedRecipe (r : Recipe) (hr : RecipeValid r) : TypedRecipe 20 where
  target := targetIndex r hr
  guard := guardIndex r hr
  tolerance := tolerance r

abbrev LevelCoord (I : Type) := (Fin 11987 × Fin 2) × I
abbrev CycleCoord (I : Type) := LevelCoord (LevelCoord (LevelCoord (LevelCoord I)))

def cycleFamily {I : Type} (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (F : Fin 20 → (I → Bool) → Bool) :
    Fin 20 → (CycleCoord I → Bool) → Bool :=
  stageFamily T label
    (stageFamily T label
      (stageFamily T label (stageFamily T label F recipe0 recipe0_valid) recipe1 recipe1_valid)
      recipe2 recipe2_valid) recipe3 recipe3_valid

 

 

 def blocks_cycle {I : Type} (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (F : Fin 20 → (I → Bool) → Bool)
    {n : Nat} (w : Blocks F n) : Blocks (cycleFamily T label F) ((11987^4)*n) := by
  let w1 := w.stage T label (typedRecipe recipe0 recipe0_valid) F
  let w2 := w1.stage T label (typedRecipe recipe1 recipe1_valid) _
  let w3 := w2.stage T label (typedRecipe recipe2 recipe2_valid) _
  let w4 := w3.stage T label (typedRecipe recipe3 recipe3_valid) _
  have he : 11987*(11987*(11987*(11987*n))) = (11987^4)*n := by
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_one,Nat.mul_assoc]
  exact he ▸ w4

 def sensitive_cycle {I : Type} (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (F : Fin 20 → (I → Bool) → Bool)
    (hz : ∀ q, F q (fun _ => false) = false)
    {n : Nat} (w : SensitiveWitness F n) : SensitiveWitness (cycleFamily T label F) (16*n) := by
  let w1 := w.stage T label (typedRecipe recipe0 recipe0_valid) F hz 0
  have hz1 := step_zero T label (typedRecipe recipe0 recipe0_valid) F hz
  let w2 := w1.stage T label (typedRecipe recipe1 recipe1_valid) _ hz1 0
  have hz2 := step_zero T label (typedRecipe recipe1 recipe1_valid) _ hz1
  let w3 := w2.stage T label (typedRecipe recipe2 recipe2_valid) _ hz2 0
  have hz3 := step_zero T label (typedRecipe recipe2 recipe2_valid) _ hz2
  let w4 := w3.stage T label (typedRecipe recipe3 recipe3_valid) _ hz3 0
  have he : 2*(2*(2*(2*n))) = 16*n := by omega
  exact he ▸ w4

end ZP
end
end z79


