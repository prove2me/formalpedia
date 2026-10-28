-- Prove2me | Definitions.Def_Sensitivity213303_Endpoint40Recipes
-- name    : Sensitivity213303_Endpoint40Recipes
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:31:13.339961+00:00
-- url     : https://prove2.me/theorems/68835f4c-8563-4264-b9e3-0e7ddb8f0790
-- title:
--   The four concrete guarded parent stages on 10,007 tournament vertices
-- statement:
--   These definitions fix the actual recursive Boolean construction for the first endpoint: the selected binary labeling on the 10,007-vertex tournament, four phase recipes on 40 ordered levels, their guard indices, target thresholds and tolerances, and the periodically iterated Boolean family. Each parent stage combines two children per vertex using the recipe target test and the allowed number of selected-child guard failures.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Endpoint40Recipes; source SHA256 29f22a4ef4d356b61cf2fa543f64c86ce5c8d7b35757403272c08ed0ee60a55c.

/- Actual 40-level recipes from the 2.13303 checkpoint.
Source certificate SHA-256: 4e0d5e2f6eaa601198bb5034680c7bc4a24fc1b0af7fea31fe4aaf9f090acf1f
-/
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_MinMaxNesting
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_Selected10007
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
namespace ThreeBoundNesting
end ThreeBoundNesting
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

namespace Sensitivity10007Endpoint40
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting

structure Entry where
  t0 : Fin 40
  t1 : Fin 40
  t2 : Fin 40
  guard : Fin 40
  tolerance : ℕ
  deriving Inhabited

def Entry.threshold (e : Entry) (b : ℕ) : Fin 40 :=
  if 3 ≤ e.tolerance ∨ b = 0 then e.t0 else if b = 1 then e.t1 else e.t2

theorem Entry.threshold_monotone (e : Entry) (h01 : e.t0 ≤ e.t1)
    (h12 : e.t1 ≤ e.t2) : Monotone e.threshold := by
  intro a b hab
  unfold threshold
  split_ifs <;> first | exact le_rfl | exact h01 | exact h12 | exact h01.trans h12 | omega

def entries0 : Array Entry := #[
  ⟨12,12,12,8,3⟩,
  ⟨17,21,27,8,2⟩,
  ⟨21,28,28,8,1⟩,
  ⟨23,23,23,8,0⟩,
  ⟨23,23,23,8,0⟩,
  ⟨27,27,27,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨28,28,28,8,0⟩,
  ⟨29,29,29,8,0⟩,
  ⟨29,29,29,8,0⟩,
  ⟨29,29,29,8,0⟩,
  ⟨29,29,29,4,0⟩,
  ⟨29,29,29,4,0⟩,
  ⟨30,30,30,3,0⟩,
  ⟨31,31,31,3,0⟩,
  ⟨33,33,33,3,0⟩,
  ⟨33,33,33,3,0⟩,
  ⟨35,35,35,3,0⟩,
  ⟨35,35,35,3,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,1,0⟩,
  ⟨39,39,39,1,0⟩
]

def entries1 : Array Entry := #[
  ⟨13,13,13,10,4⟩,
  ⟨15,15,15,10,3⟩,
  ⟨19,22,25,10,2⟩,
  ⟨21,24,24,10,1⟩,
  ⟨23,25,25,10,1⟩,
  ⟨26,29,29,10,1⟩,
  ⟨26,29,29,10,1⟩,
  ⟨26,32,32,10,1⟩,
  ⟨26,32,32,10,1⟩,
  ⟨26,34,34,10,1⟩,
  ⟨26,38,38,10,1⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨26,26,26,10,0⟩,
  ⟨27,27,27,10,0⟩,
  ⟨32,32,32,7,0⟩,
  ⟨32,32,32,6,0⟩,
  ⟨32,32,32,6,0⟩,
  ⟨32,32,32,6,0⟩,
  ⟨32,32,32,6,0⟩,
  ⟨32,32,32,2,0⟩,
  ⟨32,32,32,2,0⟩,
  ⟨32,32,32,2,0⟩,
  ⟨32,32,32,2,0⟩,
  ⟨32,32,32,2,0⟩,
  ⟨32,32,32,1,0⟩,
  ⟨32,32,32,1,0⟩,
  ⟨32,32,32,1,0⟩,
  ⟨33,33,33,1,0⟩,
  ⟨35,35,35,1,0⟩,
  ⟨35,35,35,1,0⟩,
  ⟨35,35,35,1,0⟩,
  ⟨35,35,35,0,0⟩,
  ⟨35,35,35,0,0⟩,
  ⟨38,38,38,0,0⟩
]

def entries2 : Array Entry := #[
  ⟨18,18,18,18,7⟩,
  ⟨20,20,20,18,4⟩,
  ⟨20,20,25,18,2⟩,
  ⟨21,27,27,18,1⟩,
  ⟨23,23,23,18,0⟩,
  ⟨23,23,23,18,0⟩,
  ⟨23,23,23,18,0⟩,
  ⟨23,23,23,18,0⟩,
  ⟨26,26,26,18,0⟩,
  ⟨27,27,27,18,0⟩,
  ⟨27,27,27,18,0⟩,
  ⟨27,27,27,18,0⟩,
  ⟨29,29,29,18,0⟩,
  ⟨29,29,29,18,0⟩,
  ⟨29,29,29,18,0⟩,
  ⟨29,29,29,18,0⟩,
  ⟨29,29,29,18,0⟩,
  ⟨29,29,29,18,0⟩,
  ⟨30,30,30,13,0⟩,
  ⟨30,30,30,13,0⟩,
  ⟨30,30,30,13,0⟩,
  ⟨30,30,30,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨35,35,35,13,0⟩,
  ⟨35,35,35,12,0⟩,
  ⟨35,35,35,11,0⟩,
  ⟨35,35,35,11,0⟩,
  ⟨36,36,36,11,0⟩,
  ⟨36,36,36,11,0⟩,
  ⟨36,36,36,11,0⟩,
  ⟨36,36,36,5,0⟩,
  ⟨36,36,36,4,0⟩,
  ⟨36,36,36,4,0⟩,
  ⟨36,36,36,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,2,0⟩,
  ⟨39,39,39,1,0⟩,
  ⟨39,39,39,0,0⟩
]

def entries3 : Array Entry := #[
  ⟨17,17,17,13,4⟩,
  ⟨20,20,20,13,4⟩,
  ⟨21,21,21,13,3⟩,
  ⟨23,23,33,13,2⟩,
  ⟨23,33,33,13,1⟩,
  ⟨23,23,23,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨33,33,33,13,0⟩,
  ⟨34,34,34,13,0⟩,
  ⟨34,34,34,13,0⟩,
  ⟨34,34,34,13,0⟩,
  ⟨34,34,34,13,0⟩,
  ⟨34,34,34,13,0⟩,
  ⟨34,34,34,9,0⟩,
  ⟨35,35,35,9,0⟩,
  ⟨35,35,35,9,0⟩,
  ⟨35,35,35,9,0⟩,
  ⟨35,35,35,9,0⟩,
  ⟨35,35,35,9,0⟩,
  ⟨35,35,35,3,0⟩,
  ⟨35,35,35,3,0⟩,
  ⟨35,35,35,3,0⟩,
  ⟨38,38,38,2,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,1,0⟩,
  ⟨38,38,38,0,0⟩,
  ⟨39,39,39,0,0⟩,
  ⟨39,39,39,0,0⟩
]

def entry (p : Fin 4) (l : Fin 40) : Entry :=
  match p.val with
  | 0 => entries0.getD l.val default
  | 1 => entries1.getD l.val default
  | 2 => entries2.getD l.val default
  | _ => entries3.getD l.val default

theorem entry_internal_order : ∀ p l,
    (entry p l).t0 ≤ (entry p l).t1 ∧
    (entry p l).t1 ≤ (entry p l).t2 ∧
    (entry p l).tolerance ≤ 8 := by decide +kernel

theorem entry_pair_order : ∀ (p : Fin 4) (i j : Fin 40), i ≤ j →
    (entry p j).guard ≤ (entry p i).guard ∧
    (entry p j).tolerance ≤ (entry p i).tolerance ∧
    ∀ b : Fin 9, b.val ≤ (entry p j).tolerance →
      (entry p i).threshold b.val ≤ (entry p j).threshold b.val := by decide +kernel

noncomputable def recipe (p : Fin 4) : MinMaxRecipe (Fin 40) (Fin 10007) where
  Adj := Sensitivity10007Labeling.Labeling10007.Adj
  loopless := Sensitivity10007Labeling.Labeling10007.irreflexive
  label v w := decide (Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w) = 1)
  guard l := (entry p l).guard
  tolerance l := (entry p l).tolerance
  lower l b := (entry p l).threshold b
  upper l b := (entry p l).threshold b

theorem recipe_ordered (p : Fin 4) : OrderedRecipe (recipe p) := by
  have hm : ∀ l : Fin 40, Monotone ((entry p l).threshold) := fun l =>
    Entry.threshold_monotone _ (entry_internal_order p l).1
      (entry_internal_order p l).2.1
  have ho : ∀ i j : Fin 40, i ≤ j → ∀ b : ℕ, b ≤ (entry p j).tolerance →
      (entry p i).threshold b ≤ (entry p j).threshold b := by
    intro i j hij b hb
    have hb9 : b < 9 := by have ht := (entry_internal_order p j).2.2; omega
    exact (entry_pair_order p i j hij).2.2 ⟨b,hb9⟩ hb
  exact {
    guard := fun i j hij => (entry_pair_order p i j hij).1
    tolerance := fun i j hij => (entry_pair_order p i j hij).2.1
    lower_mono := hm
    upper_mono := hm
    lower_order := ho
    upper_order := ho }

noncomputable def periodicRecipe (n : ℕ) : MinMaxRecipe (Fin 40) (Fin 10007) :=
  recipe ⟨n % 4, Nat.mod_lt n (by decide)⟩

noncomputable def family (n : ℕ) :
    Fin 40 → (IterProd (Fin 10007 × Bool) n → Bool) → Bool :=
  towerFamily periodicRecipe n



end Sensitivity10007Endpoint40


