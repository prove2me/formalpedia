-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Recipes
-- name    : BS2_b3ba934b_Endpoint16Recipes
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:25:51.972536+00:00
-- url     : https://prove2.me/theorems/9e1b78fb-4704-4aae-bb88-7357184fe4dc
-- title:
--   Sensitivity separation: Endpoint16Recipes (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Recipes` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Recipes.lean; original SHA-256 1f5b06f3fd098caf4a245712bcbdd30ba2d29fd0cb1b025336c3d1da4e3e7857; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual sixteen-level symmetric min/max recipes of the second endpoint. -/
import Definitions.Def_BS2_b3ba934b_MinMaxNesting
import Definitions.Def_BS2_b3ba934b_Selected10007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Sensitivity10007Endpoint16
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting

structure Entry where
  t0 : Fin 16
  t1 : Fin 16
  t2 : Fin 16
  u0 : Fin 16
  u1 : Fin 16
  u2 : Fin 16
  guard : Fin 16
  tolerance : ℕ
  deriving Inhabited

def Entry.threshold (e : Entry) (b : ℕ) : Fin 16 :=
  if 3≤e.tolerance ∨ b=0 then e.t0 else if b=1 then e.t1 else e.t2

def Entry.upper (e : Entry) (b : ℕ) : Fin 16 :=
  if 3≤e.tolerance ∨ b=0 then e.u0 else if b=1 then e.u1 else e.u2

theorem Entry.threshold_monotone (e : Entry) (h01 : e.t0≤e.t1) (h12 : e.t1≤e.t2) :
    Monotone e.threshold := by
  intro a b hab
  unfold threshold
  split_ifs <;> first | exact le_rfl | exact h01 | exact h12 | exact h01.trans h12 | omega

theorem Entry.upper_monotone (e : Entry) (h01 : e.u0≤e.u1) (h12 : e.u1≤e.u2) :
    Monotone e.upper := by
  intro a b hab
  unfold upper
  split_ifs <;> first | exact le_rfl | exact h01 | exact h12 | exact h01.trans h12 | omega

def entries0 : Array Entry := #[
  ⟨7,7,7,7,7,7,6,3⟩,
  ⟨8,8,11,8,11,11,6,2⟩,
  ⟨8,11,11,11,11,11,6,1⟩,
  ⟨9,9,9,11,11,11,6,0⟩,
  ⟨10,10,10,11,11,11,6,0⟩,
  ⟨11,11,11,11,11,11,6,0⟩,
  ⟨13,13,13,13,13,13,6,0⟩,
  ⟨13,13,13,13,13,13,4,0⟩,
  ⟨13,13,13,13,13,13,3,0⟩,
  ⟨14,14,14,14,14,14,3,0⟩,
  ⟨15,15,15,15,15,15,2,0⟩,
  ⟨15,15,15,15,15,15,0,0⟩,
  ⟨15,15,15,15,15,15,0,0⟩,
  ⟨15,15,15,15,15,15,0,0⟩,
  ⟨15,15,15,15,15,15,0,0⟩,
  ⟨15,15,15,15,15,15,0,0⟩
]

def entries1 : Array Entry := #[
  ⟨5,5,5,5,5,5,5,7⟩,
  ⟨5,5,5,5,5,5,5,3⟩,
  ⟨6,6,7,6,7,7,5,2⟩,
  ⟨6,7,7,7,7,7,5,1⟩,
  ⟨6,6,6,7,7,7,5,0⟩,
  ⟨7,7,7,7,7,7,5,0⟩,
  ⟨9,9,9,9,9,9,5,0⟩,
  ⟨9,9,9,9,9,9,4,0⟩,
  ⟨9,9,9,9,9,9,2,0⟩,
  ⟨10,10,10,10,10,10,1,0⟩,
  ⟨11,11,11,11,11,11,1,0⟩,
  ⟨11,11,11,11,11,11,0,0⟩,
  ⟨11,11,11,11,11,11,0,0⟩,
  ⟨11,11,11,11,11,11,0,0⟩,
  ⟨11,11,11,11,11,11,0,0⟩,
  ⟨11,11,11,11,11,11,0,0⟩
]

def entries2 : Array Entry := #[
  ⟨6,6,6,6,6,6,5,4⟩,
  ⟨6,6,6,6,6,6,5,3⟩,
  ⟨6,6,8,6,8,8,5,2⟩,
  ⟨6,8,8,8,8,8,5,1⟩,
  ⟨6,6,6,8,8,8,5,0⟩,
  ⟨7,7,7,8,8,8,5,0⟩,
  ⟨8,8,8,8,8,8,5,0⟩,
  ⟨9,9,9,9,9,9,5,0⟩,
  ⟨9,9,9,9,9,9,4,0⟩,
  ⟨9,9,9,9,9,9,3,0⟩,
  ⟨9,9,9,9,9,9,2,0⟩,
  ⟨10,10,10,10,10,10,2,0⟩,
  ⟨11,11,11,11,11,11,2,0⟩,
  ⟨11,11,11,11,11,11,1,0⟩,
  ⟨11,11,11,11,11,11,1,0⟩,
  ⟨11,11,11,11,11,11,1,0⟩
]

def entries3 : Array Entry := #[
  ⟨7,7,7,7,7,7,6,5⟩,
  ⟨7,7,7,7,7,7,6,4⟩,
  ⟨7,7,7,7,7,7,6,3⟩,
  ⟨7,7,9,7,9,9,6,2⟩,
  ⟨7,9,9,9,9,9,6,1⟩,
  ⟨7,7,7,9,9,9,6,0⟩,
  ⟨9,9,9,9,9,9,6,0⟩,
  ⟨10,10,10,10,10,10,6,0⟩,
  ⟨12,12,12,12,12,12,6,0⟩,
  ⟨12,12,12,12,12,12,5,0⟩,
  ⟨12,12,12,12,12,12,4,0⟩,
  ⟨12,12,12,12,12,12,3,0⟩,
  ⟨13,13,13,13,13,13,3,0⟩,
  ⟨13,13,13,13,13,13,2,0⟩,
  ⟨13,13,13,13,13,13,1,0⟩,
  ⟨13,13,13,13,13,13,0,0⟩
]

def entry (p : Fin 4) (l : Fin 16) : Entry :=
  match p.val with
  | 0 => entries0.getD l.val default
  | 1 => entries1.getD l.val default
  | 2 => entries2.getD l.val default
  | _ => entries3.getD l.val default

theorem entry_internal_order : ∀ p l,
    (entry p l).t0≤(entry p l).t1 ∧ (entry p l).t1≤(entry p l).t2 ∧
    (entry p l).u0≤(entry p l).u1 ∧ (entry p l).u1≤(entry p l).u2 ∧
    (entry p l).tolerance≤8 := by decide +kernel

theorem entry_guard_order : ∀ p l, (entry p l).guard≤(entry p l).t0 ∧
    ∀ b : Fin 9, b.val≤(entry p l).tolerance →
      (entry p l).threshold b.val≤(entry p l).upper b.val := by decide +kernel

theorem entry_pair_order : ∀ (p : Fin 4) (i j : Fin 16), i≤j →
    (entry p j).guard≤(entry p i).guard ∧
    (entry p j).tolerance≤(entry p i).tolerance ∧
    ∀ b : Fin 9, b.val≤(entry p j).tolerance →
      (entry p i).threshold b.val≤(entry p j).threshold b.val ∧
      (entry p i).upper b.val≤(entry p j).upper b.val := by decide +kernel

noncomputable def recipe (p : Fin 4) : MinMaxRecipe (Fin 16) (Fin 10007) where
  Adj := Sensitivity10007Labeling.Labeling10007.Adj
  loopless := Sensitivity10007Labeling.Labeling10007.irreflexive
  label v w := decide (Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w)=1)
  guard l := (entry p l).guard
  tolerance l := (entry p l).tolerance
  lower l b := (entry p l).threshold b
  upper l b := (entry p l).upper b

theorem recipe_ordered (p : Fin 4) : OrderedRecipe (recipe p) := by
  have hl : ∀ l : Fin 16, Monotone ((entry p l).threshold) := fun l =>
    Entry.threshold_monotone _ (entry_internal_order p l).1 (entry_internal_order p l).2.1
  have hu : ∀ l : Fin 16, Monotone ((entry p l).upper) := fun l =>
    Entry.upper_monotone _ (entry_internal_order p l).2.2.1 (entry_internal_order p l).2.2.2.1
  have ho : ∀ i j : Fin 16, i≤j → ∀ b : ℕ, b≤(entry p j).tolerance →
      (entry p i).threshold b≤(entry p j).threshold b ∧
      (entry p i).upper b≤(entry p j).upper b := by
    intro i j hij b hb
    have hb9 : b<9 := by have ht := (entry_internal_order p j).2.2.2.2; omega
    exact (entry_pair_order p i j hij).2.2 ⟨b,hb9⟩ hb
  exact {
    guard := fun i j hij => (entry_pair_order p i j hij).1
    tolerance := fun i j hij => (entry_pair_order p i j hij).2.1
    lower_mono := hl
    upper_mono := hu
    lower_order := fun i j hij b hb => (ho i j hij b hb).1
    upper_order := fun i j hij b hb => (ho i j hij b hb).2 }

noncomputable def periodicRecipe (n : ℕ) : MinMaxRecipe (Fin 16) (Fin 10007) :=
  recipe ⟨n%4,Nat.mod_lt n (by decide)⟩

noncomputable def family (n : ℕ) :
    Fin 16 → (IterProd (Fin 10007 × Bool) n → Bool) → Bool :=
  towerFamily periodicRecipe n

theorem family_nested (n : ℕ) : Nested (family n) :=
  tower_nested periodicRecipe (fun k => recipe_ordered _) n

end Sensitivity10007Endpoint16

#print axioms Sensitivity10007Endpoint16.family_nested


