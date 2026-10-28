-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
-- name    : Sensitivity213981Formal_Endpoint22Recipes
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:42:39.171142+00:00
-- url     : https://prove2.me/theorems/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b
-- title:
--   Endpoint22 Recipes — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Recipes in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Endpoint22.Entry.upper_monotone`, `Sensitivity5591Endpoint22.entries0`, `Sensitivity5591Endpoint22.entries1`, `Sensitivity5591Endpoint22.entries2`, `Sensitivity5591Endpoint22.entries3`, `Sensitivity5591Endpoint22.Entry`, `Sensitivity5591Endpoint22.entry`, `Sensitivity5591Endpoint22.entry_lower_order`, `Sensitivity5591Endpoint22.entry_upper_order`, `Sensitivity5591Endpoint22.entry_tolerance_bound`, `Sensitivity5591Endpoint22.entry_guard_order`, `Sensitivity5591Endpoint22.entry_pair_order`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22Recipes.lean, lines 1–221.

import Definitions.Def_Sensitivity213981Formal_MinMaxNesting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/- Actual third-endpoint recipes, certificate SHA256 c706e403ddef113743f0dacc0a95d97dd3a2f32de032f35972f7ef045be6425f.
The tournament and edge labeling remain explicit parameters until the selected
order-5591 labeling is instantiated. -/


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Sensitivity5591Endpoint22
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting

structure Entry where
  t0 : Fin 22
  t1 : Fin 22
  t2 : Fin 22
  t3 : Fin 22
  u0 : Fin 22
  u1 : Fin 22
  u2 : Fin 22
  u3 : Fin 22
  guard : Fin 22
  tolerance : ℕ
  deriving Inhabited

def Entry.threshold (e : Entry) (b : ℕ) : Fin 22 :=
  if 4≤ e.tolerance ∨ b=0 then e.t0 else if b=1 then e.t1 else if b=2 then e.t2 else e.t3

def Entry.upper (e : Entry) (b : ℕ) : Fin 22 :=
  if 4≤ e.tolerance ∨ b=0 then e.u0 else if b=1 then e.u1 else if b=2 then e.u2 else e.u3

theorem Entry.threshold_monotone (e : Entry) (h01 : e.t0≤ e.t1) (h12 : e.t1≤ e.t2) (h23 : e.t2≤ e.t3) :
    Monotone e.threshold := by
  intro a b hab
  unfold threshold
  split_ifs <;> first | exact le_rfl | exact h01 | exact h12 | exact h23 |
    exact h01.trans h12 | exact h12.trans h23 | exact h01.trans (h12.trans h23) | omega

theorem Entry.upper_monotone (e : Entry) (h01 : e.u0≤ e.u1) (h12 : e.u1≤ e.u2) (h23 : e.u2≤ e.u3) :
    Monotone e.upper := by
  intro a b hab
  unfold upper
  split_ifs <;> first | exact le_rfl | exact h01 | exact h12 | exact h23 |
    exact h01.trans h12 | exact h12.trans h23 | exact h01.trans (h12.trans h23) | omega

def entries0 : Array Entry := #[
  ⟨6,6,6,6,6,6,6,6,6,5⟩,
  ⟨6,6,6,6,6,6,6,6,6,4⟩,
  ⟨6,6,7,8,6,6,8,8,6,3⟩,
  ⟨6,6,7,8,6,6,8,9,6,3⟩,
  ⟨6,6,8,8,6,6,8,8,6,2⟩,
  ⟨7,7,8,8,7,8,8,8,6,2⟩,
  ⟨7,7,7,7,7,8,8,8,6,1⟩,
  ⟨7,7,7,7,8,8,8,8,6,1⟩,
  ⟨7,8,8,8,8,8,8,8,6,1⟩,
  ⟨7,7,7,7,8,8,8,8,6,0⟩,
  ⟨8,8,8,8,8,8,8,8,6,0⟩,
  ⟨8,8,8,8,11,11,11,11,6,0⟩,
  ⟨8,8,8,8,13,13,13,13,6,0⟩,
  ⟨13,13,13,13,13,13,13,13,4,0⟩,
  ⟨13,13,13,13,14,14,14,14,3,0⟩,
  ⟨15,15,15,15,15,15,15,15,3,0⟩,
  ⟨16,16,16,16,16,16,16,16,2,0⟩,
  ⟨16,16,16,16,16,16,16,16,1,0⟩,
  ⟨16,16,16,16,16,16,16,16,0,0⟩,
  ⟨16,16,16,16,16,16,16,16,0,0⟩,
  ⟨16,16,16,16,16,16,16,16,0,0⟩,
  ⟨16,16,16,16,16,16,16,16,0,0⟩
]

def entries1 : Array Entry := #[
  ⟨11,11,11,11,11,11,11,11,10,7⟩,
  ⟨12,12,12,12,12,12,12,12,10,4⟩,
  ⟨12,12,12,12,12,12,12,12,10,3⟩,
  ⟨12,12,12,13,12,12,12,13,10,3⟩,
  ⟨12,12,12,13,12,12,13,13,10,3⟩,
  ⟨12,12,13,13,12,13,13,13,10,3⟩,
  ⟨12,12,13,13,12,13,13,14,10,3⟩,
  ⟨12,12,13,13,12,13,13,13,10,2⟩,
  ⟨12,13,13,13,13,13,13,13,10,1⟩,
  ⟨12,13,13,13,13,14,14,14,10,1⟩,
  ⟨12,12,12,12,13,13,13,13,10,0⟩,
  ⟨13,13,13,13,13,13,13,13,10,0⟩,
  ⟨13,13,13,13,15,15,15,15,10,0⟩,
  ⟨15,15,15,15,15,15,15,15,8,0⟩,
  ⟨16,16,16,16,16,16,16,16,5,0⟩,
  ⟨16,16,16,16,17,17,17,17,2,0⟩,
  ⟨17,17,17,17,17,17,17,17,2,0⟩,
  ⟨18,18,18,18,18,18,18,18,1,0⟩,
  ⟨18,18,18,18,18,18,18,18,0,0⟩,
  ⟨18,18,18,18,18,18,18,18,0,0⟩,
  ⟨18,18,18,18,18,18,18,18,0,0⟩,
  ⟨18,18,18,18,18,18,18,18,0,0⟩
]

def entries2 : Array Entry := #[
  ⟨12,12,12,13,12,12,13,13,11,3⟩,
  ⟨12,12,12,13,12,12,13,14,11,3⟩,
  ⟨12,12,13,13,12,12,13,14,11,3⟩,
  ⟨12,12,13,13,12,12,13,15,11,3⟩,
  ⟨12,12,13,13,12,13,13,15,11,3⟩,
  ⟨12,12,13,13,12,13,13,17,11,3⟩,
  ⟨12,12,13,13,12,13,13,13,11,2⟩,
  ⟨12,12,14,14,12,13,14,14,11,2⟩,
  ⟨12,12,15,15,13,13,15,15,11,2⟩,
  ⟨12,12,15,15,13,13,16,16,11,2⟩,
  ⟨12,13,16,16,13,13,16,16,11,2⟩,
  ⟨12,13,13,13,13,13,13,13,11,1⟩,
  ⟨12,12,12,12,13,13,13,13,11,0⟩,
  ⟨13,13,13,13,13,13,13,13,11,0⟩,
  ⟨13,13,13,13,14,14,14,14,11,0⟩,
  ⟨14,14,14,14,14,14,14,14,8,0⟩,
  ⟨16,16,16,16,16,16,16,16,7,0⟩,
  ⟨16,16,16,16,17,17,17,17,7,0⟩,
  ⟨17,17,17,17,17,17,17,17,4,0⟩,
  ⟨17,17,17,17,17,17,17,17,2,0⟩,
  ⟨18,18,18,18,18,18,18,18,1,0⟩,
  ⟨18,18,18,18,18,18,18,18,0,0⟩
]

def entries3 : Array Entry := #[
  ⟨14,14,14,14,14,14,14,14,14,6⟩,
  ⟨14,14,14,14,14,14,14,14,13,4⟩,
  ⟨14,14,14,15,14,14,15,15,13,3⟩,
  ⟨14,14,15,15,14,15,15,15,13,2⟩,
  ⟨14,15,15,15,15,15,15,15,13,1⟩,
  ⟨15,15,15,15,15,16,16,16,13,1⟩,
  ⟨15,15,15,15,15,15,15,15,13,0⟩,
  ⟨15,15,15,15,16,16,16,16,13,0⟩,
  ⟨16,16,16,16,16,16,16,16,11,0⟩,
  ⟨17,17,17,17,17,17,17,17,11,0⟩,
  ⟨17,17,17,17,18,18,18,18,11,0⟩,
  ⟨17,17,17,17,18,18,18,18,9,0⟩,
  ⟨18,18,18,18,18,18,18,18,7,0⟩,
  ⟨18,18,18,18,18,18,18,18,6,0⟩,
  ⟨19,19,19,19,20,20,20,20,0,0⟩,
  ⟨20,20,20,20,20,20,20,20,0,0⟩,
  ⟨21,21,21,21,21,21,21,21,0,0⟩,
  ⟨21,21,21,21,21,21,21,21,0,0⟩,
  ⟨21,21,21,21,21,21,21,21,0,0⟩,
  ⟨21,21,21,21,21,21,21,21,0,0⟩,
  ⟨21,21,21,21,21,21,21,21,0,0⟩,
  ⟨21,21,21,21,21,21,21,21,0,0⟩
]

def entry (p : Fin 4) (l : Fin 22) : Entry :=
  match p.val with
  | 0 => entries0.getD l.val default
  | 1 => entries1.getD l.val default
  | 2 => entries2.getD l.val default
  | _ => entries3.getD l.val default

theorem entry_lower_order : ∀ p l,
    (entry p l).t0≤ (entry p l).t1 ∧ (entry p l).t1≤ (entry p l).t2 ∧
    (entry p l).t2≤ (entry p l).t3 := by decide +kernel

theorem entry_upper_order : ∀ p l,
    (entry p l).u0≤ (entry p l).u1 ∧ (entry p l).u1≤ (entry p l).u2 ∧
    (entry p l).u2≤ (entry p l).u3 := by decide +kernel

theorem entry_tolerance_bound : ∀ p l, (entry p l).tolerance≤ 8 := by decide +kernel

theorem entry_guard_order : ∀ p l, (entry p l).guard≤ (entry p l).t0 ∧
    ∀ b : Fin 9, b.val≤ (entry p l).tolerance →
      (entry p l).threshold b.val≤ (entry p l).upper b.val := by decide +kernel

theorem entry_pair_order : ∀ (p : Fin 4) (i j : Fin 22), i≤ j →
    (entry p j).guard≤ (entry p i).guard ∧
    (entry p j).tolerance≤ (entry p i).tolerance ∧
    ∀ b : Fin 9, b.val≤ (entry p j).tolerance →
      (entry p i).threshold b.val≤ (entry p j).threshold b.val ∧
      (entry p i).upper b.val≤ (entry p j).upper b.val := by decide +kernel

noncomputable def recipe (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool) (p : Fin 4) : MinMaxRecipe (Fin 22) (Fin 5591) where
  Adj := Adj
  loopless := loopless
  label := label
  guard l := (entry p l).guard
  tolerance l := (entry p l).tolerance
  lower l b := (entry p l).threshold b
  upper l b := (entry p l).upper b

theorem recipe_ordered (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool) (p : Fin 4) : OrderedRecipe (recipe Adj loopless label p) := by
  have hl : ∀ l : Fin 22, Monotone ((entry p l).threshold) := fun l =>
    Entry.threshold_monotone _ (entry_lower_order p l).1 (entry_lower_order p l).2.1 (entry_lower_order p l).2.2
  have hu : ∀ l : Fin 22, Monotone ((entry p l).upper) := fun l =>
    Entry.upper_monotone _ (entry_upper_order p l).1 (entry_upper_order p l).2.1 (entry_upper_order p l).2.2
  have ho : ∀ i j : Fin 22, i≤ j → ∀ b : ℕ, b≤ (entry p j).tolerance →
      (entry p i).threshold b≤ (entry p j).threshold b ∧
      (entry p i).upper b≤ (entry p j).upper b := by
    intro i j hij b hb
    have hb9 : b< 9 := by have ht := entry_tolerance_bound p j; omega
    exact (entry_pair_order p i j hij).2.2 ⟨b,hb9⟩ hb
  exact {
    guard := fun i j hij => (entry_pair_order p i j hij).1
    tolerance := fun i j hij => (entry_pair_order p i j hij).2.1
    lower_mono := hl
    upper_mono := hu
    lower_order := fun i j hij b hb => (ho i j hij b hb).1
    upper_order := fun i j hij b hb => (ho i j hij b hb).2 }

noncomputable def periodicRecipe (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool) (n : ℕ) : MinMaxRecipe (Fin 22) (Fin 5591) :=
  recipe Adj loopless label ⟨n%4,Nat.mod_lt n (by decide)⟩

noncomputable def family (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool) (n : ℕ) :
    Fin 22 → (IterProd (Fin 5591 × Bool) n → Bool) → Bool :=
  towerFamily (periodicRecipe Adj loopless label) n



end Sensitivity5591Endpoint22




end
end Sensitivity213981Formal


