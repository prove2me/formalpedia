-- Prove2me | Definitions.Def_OAIThreeMachineSched01
-- name    : OAIThreeMachineSched01
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T06:27:32.58429+00:00
-- url     : https://prove2.me/theorems/1c7ab402-a2ac-4208-be79-33fa1a7ecd10
-- title:
--   Scheduling algorithm, machine models and routine compiler for three-machine scheduling
-- statement:
--   This block collects the supporting declarations of the stack compiler used to prove `OAI.ThreeMachine.main_theorem`, part 1 of 2, in upstream module order.
--
--   Contents: the partial order and formula structures, padding, the effective description family and the dynamic program (`Algorithm`), the stack and tree machine models, the register-program compiler, realizers and uniform routines, and the first routine families.
--
--   **Formalization Note** Declarations are reproduced from upstream `lean/OAI/Computability/Scheduling/` (openai/math, Apache-2.0, credit OpenAI), together with short lemmas their bodies and instances need, on Lean 4.33. Metaprograms are excluded. Where an upstream proof called the tactic `poly_auto`, the explicit rule applications recorded from that tactic appear instead.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/

import Mathlib
import Definitions.Def_ThreeMachine

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

section
-- module Compat
namespace OAI

-- Lean 4.33.1 equivalents of four core theorem names introduced in Lean 4.34.
theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

end OAI
end


section
-- module SeparatorWalk
namespace OAI

section

namespace ThreeMachine
namespace Structure

abbrev Layout (J : Type) [Fintype J] := J ≃ Fin (Fintype.card J)

def Layout.time {J : Type} [Fintype J] (p : Layout J) (x : J) : ℕ :=
  (p x).val / 3 + 1

def Layout.Respects {J : Type} [Fintype J] (p : Layout J)
    (r : J → J → Prop) : Prop :=
  ∀ x y, r x y → p.time x < p.time y

def Layout.Full {J : Type} [Fintype J] (p : Layout J)
    (r : J → J → Prop) : Prop :=
  3 ∣ Fintype.card J ∧ p.Respects r

def Layout.signature {J : Type} [Fintype J] (p : Layout J)
    (priority : J → ℕ) : List ℕ :=
  List.ofFn (fun i => priority (p.symm i))

def Layout.exchange {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y : J) : Layout J :=
  (Equiv.swap x y).trans p

@[simp] theorem exchange_time_left {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y : J) : (p.exchange x y).time x = p.time y := by
  simp [Layout.time, Layout.exchange]

@[simp] theorem exchange_time_right {J : Type} [Fintype J] [DecidableEq J]
    (p : Layout J) (x y : J) : (p.exchange x y).time y = p.time x := by
  simp [Layout.time, Layout.exchange]

end Structure
end ThreeMachine

namespace ThreeMachine.Structure

section Walk
variable {J : Type}

def PredAt (r : J → J → Prop) (time : J → ℕ) (s : ℕ) : Set J :=
  {x | ∃ y, time y = s ∧ r x y}

def DescAt (r : J → J → Prop) (time : J → ℕ) (s : ℕ) : Set J :=
  {x | ∃ y, time y = s ∧ r y x}

def IdealOn (W : Finset J) (r : J → J → Prop) (S : Set J) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, r x y → y ∈ S → x ∈ S

def PrefixOn (W : Finset J) (priority : J → ℕ) (S : Set J) : Prop :=
  ∀ x ∈ W, x ∈ S → ∀ y ∈ W, y ∉ S → priority x < priority y

def EarlierHigh (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) : Prop :=
  ∀ x ∈ W, time x < s → x ∉ S → x ∈ PredAt r time s

def LaterLow (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) : Prop :=
  ∀ x ∈ W, s < time x → x ∈ S → x ∈ DescAt r time s

def Separator (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) : Prop :=
  EarlierHigh W r time S s ∧ LaterLow W r time S s

def SlotClosed (W : Finset J) (time : J → ℕ) : Prop :=
  ∀ x ∈ W, ∀ y, time y = time x → y ∈ W

def AdmissiblePosition (W : Finset J) (time : J → ℕ) (s : ℕ) : Prop :=
  (∃ x ∈ W, time x = s) ∨ (∀ x ∈ W, s < time x)

def LocalObstruction (W : Finset J) (r : J → J → Prop)
    (time priority : J → ℕ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, time y < time x → priority x < priority y →
    (∀ u ∈ W, r u x → time u < time y) →
    ∃ v ∈ W, r y v ∧ time v ≤ time x

structure Exception (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) (s : ℕ) (x : J) : Prop where
  mem : x ∈ W
  low : x ∈ S
  later : s < time x
  not_desc : x ∉ DescAt r time s
  earliest : ∀ y ∈ W, y ∈ S → s < time y → time y < time x →
    y ∈ DescAt r time s

end Walk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SharedWalk
variable {J : Type}

inductive AdvancePath (W : Finset J) (r : J → J → Prop) (time : J → ℕ)
    (S : Set J) : ℕ → ℕ → Prop
  | refl (s) : AdvancePath W r time S s s
  | step {s t x} : AdvancePath W r time S s t →
      Exception W r time S t x → AdvancePath W r time S s (time x)

end SharedWalk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IdealSeparator
variable {J : Type}

end IdealSeparator
end ThreeMachine.Structure

end

end OAI
end


section
-- module GlobalBoundaries
namespace OAI

section

namespace ThreeMachine.Structure

def GlobalUpset {J : Type} (r : J → J → Prop) (A : Set J) : Prop :=
  ∀ ⦃x y⦄, r x y → x ∈ A → y ∈ A

def GlobalDownset {J : Type} (r : J → J → Prop) (A : Set J) : Prop :=
  ∀ ⦃x y⦄, r x y → y ∈ A → x ∈ A

structure GlobalList (J : Type) where
  indices : Finset ℕ
  entry : ℕ → Set J

namespace GlobalList
variable {J : Type}

def Qual (K : GlobalList J) : Set J := {x | ∃ i ∈ K.indices, x ∈ K.entry i}

def Upsets (K : GlobalList J) (r : J → J → Prop) : Prop :=
  ∀ i ∈ K.indices, GlobalUpset r (K.entry i)

noncomputable def memberships (K : GlobalList J) (x : J) : Finset ℕ := by
  classical
  exact K.indices.filter (fun i => x ∈ K.entry i)

noncomputable def lastIndex (K : GlobalList J) (x : J) : ℕ :=
  (K.memberships x).sup id

def KeyLT (K : GlobalList J) (rank : J → ℕ) (x y : J) : Prop :=
  K.lastIndex x < K.lastIndex y ∨
    K.lastIndex x = K.lastIndex y ∧ rank x < rank y

@[simp] theorem mem_memberships (K : GlobalList J) (x : J) (i : ℕ) :
    i ∈ K.memberships x ↔ i ∈ K.indices ∧ x ∈ K.entry i := by
  classical
  simp [memberships]

theorem le_lastIndex {K : GlobalList J} {x : J} {i : ℕ}
    (hi : i ∈ K.indices) (hx : x ∈ K.entry i) : i ≤ K.lastIndex x := by
  exact Finset.le_sup (f := id) ((mem_memberships K x i).mpr ⟨hi, hx⟩)

noncomputable def carry (K : GlobalList J) (rank : J → ℕ) (d r : ℕ) : GlobalList J := by
  classical
  exact ⟨K.indices.filter (d ≤ ·), fun i =>
    if i = d then K.entry i ∩ {x | r ≤ rank x} else K.entry i⟩

noncomputable def prune (K : GlobalList J) (W : Set J) : GlobalList J := by
  classical
  exact ⟨K.indices.filter (fun i => (K.entry i ∩ W).Nonempty), K.entry⟩

theorem prune_membership (K : GlobalList J) (W : Set J) (i : ℕ) (x : J) :
    i ∈ (K.prune W).memberships x ↔
      i ∈ K.indices ∧ (K.entry i ∩ W).Nonempty ∧ x ∈ K.entry i := by
  classical
  rw [mem_memberships]
  change (i ∈ K.indices.filter (fun j => (K.entry j ∩ W).Nonempty) ∧
    x ∈ K.entry i) ↔ _
  rw [Finset.mem_filter]
  exact and_assoc

theorem prune_qual_subset (K : GlobalList J) (W : Set J) : (K.prune W).Qual ⊆ K.Qual := by
  rintro x ⟨i, hi, hx⟩
  have hm := (prune_membership K W i x).mp ((mem_memberships _ _ _).mpr ⟨hi, hx⟩)
  exact ⟨i, hm.1, hm.2.2⟩

theorem prune_qual (K : GlobalList J) {W : Set J} {x : J} (hx : x ∈ W) :
    x ∈ (K.prune W).Qual ↔ x ∈ K.Qual := by
  refine ⟨fun h => prune_qual_subset K W h, ?_⟩
  rintro ⟨i, hi, hxi⟩
  refine ⟨i, ?_⟩
  apply (mem_memberships _ _ _).mp
  exact (prune_membership K W i x).mpr ⟨hi, ⟨x, hxi, hx⟩, hxi⟩

theorem prune_lastIndex_le (K : GlobalList J) (W : Set J) (x : J) :
    (K.prune W).lastIndex x ≤ K.lastIndex x := by
  apply Finset.sup_le
  intro i hi
  have hm := (prune_membership K W i x).mp hi
  exact le_lastIndex hm.1 hm.2.2

theorem prune_lastIndex (K : GlobalList J) {W : Set J} {x : J} (hx : x ∈ W) :
    (K.prune W).lastIndex x = K.lastIndex x := by
  apply le_antisymm (prune_lastIndex_le K W x)
  apply Finset.sup_le
  intro i hi
  have hm := (mem_memberships K x i).mp hi
  apply Finset.le_sup (f := id)
  exact (prune_membership K W i x).mpr ⟨hm.1, ⟨x, hm.2, hx⟩, hm.2⟩

theorem prune_key {K : GlobalList J} {W : Set J} {rank : J → ℕ} {x y : J}
    (hx : x ∈ W) (hkey : (K.prune W).KeyLT rank x y) : K.KeyLT rank x y := by
  have heq := prune_lastIndex K hx
  have hle := prune_lastIndex_le K W y
  rcases hkey with h | ⟨h, hr⟩
  · exact Or.inl (by omega)
  · by_cases hlt : K.lastIndex x < K.lastIndex y
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, hr⟩

theorem prune_upsets {K : GlobalList J} {W : Set J} {r : J → J → Prop}
    (hK : K.Upsets r) : (K.prune W).Upsets r := by
  classical
  intro i hi
  have hi' : i ∈ K.indices ∧ (K.entry i ∩ W).Nonempty := by simpa [prune] using hi
  exact hK i hi'.1

end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IntervalNormalization
variable {J : Type} [Fintype J]

def Layout.FixedOutside (p q : Layout J) (W : Set J) : Prop :=
  ∀ x, x ∉ W → q x = p x

theorem Layout.FixedOutside.trans {p q u : Layout J} {W : Set J}
    (hpq : p.FixedOutside q W) (hqu : q.FixedOutside u W) : p.FixedOutside u W :=
  fun x hx => (hqu x hx).trans (hpq x hx)

theorem Layout.FixedOutside.time {p q : Layout J} {W : Set J}
    (h : p.FixedOutside q W) {x : J} (hx : x ∉ W) : q.time x = p.time x := by
  simp [Layout.time, h x hx]

theorem Layout.FixedOutside.position_mem {p q : Layout J} {W : Set J}
    (h : p.FixedOutside q W) {x : J} (hx : x ∈ W) : p.symm (q x) ∈ W := by
  by_contra hn
  have he : q (p.symm (q x)) = q x := by rw [h _ hn, p.apply_symm_apply]
  apply hn
  rw [q.injective he]
  exact hx

theorem Layout.FixedOutside.time_range {p q : Layout J} {W : Set J} {a b : ℕ}
    (h : p.FixedOutside q W) (hW : ∀ x ∈ W, a < p.time x ∧ p.time x < b)
    {x : J} (hx : x ∈ W) : a < q.time x ∧ q.time x < b := by
  have hr := hW _ (h.position_mem hx)
  simpa [Layout.time] using hr

def Layout.NormalizedOn (p : Layout J) (W : Set J)
    (r : J → J → Prop) (priority : J → ℕ) : Prop :=
  p.Respects r ∧ ∀ q : Layout J, q.Respects r → p.FixedOutside q W →
    p.signature priority ≤ q.signature priority

end IntervalNormalization
end ThreeMachine.Structure

namespace ThreeMachine.Structure

abbrev Triple (J : Type) := {Z : Finset J // Z.card = 3}

inductive Boundary (J : Type)
  | left
  | actual (Z : Triple J)
  | right

namespace Boundary
variable {J : Type}

def pred (r : J → J → Prop) : Boundary J → Set J
  | .left => ∅
  | .actual Z => {x | ∃ y ∈ Z.val, r x y}
  | .right => Set.univ

def desc (r : J → J → Prop) : Boundary J → Set J
  | .left => Set.univ
  | .actual Z => {x | ∃ y ∈ Z.val, r y x}
  | .right => ∅

def weakPred (r : J → J → Prop) : Boundary J → Set J
  | .left => ∅
  | .actual Z => pred r (.actual Z) ∪ (Z.val : Set J)
  | .right => Set.univ

def weakDesc (r : J → J → Prop) : Boundary J → Set J
  | .left => Set.univ
  | .actual Z => desc r (.actual Z) ∪ (Z.val : Set J)
  | .right => ∅

def reverse : Boundary J → Boundary J
  | .left => .right
  | .actual Z => .actual Z
  | .right => .left

@[simp] theorem reverse_reverse (B : Boundary J) : B.reverse.reverse = B := by cases B <;> rfl

@[simp] theorem pred_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.pred (fun x y => r y x) = B.desc r := by cases B <;> rfl

@[simp] theorem desc_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.desc (fun x y => r y x) = B.pred r := by cases B <;> rfl

@[simp] theorem weakPred_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.weakPred (fun x y => r y x) = B.weakDesc r := by cases B <;> rfl

@[simp] theorem weakDesc_reverse (r : J → J → Prop) (B : Boundary J) :
    B.reverse.weakDesc (fun x y => r y x) = B.weakPred r := by cases B <;> rfl

theorem pred_downset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalDownset r (B.pred r) := by
  intro x y hxy hy
  cases B with
  | left => exact hy.elim
  | right => trivial
  | actual Z =>
      obtain ⟨z, hz, hyz⟩ := hy
      exact ⟨z, hz, htrans hxy hyz⟩

theorem desc_upset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalUpset r (B.desc r) := by
  intro x y hxy hx
  cases B with
  | left => trivial
  | right => exact hx.elim
  | actual Z =>
      obtain ⟨z, hz, hzx⟩ := hx
      exact ⟨z, hz, htrans hzx hxy⟩

theorem weakDesc_upset {r : J → J → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (B : Boundary J) :
    GlobalUpset r (B.weakDesc r) := by
  intro x y hxy hx
  cases B with
  | left => trivial
  | right => exact hx.elim
  | actual Z =>
      rcases hx with h | h
      · exact Or.inl (desc_upset htrans (.actual Z) hxy h)
      · exact Or.inl ⟨x, h, hxy⟩

def At (time : J → ℕ) (T : ℕ) : Boundary J → ℕ → Prop
  | .left, s => s = 0
  | .actual Z, s => 1 ≤ s ∧ s ≤ T ∧ ∀ x, x ∈ Z.val ↔ time x = s
  | .right, s => s = T + 1

theorem pred_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.pred r) : time x < s := by
  cases B with
  | left => exact hx.elim
  | right => have := (hbound x).2; dsimp [At] at hB; omega
  | actual Z =>
      obtain ⟨y, hy, hxy⟩ := hx
      have he := (hB.2.2 y).mp hy
      have := hrespect x y hxy
      omega

theorem desc_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.desc r) : s < time x := by
  cases B with
  | left => have := (hbound x).1; dsimp [At] at hB; omega
  | right => exact hx.elim
  | actual Z =>
      obtain ⟨y, hy, hyx⟩ := hx
      have he := (hB.2.2 y).mp hy
      have := hrespect y x hyx
      omega

theorem weakPred_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.weakPred r) : time x ≤ s := by
  cases B with
  | left => exact hx.elim
  | right => have := (hbound x).2; dsimp [At] at hB; omega
  | actual Z =>
      rcases hx with h | h
      · exact (pred_time hrespect hbound hB h).le
      · exact ((hB.2.2 x).mp h).le

theorem weakDesc_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : x ∈ B.weakDesc r) : s ≤ time x := by
  cases B with
  | left => dsimp [At] at hB; omega
  | right => exact hx.elim
  | actual Z =>
      rcases hx with h | h
      · exact (desc_time hrespect hbound hB h).le
      · exact ((hB.2.2 x).mp h).ge

theorem mem_weak_at_time {r : J → J → Prop} {time : J → ℕ} {T s : ℕ} {B : Boundary J}
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    {x : J} (hx : time x = s) : x ∈ B.weakPred r ∧ x ∈ B.weakDesc r := by
  cases B with
  | left => have := (hbound x).1; dsimp [At] at hB; omega
  | right => have := (hbound x).2; dsimp [At] at hB; omega
  | actual Z => exact ⟨Or.inr ((hB.2.2 x).mpr hx), Or.inr ((hB.2.2 x).mpr hx)⟩

end Boundary

inductive Formula (A : Type)
  | leaf (atom : A) (negative : Bool)
  | conj (p q : Formula A)
  | disj (p q : Formula A)

namespace Formula
variable {A J : Type}

def leaves : Formula A → ℕ
  | .leaf _ _ => 1
  | .conj p q | .disj p q => p.leaves + q.leaves

def eval (atoms : A → Set J) : Formula A → Set J
  | .leaf a false => atoms a
  | .leaf a true => (atoms a)ᶜ
  | .conj p q => p.eval atoms ∩ q.eval atoms
  | .disj p q => p.eval atoms ∪ q.eval atoms

def negate : Formula A → Formula A
  | .leaf a b => .leaf a (!b)
  | .conj p q => .disj p.negate q.negate
  | .disj p q => .conj p.negate q.negate

@[simp] theorem leaves_negate (p : Formula A) : p.negate.leaves = p.leaves := by
  induction p with
  | leaf a b => cases b <;> rfl
  | conj p q hp hq | disj p q hp hq => simp [negate, leaves, hp, hq]

@[simp] theorem eval_negate (atoms : A → Set J) (p : Formula A) :
    p.negate.eval atoms = (p.eval atoms)ᶜ := by
  induction p with
  | leaf a b => cases b <;> simp [negate, eval]
  | conj p q hp hq =>
      ext x
      simp only [negate, eval, hp, hq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
      tauto
  | disj p q hp hq => simp [negate, eval, hp, hq]

end Formula

def Described {A J : Type} (atoms : A → Set J) (W : Set J) (k : ℕ) : Prop :=
  ∃ p : Formula A, p.eval atoms = W ∧ p.leaves ≤ k

namespace Described
variable {A J : Type} {atoms : A → Set J} {W U : Set J} {k l : ℕ}

theorem mono (h : Described atoms W k) (hkl : k ≤ l) : Described atoms W l := by
  obtain ⟨p, hp, hk⟩ := h
  exact ⟨p, hp, hk.trans hkl⟩

theorem compl (h : Described atoms W k) : Described atoms Wᶜ k := by
  obtain ⟨p, hp, hk⟩ := h
  exact ⟨p.negate, by simp [hp], by simpa using hk⟩

theorem inter (hW : Described atoms W k) (hU : Described atoms U l) :
    Described atoms (W ∩ U) (k + l) := by
  obtain ⟨p, hp, hk⟩ := hW
  obtain ⟨q, hq, hl⟩ := hU
  exact ⟨.conj p q, by simp [Formula.eval, hp, hq], Nat.add_le_add hk hl⟩

theorem union (hW : Described atoms W k) (hU : Described atoms U l) :
    Described atoms (W ∪ U) (k + l) := by
  obtain ⟨p, hp, hk⟩ := hW
  obtain ⟨q, hq, hl⟩ := hU
  exact ⟨.disj p q, by simp [Formula.eval, hp, hq], Nat.add_le_add hk hl⟩

theorem diff (hW : Described atoms W k) (hU : Described atoms U l) :
    Described atoms (W \ U) (k + l) := hW.inter hU.compl

theorem finite_union {ι : Type} (s : Finset ι) (E : ι → Set J) (b : ι → ℕ)
    (hne : s.Nonempty) (hE : ∀ i ∈ s, Described atoms (E i) (b i)) :
    Described atoms {x | ∃ i ∈ s, x ∈ E i} (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | @insert i s hi ih =>
      by_cases hs : s.Nonempty
      · have hrest := ih hs (fun j hj => hE j (Finset.mem_insert_of_mem hj))
        have hfirst := hE i (Finset.mem_insert_self _ _)
        have he : {x | ∃ j ∈ insert i s, x ∈ E j} = E i ∪ {x | ∃ j ∈ s, x ∈ E j} := by
          ext x
          simp only [Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union]
          aesop
        rw [he, Finset.sum_insert hi]
        exact hfirst.union hrest
      · have es : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simpa using hE i (Finset.mem_insert_self i ∅)

end Described
end ThreeMachine.Structure

end

end OAI
end


section
-- module CutoffSimplification
namespace OAI

section

namespace ThreeMachine.Structure
namespace GlobalList
variable {J : Type}

noncomputable def append (K : GlobalList J) (A : Set J) : GlobalList J := by
  classical
  exact ⟨insert (max 1 (K.indices.sup id) + 1) K.indices,
    fun i => if i = max 1 (K.indices.sup id) + 1 then A else K.entry i⟩

def nextIndex (K : GlobalList J) : ℕ := max 1 (K.indices.sup id) + 1

theorem injection_card_bound {K : GlobalList J} {r : J → J → Prop}
    {W W' : Set J} {B : Finset J} {I : Finset ℕ}
    (hI : I ⊆ K.indices) (hK : K.Upsets r)
    (hB : (B : Set J) ⊆ W)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ x ∈ W, x ∈ K.entry i → x ∉ K.entry j)
    (hmeet : ∀ i ∈ I, (K.entry i ∩ W').Nonempty)
    (hpred : ∀ x ∈ W', x ∈ K.Qual → ∃ z ∈ B, r x z) : I.card ≤ B.card := by
  classical
  have hex : ∀ i ∈ I, ∃ z ∈ B, z ∈ K.entry i := by
    intro i hi
    obtain ⟨x, hxi, hxW⟩ := hmeet i hi
    obtain ⟨z, hz, hxz⟩ := hpred x hxW ⟨i, hI hi, hxi⟩
    exact ⟨z, hz, hK i (hI hi) hxz hxi⟩
  let f : ↥I → ↥B := fun i =>
    ⟨Classical.choose (hex i.val i.property), (Classical.choose_spec (hex i.val i.property)).1⟩
  have hf : ∀ i : ↥I, (f i).val ∈ K.entry i.val := fun i =>
    (Classical.choose_spec (hex i.val i.property)).2
  have hinj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    have e : (f i).val = (f j).val := congrArg Subtype.val he
    exact hdisj i.val i.property j.val j.property hne (f i).val
      (hB (f i).property) (hf i) (e ▸ hf j)
  simpa using Fintype.card_le_of_injective f hinj

end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
variable {J : Type}

def Window (time : J → ℕ) (a b : ℕ) : Set J := {x | a < time x ∧ time x < b}

namespace Boundary

theorem desc_subset_weakDesc (r : J → J → Prop) (B : Boundary J) :
    B.desc r ⊆ B.weakDesc r := by
  cases B with
  | left => exact Set.Subset.rfl
  | right => exact Set.Subset.rfl
  | actual Z => exact Set.subset_union_left

def Separates (B : Boundary J) (r : J → J → Prop) (time : J → ℕ)
    (W S : Set J) (s : ℕ) : Prop :=
  (∀ x ∈ W, time x < s → x ∉ S → x ∈ B.pred r) ∧
  (∀ x ∈ W, s < time x → x ∈ S → x ∈ B.desc r)

def before (B : Boundary J) (r : J → J → Prop) (H : Set J) : Set J :=
  B.pred r ∪ (H \ B.weakDesc r)

theorem separates_description {r : J → J → Prop} {time : J → ℕ} {T s : ℕ}
    {B : Boundary J} {W S H : Set J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T) (hB : B.At time T s)
    (hsep : B.Separates r time W S s) (hagree : ∀ x ∈ W, x ∈ H ↔ x ∈ S) :
    ∀ x ∈ W, x ∈ B.before r H ↔ time x < s := by
  intro x hx
  constructor
  · rintro (hP | ⟨hH, hnD⟩)
    · exact pred_time hrespect hbound hB hP
    · have hS := (hagree x hx).mp hH
      by_contra hn
      have hle : s ≤ time x := by omega
      rcases hle.eq_or_lt with he | hl
      · exact hnD (mem_weak_at_time hbound hB he.symm).2
      · exact hnD (desc_subset_weakDesc r B (hsep.2 x hx hl hS))
  · intro hlt
    by_cases hS : x ∈ S
    · refine Or.inr ⟨(hagree x hx).mpr hS, ?_⟩
      intro hD
      have := weakDesc_time hrespect hbound hB hD
      omega
    · exact Or.inl (hsep.1 x hx hlt hS)

end Boundary

def PastInvariant (r : J → J → Prop) (time : J → ℕ)
    (K : GlobalList J) (A : Boundary J) (a : ℕ) : Prop :=
  ∀ x ∈ K.Qual, time x ≤ a → x ∈ A.weakPred r

theorem past_prune {r : J → J → Prop} {time : J → ℕ}
    {K : GlobalList J} {A : Boundary J} {a : ℕ} {W : Set J}
    (h : PastInvariant r time K A a) : PastInvariant r time (K.prune W) A a := by
  intro x hx ht
  exact h x (K.prune_qual_subset W hx) ht

theorem global_high_identity {r : J → J → Prop} {time : J → ℕ} {T a b : ℕ}
    {A B : Boundary J} {K : GlobalList J} {S : Set J}
    (hrespect : ∀ u v, r u v → time u < time v)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hA : A.At time T a) (hB : B.At time T b)
    (hlabels : ∀ x ∈ Window time a b, x ∈ K.Qual ↔ x ∉ S)
    (hhigh : ∀ x ∈ Window time a b, x ∉ S → x ∈ B.pred r)
    (hpast : PastInvariant r time K A a) :
    Window time a b \ S = K.Qual ∩ B.pred r ∩ (A.weakPred r)ᶜ := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    refine ⟨⟨(hlabels x hx).mpr hS, hhigh x hx hS⟩, ?_⟩
    intro hbad
    have ht := A.weakPred_time hrespect hbound hA hbad
    exact (not_le_of_gt hx.1) ht
  · rintro ⟨⟨hq, hP⟩, hnP⟩
    have hxb := B.pred_time hrespect hbound hB hP
    have hax : a < time x := by
      by_contra h
      exact hnP (hpast x hq (by omega))
    exact ⟨⟨hax, hxb⟩, (hlabels x ⟨hax, hxb⟩).mp hq⟩

theorem global_low_identity {r : J → J → Prop} {time : J → ℕ}
    {T a b ap bp v : ℕ} {A' B B' V : Boundary J} {S Sstar H : Set J}
    (hrespect : ∀ u z, r u z → time u < time z)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hA' : A'.At time T ap) (hB : B.At time T b)
    (hB' : B'.At time T bp) (hV : V.At time T v)
    (ha : a ≤ ap) (_hap : ap < bp) (hbp : bp ≤ v) (hvb : v < b)
    (hagree : ∀ x ∈ Window time a b, x ∈ H ↔ x ∈ S)
    (hsub : ∀ x ∈ Window time a b, x ∈ S → x ∈ Sstar)
    (hcenter : V.Separates r time (Window time a b) Sstar v)
    (hend : B'.Separates r time (Window time a v) S bp)
    (hlow : ∀ x ∈ Window time ap bp, x ∈ S → x ∈ A'.desc r ∩ B.pred r) :
    Window time ap bp ∩ S =
      A'.desc r ∩ B.pred r ∩ (B'.weakDesc r)ᶜ ∩ (V.weakDesc r)ᶜ ∩ H := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    have hxW : x ∈ Window time a b := ⟨by have := hx.1; omega, by have := hx.2; omega⟩
    refine ⟨⟨⟨hlow x hx hS, ?_⟩, ?_⟩, (hagree x hxW).mpr hS⟩
    · intro hbad
      have := B'.weakDesc_time hrespect hbound hB' hbad
      have := hx.2
      omega
    · intro hbad
      have := V.weakDesc_time hrespect hbound hV hbad
      have := hx.2
      omega
  · rintro ⟨⟨⟨⟨hD, hP⟩, hnB⟩, hnV⟩, hH⟩
    have hapx := A'.desc_time hrespect hbound hA' hD
    have hxb := B.pred_time hrespect hbound hB hP
    have hxW : x ∈ Window time a b := ⟨by omega, hxb⟩
    have hS := (hagree x hxW).mp hH
    have hxv : time x < v := by
      by_contra h
      have hle : v ≤ time x := by omega
      rcases hle.eq_or_lt with he | hl
      · exact hnV (Boundary.mem_weak_at_time hbound hV he.symm).2
      · exact hnV (V.desc_subset_weakDesc r (hcenter.2 x hxW hl (hsub x hxW hS)))
    have hxbp : time x < bp := by
      by_contra h
      have hle : bp ≤ time x := by omega
      rcases hle.eq_or_lt with he | hl
      · exact hnB (Boundary.mem_weak_at_time hbound hB' he.symm).2
      · have hxE : x ∈ Window time a v := ⟨by omega, hxv⟩
        exact hnB (B'.desc_subset_weakDesc r (hend.2 x hxE hl hS))
    exact ⟨⟨hapx, hxbp⟩, hS⟩

end ThreeMachine.Structure

namespace ThreeMachine.Structure
variable {J : Type}

end ThreeMachine.Structure

end

end OAI
end


section
-- module FrameInvariants
namespace OAI

section

namespace ThreeMachine.Structure
namespace Layout
variable {J : Type} [Fintype J]

theorem time_bounds (p : Layout J) (hfull : 3 ∣ Fintype.card J) (x : J) :
    1 ≤ p.time x ∧ p.time x ≤ Fintype.card J / 3 := by
  obtain ⟨T, hT⟩ := hfull
  have hp := (p x).isLt
  dsimp [time]
  omega

noncomputable def slot (p : Layout J) (s : ℕ) : Finset J := by
  classical
  exact Finset.univ.filter (fun x => p.time x = s)

@[simp] theorem mem_slot (p : Layout J) (s : ℕ) (x : J) :
    x ∈ p.slot s ↔ p.time x = s := by
  classical
  simp [slot]

theorem card_slot (p : Layout J) (hfull : 3 ∣ Fintype.card J) (s : ℕ)
    (hs : 1 ≤ s) (hsT : s ≤ Fintype.card J / 3) : (p.slot s).card = 3 := by
  classical
  obtain ⟨T, hT⟩ := hfull
  let i : Fin (Fintype.card J) := ⟨3 * (s - 1), by omega⟩
  let j : Fin (Fintype.card J) := ⟨3 * (s - 1) + 1, by omega⟩
  let k : Fin (Fintype.card J) := ⟨3 * (s - 1) + 2, by omega⟩
  apply Finset.card_eq_three.mpr
  refine ⟨p.symm i, p.symm j, p.symm k, ?_, ?_, ?_, ?_⟩
  · intro he
    have hev := congrArg Fin.val (p.symm.injective he)
    dsimp [i, j] at hev
    omega
  · intro he
    have hev := congrArg Fin.val (p.symm.injective he)
    dsimp [i, k] at hev
    omega
  · intro he
    have hev := congrArg Fin.val (p.symm.injective he)
    dsimp [j, k] at hev
    omega
  · ext x
    simp only [mem_slot, Finset.mem_insert, Finset.mem_singleton]
    have hxi : x = p.symm i ↔ (p x).val = 3 * (s - 1) := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext_iff
    have hxj : x = p.symm j ↔ (p x).val = 3 * (s - 1) + 1 := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext_iff
    have hxk : x = p.symm k ↔ (p x).val = 3 * (s - 1) + 2 := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext_iff
    rw [hxi, hxj, hxk]
    dsimp [time]
    omega

noncomputable def triple (p : Layout J) (hfull : 3 ∣ Fintype.card J)
    (s : ℕ) (hs : 1 ≤ s) (hsT : s ≤ Fintype.card J / 3) : Triple J :=
  ⟨p.slot s, p.card_slot hfull s hs hsT⟩

def reverse (p : Layout J) : Layout J := p.trans Fin.revPerm

@[simp] theorem reverse_reverse (p : Layout J) : p.reverse.reverse = p := by
  ext x
  simp [reverse]

theorem reverse_time (p : Layout J) (hfull : 3 ∣ Fintype.card J) (x : J) :
    p.reverse.time x = Fintype.card J / 3 + 1 - p.time x := by
  obtain ⟨T, hT⟩ := hfull
  have hp := (p x).isLt
  change (Fintype.card J - ((p x).val + 1)) / 3 + 1 =
    Fintype.card J / 3 + 1 - ((p x).val / 3 + 1)
  omega

end Layout

namespace Boundary
variable {J : Type} [Fintype J]

end Boundary

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section IntervalHelpers
variable {J : Type} [Fintype J]

theorem Layout.FixedOutside.window {p q : Layout J} {W : Set J} {a b : ℕ}
    (h : p.FixedOutside q W) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) :
    ∀ x, x ∈ W ↔ x ∈ Window q.time a b := by
  intro x
  constructor
  · exact h.time_range (fun z hz => (hW z).mp hz)
  · intro hx
    by_contra hn
    have he := h.time hn
    apply hn
    apply (hW x).mpr
    change a < q.time x ∧ q.time x < b at hx
    change a < p.time x ∧ p.time x < b
    simpa only [he] using hx

theorem Layout.FixedOutside.boundary {p q : Layout J} {W : Set J} {a b s T : ℕ}
    {B : Boundary J} (h : p.FixedOutside q W)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hs : s ≤ a ∨ b ≤ s) (hB : B.At p.time T s) : B.At q.time T s := by
  cases B with
  | left => exact hB
  | right => exact hB
  | actual Z =>
      refine ⟨hB.1, hB.2.1, ?_⟩
      intro x
      by_cases hx : x ∈ W
      · have hp := (hW x).mp hx
        have hq := (h.window hW x).mp hx
        have hnp : p.time x ≠ s := by rcases hs with hs | hs <;> dsimp [Window] at hp <;> omega
        have hnq : q.time x ≠ s := by rcases hs with hs | hs <;> dsimp [Window] at hq <;> omega
        rw [hB.2.2]
        exact iff_of_false hnp hnq
      · rw [hB.2.2, h.time hx]

theorem PastInvariant.reorder {r : J → J → Prop} {p q : Layout J}
    {K : GlobalList J} {A : Boundary J} {a b : ℕ} {W : Set J}
    (hpast : PastInvariant r p.time K A a) (hfix : p.FixedOutside q W)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) :
    PastInvariant r q.time K A a := by
  intro x hx htime
  have hnW : x ∉ W := by
    intro hw
    have h := ((hfix.window hW) x).mp hw
    exact (not_lt_of_ge htime) h.1
  have ht : p.time x = q.time x := (hfix.time hnW).symm
  exact hpast x hx (ht ▸ htime)

def SwapInvariant [DecidableEq J] (r : J → J → Prop) (p : Layout J)
    (W : Set J) (K : GlobalList J) (rank : J → ℕ) (A : Boundary J) (a : ℕ) : Prop :=
  ∀ q : Layout J, p.FixedOutside q W → q.Respects r →
    ∀ x ∈ W, x ∉ A.desc r → ∀ y, q.time y = a → y ∈ K.Qual →
      K.KeyLT rank x y → ¬(q.exchange x y).Respects r

theorem SwapInvariant.reorder [DecidableEq J] {r : J → J → Prop} {p q : Layout J}
    {W : Set J} {K : GlobalList J} {rank : J → ℕ} {A : Boundary J} {a : ℕ}
    (h : SwapInvariant r p W K rank A a) (hfix : p.FixedOutside q W) :
    SwapInvariant r q W K rank A a := by
  intro u hqu hu x hx hnx y hy hyq hkey
  exact h u (hfix.trans hqu) hu x hx hnx y hy hyq hkey

end IntervalHelpers
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section BoundaryWalk
variable {J : Type} [Fintype J]

end BoundaryWalk
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section VaryingWalk
variable {J : Type}

inductive CutoffWalk (E : Finset J) (r : J → J → Prop) (time priority : J → ℕ)
    (Sfinal : Set J) (a : ℕ) : ℕ → Prop
  | refl : CutoffWalk E r time priority Sfinal a a
  | step {s : ℕ} {x : J} {U : Set J}
      (prev : CutoffWalk E r time priority Sfinal a s)
      (ideal : IdealOn E r U) (isPrefix : PrefixOn E priority U)
      (below : ∀ z ∈ E, z ∈ U → z ∈ Sfinal)
      (exception : Exception E r time U s x) :
      CutoffWalk E r time priority Sfinal a (time x)

end VaryingWalk

section PastUpdate
variable {J : Type} [Fintype J]

end PastUpdate
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ChildSwaps
variable {J : Type} [Fintype J] [DecidableEq J]

theorem swap_prune {r : J → J → Prop} {p : Layout J}
    {W : Set J} {K : GlobalList J} {rank : J → ℕ} {A : Boundary J} {a : ℕ}
    (hparent : SwapInvariant r p W K rank A a) :
    SwapInvariant r p W (K.prune W) rank A a := by
  intro q hfix hq x hx hnx y hy hyq hkey
  exact hparent q hfix hq x hx hnx y hy (K.prune_qual_subset W hyq)
    (GlobalList.prune_key hx hkey)

end ChildSwaps
end ThreeMachine.Structure

end

end OAI
end


section
-- module RunCertificates
namespace OAI

section

namespace ThreeMachine.Structure
section RunCertificates
variable {J A : Type}

def RankTail (rank : J → ℕ) (k : ℕ) : Set J := {x | k ≤ rank x}

structure RunData (K : GlobalList J) (rank : J → ℕ) (atoms : A → Set J)
    (W : Set J) where
  base : ℕ → Set J
  threshold : ℕ → ℕ
  second : Set J
  entry_eq : ∀ i ∈ K.indices, K.entry i = base i ∩ RankTail rank (threshold i)
  simple : ∀ i ∈ K.indices, i ≠ 0 → Described atoms (base i) 2
  first_small : Described atoms (base 0) 24
  second_small : Described atoms second 1
  second_eq : base 1 = second
  cover : ∀ x ∈ W, x ∉ second → x ∈ base 0
  pair : 0 ∈ K.indices → ∀ x ∈ W, x ∈ second → 1 ∈ K.indices ∧ x ∈ K.entry 1

namespace RunData
variable {K : GlobalList J} {rank : J → ℕ} {atoms : A → Set J} {W W' : Set J}

noncomputable def carry (D : RunData K rank atoms W) (d k : ℕ) :
    RunData (K.carry rank d k) rank atoms W := by
  classical
  refine { base := D.base
           threshold := fun i => if i = d then max (D.threshold i) k else D.threshold i
           second := D.second
           entry_eq := ?_
           simple := ?_
           first_small := D.first_small
           second_small := D.second_small
           second_eq := D.second_eq
           cover := D.cover
           pair := ?_ }
  · intro i hi
    have hi' : i ∈ K.indices ∧ d ≤ i := Finset.mem_filter.mp hi
    change (if i = d then K.entry i ∩ {x | k ≤ rank x} else K.entry i) = _
    rw [D.entry_eq i hi'.1]
    by_cases hid : i = d
    · simp only [hid, ite_eq_left]
      ext x
      simp only [Set.mem_inter_iff, RankTail, Set.mem_ofPred_eq, max_le_iff]
      tauto
    · simp only [hid, ite_false]
  · intro i hi hn
    exact D.simple i (Finset.mem_filter.mp hi).1 hn
  · intro hzero x hx hxD
    have hd : d = 0 := by have := (Finset.mem_filter.mp hzero).2; omega
    have hz : 0 ∈ K.indices := (Finset.mem_filter.mp hzero).1
    obtain ⟨h1, hx1⟩ := D.pair hz x hx hxD
    refine ⟨Finset.mem_filter.mpr ⟨h1, by omega⟩, ?_⟩
    change x ∈ if 1 = d then _ else _
    simpa [hd] using hx1

noncomputable def prune (D : RunData K rank atoms W) (hsub : W' ⊆ W) :
    RunData (K.prune W') rank atoms W' := by
  classical
  refine { base := D.base, threshold := D.threshold, second := D.second
           entry_eq := ?_, simple := ?_, first_small := D.first_small
           second_small := D.second_small, second_eq := D.second_eq
           cover := fun x hx hn => D.cover x (hsub hx) hn
           pair := ?_ }
  · intro i hi
    exact D.entry_eq i (Finset.mem_filter.mp hi).1
  · intro i hi hn
    exact D.simple i (Finset.mem_filter.mp hi).1 hn
  · intro hzero x hx hxD
    obtain ⟨h1, hx1⟩ := D.pair (Finset.mem_filter.mp hzero).1 x (hsub hx) hxD
    exact ⟨Finset.mem_filter.mpr ⟨h1, ⟨x, hx1, hx⟩⟩, hx1⟩

noncomputable def append (D : RunData K rank atoms W) (I : Set J)
    (hI : Described atoms I 2) : RunData (K.append I) rank atoms W := by
  classical
  have hnext : 2 ≤ K.nextIndex := by dsimp [GlobalList.nextIndex]; omega
  refine { base := fun i => if i = K.nextIndex then I else D.base i
           threshold := fun i => if i = K.nextIndex then 0 else D.threshold i
           second := D.second
           entry_eq := ?_, simple := ?_, first_small := ?_
           second_small := D.second_small, second_eq := ?_
           cover := ?_, pair := ?_ }
  · intro i hi
    change i ∈ insert K.nextIndex K.indices at hi
    change (if i = K.nextIndex then I else K.entry i) = _
    by_cases he : i = K.nextIndex
    · simp only [he, ite_eq_left]
      ext x
      simp [RankTail]
    · have hiK : i ∈ K.indices := (Finset.mem_insert.mp hi).resolve_left he
      simpa only [he, ite_false] using D.entry_eq i hiK
  · intro i hi hn
    change i ∈ insert K.nextIndex K.indices at hi
    by_cases he : i = K.nextIndex
    · simpa only [he, ite_eq_left] using hI
    · simpa only [he, ite_false] using D.simple i ((Finset.mem_insert.mp hi).resolve_left he) hn
  · simpa only [show 0 ≠ K.nextIndex by omega, ite_false] using D.first_small
  · simpa only [show 1 ≠ K.nextIndex by omega, ite_false] using D.second_eq
  · intro x hx hn
    simpa only [show 0 ≠ K.nextIndex by omega, ite_false] using D.cover x hx hn
  · intro hz x hx hxD
    change 0 ∈ insert K.nextIndex K.indices at hz
    have hzK : 0 ∈ K.indices := (Finset.mem_insert.mp hz).resolve_left (by omega)
    obtain ⟨h1, hx1⟩ := D.pair hzK x hx hxD
    refine ⟨Finset.mem_insert_of_mem h1, ?_⟩
    change x ∈ if 1 = K.nextIndex then I else K.entry 1
    simpa only [show 1 ≠ K.nextIndex by omega, ite_false] using hx1

theorem entry_small (D : RunData K rank atoms W)
    (hrank : ∀ k, Described atoms (RankTail rank k) 1) {i : ℕ} (hi : i ∈ K.indices) :
    Described atoms (K.entry i) 25 := by
  rw [D.entry_eq i hi]
  by_cases he : i = 0
  · subst i
    exact D.first_small.inter (hrank _)
  · exact ((D.simple i hi he).inter (hrank _)).mono (by omega)

noncomputable def flatEntry (D : RunData K rank atoms W) (i : ℕ) : Set J :=
  if i = 0 then D.second ∪ RankTail rank (D.threshold 0) else K.entry i

end RunData
end RunCertificates
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace GlobalList
variable {J : Type}

def empty : GlobalList J := ⟨∅, fun _ => ∅⟩

def one (A : Set J) : GlobalList J := ⟨{1}, fun _ => A⟩

def pair (A B : Set J) : GlobalList J := ⟨{0, 1}, fun i => if i = 0 then A else B⟩

@[simp] theorem qual_empty : (empty : GlobalList J).Qual = ∅ := by
  ext x
  simp [Qual, empty]

@[simp] theorem qual_one (A : Set J) : (one A).Qual = A := by
  ext x
  simp [Qual, one]

@[simp] theorem qual_pair (A B : Set J) : (pair A B).Qual = A ∪ B := by
  ext x
  simp [Qual, pair]

def InjectionDisjoint (K : GlobalList J) (W : Set J) : Prop :=
  ∀ i ∈ K.indices, 2 ≤ i → ∀ j ∈ K.indices, 2 ≤ j → i ≠ j →
    ∀ x ∈ W, x ∈ K.entry i → x ∉ K.entry j

theorem InjectionDisjoint.prune {K : GlobalList J} {W W' : Set J}
    (h : K.InjectionDisjoint W) (hsub : W' ⊆ W) : (K.prune W').InjectionDisjoint W' := by
  classical
  intro i hi h2i j hj h2j hn x hx hxi hxj
  exact h i (Finset.mem_filter.mp hi).1 h2i j (Finset.mem_filter.mp hj).1 h2j hn
    x (hsub hx) hxi hxj

theorem pruned_length {K : GlobalList J} {r : J → J → Prop}
    {W W' : Set J} {B : Triple J}
    (hup : K.Upsets r) (hdisj : K.InjectionDisjoint W)
    (hB : ∀ z ∈ B.val, z ∈ W)
    (hhigh : ∀ x ∈ W', x ∈ K.Qual → ∃ z ∈ B.val, r x z) :
    (K.prune W').indices.card ≤ 5 := by
  classical
  let P := K.prune W'
  let I := P.indices.filter (2 ≤ ·)
  have hI : ∀ i ∈ I, i ∈ K.indices := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hactive : ∀ i ∈ I, ∃ x ∈ W', x ∈ K.entry i := by
    intro i hi
    obtain ⟨x, hxK, hxW⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    exact ⟨x, hxW, hxK⟩
  have hcap : I.card ≤ B.val.card := injection_card_bound (fun _ hi => hI _ hi) hup
    (fun _ hz => hB _ hz)
    (fun i hi j hj hn x hx hxi hxj => hdisj i (hI i hi) (Finset.mem_filter.mp hi).2
      j (hI j hj) (Finset.mem_filter.mp hj).2 hn x hx hxi hxj)
    (fun i hi => by obtain ⟨x, hxW, hxi⟩ := hactive i hi; exact ⟨x, hxi, hxW⟩)
    (fun x hx hxq => hhigh x hx hxq)
  have hsmall : (P.indices.filter (fun i => i < 2)).card ≤ 2 := by
    apply le_trans (Finset.card_le_card (t := {0, 1}) ?_) (by decide)
    intro i hi
    have hi2 := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsum := Finset.card_filter_add_card_filter_not (s := P.indices) (p := fun i => 2 ≤ i)
  have hnot : P.indices.filter (fun i => ¬2 ≤ i) = P.indices.filter (fun i => i < 2) := by
    simp only [not_le]
  rw [hnot] at hsum
  change I.card + _ = P.indices.card at hsum
  have hthree := B.property
  change (K.prune W').indices.card ≤ 5
  dsimp only [P] at hsum hsmall
  omega

end GlobalList

namespace RunData
variable {J A : Type} {rank : J → ℕ} {atoms : A → Set J} {W : Set J}

noncomputable def root (htrue : Described atoms Set.univ 1) :
    RunData (GlobalList.one Set.univ) rank atoms W := by
  refine { base := fun _ => Set.univ, threshold := fun _ => 0, second := Set.univ
           entry_eq := ?_, simple := ?_, first_small := htrue.mono (by omega)
           second_small := htrue, second_eq := rfl, cover := ?_, pair := ?_ }
  · intro i _
    ext x
    simp [GlobalList.one, RankTail]
  · intro i _ _
    exact htrue.mono (by omega)
  · intro x _ _
    trivial
  · intro hz
    simp [GlobalList.one] at hz

noncomputable def switched {G D : Set J} (hG : Described atoms G 24)
    (hD : Described atoms D 1) (hcover : ∀ x ∈ W, x ∉ D → x ∈ G) (k : ℕ) :
    RunData (GlobalList.pair (G ∩ RankTail rank k) D) rank atoms W := by
  refine { base := fun i => if i = 0 then G else D
           threshold := fun i => if i = 0 then k else 0
           second := D
           entry_eq := ?_, simple := ?_, first_small := ?_
           second_small := hD, second_eq := ?_, cover := ?_, pair := ?_ }
  · intro i _
    by_cases he : i = 0
    · simp [GlobalList.pair, he]
    · ext x
      simp [GlobalList.pair, he, RankTail]
  · intro i _ hn
    simpa only [hn, ite_false] using hD.mono (show 1 ≤ 2 by omega)
  · simpa using hG
  · simp
  · simpa using hcover
  · intro _ x _ hx
    exact ⟨by simp [GlobalList.pair], by simpa [GlobalList.pair] using hx⟩

end RunData
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section NumericWalk
variable {J : Type}

def PriorityCut (priority : J → ℕ) (k : ℕ) : Set J := {x | priority x < k}

structure NumericWalkData (E : Finset J) (r : J → J → Prop)
    (time priority : J → ℕ) (a lo count : ℕ) where
  position : Fin (count+1) → ℕ
  first : position 0 = a
  endpoint : ∀ i, position i = a ∨ ∃ x ∈ E, time x = position i
  separator : ∀ i, Separator E r time (PriorityCut priority (lo+i.val)) (position i)
  history : ∀ i, CutoffWalk E r time priority (PriorityCut priority (lo+i.val)) a (position i)
  steps : ∀ i : Fin count,
    AdvancePath E r time (PriorityCut priority (lo+i.val+1))
      (position i.castSucc) (position i.succ) ∧
    Separator E r time (PriorityCut priority (lo+i.val)) (position i.succ)

end NumericWalk
end ThreeMachine.Structure

end

end OAI
end


section
-- module PriorityUpdates
namespace OAI

section

namespace ThreeMachine.Structure
section PriorityEncoding
variable {J : Type}

namespace GlobalList

noncomputable def keyValue (K : GlobalList J) (rank : J → ℕ) (B : ℕ) (x : J) : ℕ :=
  K.lastIndex x * B + rank x

noncomputable def samePriority (K : GlobalList J) (rank : J → ℕ) (B : ℕ)
    (P : Set J) (x : J) : ℕ := by
  classical
  exact if x ∈ K.Qual then B + K.keyValue rank B x
    else if x ∈ P then rank x else B + (K.indices.sup id + 1) * B + rank x

end GlobalList
end PriorityEncoding
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchedPriorities
variable {J : Type}

noncomputable def switchPriority (rank : J → ℕ) (B : ℕ) (D : Set J) (x : J) : ℕ := by
  classical
  exact if x ∈ D then B + rank x else rank x

namespace GlobalList

end GlobalList
end SwitchedPriorities
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ReverseSeeds
variable {J A : Type}

structure ReverseSeed (r : J → J → Prop) (time : J → ℕ) (atoms : A → Set J)
    (W : Set J) (B : Boundary J) (b : ℕ) where
  predicate : Set J
  downset : GlobalUpset (fun x y => r y x) predicate
  small : Described atoms predicate 24
  cover : ∀ x ∈ W, x ∉ B.pred r → x ∈ predicate
  earlier : ∀ x ∈ predicate, time x < b

variable {r : J → J → Prop} {time : J → ℕ} {atoms : A → Set J}

theorem reverse_seed_at_edge {T a b ap bp v : ℕ} {B B' V : Boundary J}
    {W E W' S Sstar Hext : Set J}
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hrespect : ∀ x y, r x y → time x < time y)
    (hbound : ∀ x, 1 ≤ time x ∧ time x ≤ T)
    (hB : B.At time T b) (hB' : B'.At time T bp) (hV : V.At time T v)
    (hW : W = Window time a b) (hE : E = Window time a v)
    (hW' : W' = Window time ap bp)
    (hapos : a ≤ ap) (hab : ap < bp) (hbv : bp ≤ v) (hvb : v < b)
    (hhigh : ∀ x ∈ W', x ∉ S → x ∈ B'.pred r)
    (hcovers : ∀ x ∈ W, x ∈ S → x ∈ B.pred r)
    (hbelow : ∀ x ∈ W, x ∈ S → x ∈ Sstar)
    (hcenter : V.Separates r time W Sstar v)
    (hsep : B'.Separates r time E S bp)
    (hH : GlobalUpset (fun x y => r y x) Hext)
    (hagrees : ∀ x ∈ W, x ∈ Hext ↔ x ∈ S)
    (hsmall : Described atoms Hext 21)
    (hPsmall : Described atoms (B.pred r) 1)
    (hDbsmall : Described atoms (B'.weakDesc r) 1)
    (hDvsmall : Described atoms (V.weakDesc r) 1) :
    Nonempty (ReverseSeed r time atoms W' B' bp) := by
  let G := ((B.pred r \ B'.weakDesc r) \ V.weakDesc r) ∩ Hext
  have hup : GlobalUpset (fun x y => r y x) G := by
    intro x y hyx hx
    refine ⟨⟨⟨Boundary.pred_downset htrans B hyx hx.1.1.1, ?_⟩, ?_⟩, hH hyx hx.2⟩
    · intro hy
      exact hx.1.1.2 (Boundary.weakDesc_upset htrans B' hyx hy)
    · intro hy
      exact hx.1.2 (Boundary.weakDesc_upset htrans V hyx hy)
  have hGsmall : Described atoms G 24 := by
    exact ((hPsmall.diff hDbsmall).diff hDvsmall).inter hsmall
  refine ⟨⟨G, hup, hGsmall, ?_, ?_⟩⟩
  · intro x hx hnP
    have hxt : x ∈ Window time ap bp := hW' ▸ hx
    change ap < time x ∧ time x < bp at hxt
    have hxW : x ∈ W := hW ▸ show x ∈ Window time a b from ⟨by omega, by omega⟩
    have hxS : x ∈ S := by by_contra hn; exact hnP (hhigh x hx hn)
    refine ⟨⟨⟨hcovers x hxW hxS, ?_⟩, ?_⟩, (hagrees x hxW).mpr hxS⟩
    · intro hD
      have := Boundary.weakDesc_time hrespect hbound hB' hD
      omega
    · intro hD
      have := Boundary.weakDesc_time hrespect hbound hV hD
      omega
  · intro x hx
    have hxb := Boundary.pred_time hrespect hbound hB hx.1.1.1
    by_contra hn
    have hxW : x ∈ W := hW ▸ show x ∈ Window time a b from ⟨by omega, hxb⟩
    have hxS := (hagrees x hxW).mp hx.2
    have hxv : time x < v := by
      by_contra hnv
      rcases (show v ≤ time x by omega).eq_or_lt with he | hl
      · exact hx.1.2 (Boundary.mem_weak_at_time hbound hV he.symm).2
      · exact hx.1.2 (V.desc_subset_weakDesc r (hcenter.2 x hxW hl (hbelow x hxW hxS)))
    have hxE : x ∈ E := hE ▸ show x ∈ Window time a v from ⟨by omega, hxv⟩
    rcases (show bp ≤ time x by omega).eq_or_lt with he | hl
    · exact hx.1.1.2 (Boundary.mem_weak_at_time hbound hB' he.symm).2
    · exact hx.1.1.2 (B'.desc_subset_weakDesc r (hsep.2 x hxE hl hxS))

variable [Fintype J]

def ReverseSeed.reorder {p q : Layout J} {W : Set J} {B : Boundary J} {a b : ℕ}
    (D : ReverseSeed r p.time atoms W B b)
    (hW : W = Window p.time a b) (hfix : p.FixedOutside q W) :
    ReverseSeed r q.time atoms W B b := by
  refine { D with earlier := ?_ }
  intro x hx
  by_cases hxW : x ∈ W
  · exact ((hfix.time_range (fun z hz => hW ▸ hz) hxW)).2
  · rw [hfix.time hxW]
    exact D.earlier x hx

end ReverseSeeds
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section DescriptionInterface
variable {J A : Type} {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}

structure AtomSupport (atoms : A → Set J) (r : J → J → Prop) (rank : J → ℕ) : Prop where
  truth : Described atoms Set.univ 1
  falsity : Described atoms ∅ 1
  rankTail : ∀ k, Described atoms (RankTail rank k) 1
  pred : ∀ B : Boundary J, Described atoms (B.pred r) 1
  desc : ∀ B : Boundary J, Described atoms (B.desc r) 1
  weakPred : ∀ B : Boundary J, Described atoms (B.weakPred r) 1
  weakDesc : ∀ B : Boundary J, Described atoms (B.weakDesc r) 1
  triple : ∀ Z : Triple J, Described atoms (Z.val : Set J) 1

namespace RunData
variable {K : GlobalList J} {W : Set J}

theorem qual_small (D : RunData K rank atoms W) (hA : AtomSupport atoms r rank)
    (hcard : K.indices.card ≤ 5) : Described atoms K.Qual 195 := by
  classical
  by_cases hne : K.indices.Nonempty
  · have hd := Described.finite_union K.indices K.entry (fun _ => 25) hne
      (fun i hi => D.entry_small hA.rankTail hi)
    apply hd.mono
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  · have hzero : K.indices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have he : K.Qual = ∅ := by ext x; simp [GlobalList.Qual, hzero]
    rw [he]
    exact hA.falsity.mono (by omega)

end RunData

theorem global_child_small
    {A' B B' V : Boundary J} {W' S Stilde : Set J} {K' : GlobalList J}
    (hA : AtomSupport atoms r rank)
    (hqual : Described atoms K'.Qual 195)
    (hcut : Described atoms Stilde 205)
    (hhigh : W' \ S = (K'.Qual ∩ B'.pred r) \ A'.weakPred r)
    (hlow : W' ∩ S = (((A'.desc r ∩ B.pred r) \ B'.weakDesc r) \ V.weakDesc r) ∩ Stilde) :
    Described atoms W' 406 := by
  have hh : Described atoms (W' \ S) 197 := by
    rw [hhigh]
    exact (hqual.inter (hA.pred B')).diff (hA.weakPred A')
  have hl : Described atoms (W' ∩ S) 209 := by
    rw [hlow]
    exact ((((hA.desc A').inter (hA.pred B)).diff (hA.weakDesc B')).diff (hA.weakDesc V)).inter hcut
  have he : W' = (W' \ S) ∪ (W' ∩ S) := by ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [he]
  exact hh.union hl

end DescriptionInterface
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace GlobalList
section SameUpdate
variable {J : Type} {K : GlobalList J} {rank : J → ℕ}

noncomputable def sameUpdate (K : GlobalList J) (rank : J → ℕ) (B t : ℕ)
    (D P : Set J) : GlobalList J :=
  (K.carry rank (t/B) (t%B)).append (D \ P)

end SameUpdate
end GlobalList
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SameBoundaryUpdate
variable {J : Type} [Fintype J] [DecidableEq J]

end SameBoundaryUpdate
end ThreeMachine.Structure

end

end OAI
end


section
-- module NodeCertificates
namespace OAI

section

namespace ThreeMachine.Structure
section NodeCertificates
variable {J A : Type} [Fintype J] [DecidableEq J]

structure NodeData (r : J → J → Prop) (rank : J → ℕ) (atoms : A → Set J)
    (p : Layout J) (W : Set J) where
  full : p.Full r
  a : ℕ
  b : ℕ
  left : Boundary J
  right : Boundary J
  leftAt : left.At p.time (Fintype.card J / 3) a
  rightAt : right.At p.time (Fintype.card J / 3) b
  window : ∀ x, x ∈ W ↔ x ∈ Window p.time a b
  list : GlobalList J
  run : RunData list rank atoms W
  upsets : list.Upsets r
  second_upset : GlobalUpset r run.second
  disjoint : list.InjectionDisjoint W
  length : list.indices.card ≤ 5
  high : ∀ x ∈ W, x ∈ list.Qual → x ∈ right.pred r
  low : ∀ x ∈ W, x ∉ list.Qual → x ∈ left.desc r
  past : PastInvariant r p.time list left a
  swap : SwapInvariant r p W list rank left a
  small : Described atoms W 406
  reverseSeed : ReverseSeed r p.time atoms W right b

namespace NodeData
variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J}

def reorder (D : NodeData r rank atoms p W) (hfix : p.FixedOutside q W)
    (hq : q.Respects r) : NodeData r rank atoms q W :=
  { D with
    full := ⟨D.full.1, hq⟩
    leftAt := hfix.boundary D.window (Or.inl le_rfl) D.leftAt
    rightAt := hfix.boundary D.window (Or.inr le_rfl) D.rightAt
    window := hfix.window D.window
    past := D.past.reorder hfix D.window
    swap := D.swap.reorder hfix
    reverseSeed := D.reverseSeed.reorder (Set.ext D.window) hfix }

noncomputable def root (p : Layout J) (hp : p.Full r)
    (hA : AtomSupport atoms r rank) : NodeData r rank atoms p Set.univ := by
  refine { full := hp, a := 0, b := Fintype.card J / 3 + 1
           left := .left, right := .right, leftAt := rfl, rightAt := rfl
           window := ?_, list := .one Set.univ, run := RunData.root hA.truth
           upsets := ?_, second_upset := ?_, disjoint := ?_, length := ?_
           high := ?_, low := ?_, past := ?_, swap := ?_
           small := hA.truth.mono (by omega), reverseSeed := ?_ }
  · intro x
    have := p.time_bounds hp.1 x
    simp only [Set.mem_univ, Window, Set.mem_ofPred_eq, true_iff]
    omega
  · intro i _ x y _ _
    trivial
  · intro x y _ _
    trivial
  · intro i hi h2i
    simp only [GlobalList.one, Finset.mem_singleton] at hi
    omega
  · simp [GlobalList.one]
  · intro x _ _
    trivial
  · intro x _ _
    trivial
  · intro x _ htime
    have := (p.time_bounds hp.1 x).1
    omega
  · intro q _ _ x _ _ y hy
    have := (q.time_bounds hp.1 y).1
    omega
  · refine ⟨Set.univ, ?_, hA.truth.mono (by omega), ?_, ?_⟩
    · intro x y _ _
      trivial
    · intro x _ _
      trivial
    · intro x _
      have := (p.time_bounds hp.1 x).2
      omega

end NodeData

structure EdgeData (r : J → J → Prop) (rank : J → ℕ) (atoms : A → Set J)
    (p : Layout J) (W : Set J) (a b v ap bp : ℕ)
    (B V A' B' : Boundary J) where
  full : p.Full r
  parent : W = Window p.time a b
  endAt : B.At p.time (Fintype.card J / 3) b
  centerAt : V.At p.time (Fintype.card J / 3) v
  startAt : A'.At p.time (Fintype.card J / 3) ap
  targetAt : B'.At p.time (Fintype.card J / 3) bp
  targetActual : ∃ Z, B' = Boundary.actual Z
  start_le : a ≤ ap
  strict : ap < bp
  target_le : bp ≤ v
  center_lt : v < b
  cutoff : Set J
  finalCutoff : Set J
  finalSmall : Described atoms finalCutoff 1
  centerSep : V.Separates r p.time W finalCutoff v
  startSep : A'.Separates r p.time (Window p.time a v) cutoff ap
  targetSep : B'.Separates r p.time (Window p.time a v) cutoff bp
  covers : ∀ x ∈ W, x ∈ cutoff → x ∈ B.pred r
  below : ∀ x ∈ W, x ∈ cutoff → x ∈ finalCutoff
  list : GlobalList J
  run : RunData list rank atoms W
  upsets : list.Upsets r
  second_upset : GlobalUpset r run.second
  disjoint : list.InjectionDisjoint W
  labels : ∀ x ∈ W, x ∈ list.Qual ↔ x ∉ cutoff
  past : PastInvariant r p.time list A' ap
  swap : SwapInvariant r p (Window p.time ap bp) list rank A' ap
  globalCutoff : Set J
  cutoffSmall : Described atoms globalCutoff 205
  cutoffAgrees : ∀ x ∈ W, x ∈ globalCutoff ↔ x ∈ cutoff
  lowExtension : Set J
  downset : GlobalUpset (fun x y => r y x) lowExtension
  lowSmall : Described atoms lowExtension 21
  lowAgrees : ∀ x ∈ W, x ∈ lowExtension ↔ x ∈ cutoff

namespace EdgeData
variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {a b v ap bp : ℕ} {B V A' B' : Boundary J}

noncomputable def toNode
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) :
    NodeData r rank atoms p (Window p.time ap bp) := by
  let W' := Window p.time ap bp
  have hsub : W' ⊆ W := by
    intro x hx
    rw [D.parent]
    exact ⟨D.start_le.trans_lt hx.1, hx.2.trans_le D.target_le |>.trans D.center_lt⟩
  have hE : W' ⊆ Window p.time a v := by
    intro x hx
    exact ⟨D.start_le.trans_lt hx.1, hx.2.trans_le D.target_le⟩
  have hhigh : ∀ x ∈ W', x ∉ D.cutoff → x ∈ B'.pred r := by
    intro x hx hn
    exact D.targetSep.1 x (hE hx) hx.2 hn
  have hlow : ∀ x ∈ W', x ∈ D.cutoff → x ∈ A'.desc r ∩ B.pred r := by
    intro x hx hS
    exact ⟨D.startSep.2 x (hE hx) hx.1 hS, D.covers x (hsub hx) hS⟩
  let K' := D.list.prune W'
  let R' := D.run.prune hsub
  have hqual : ∀ x ∈ W', x ∈ K'.Qual ↔ x ∉ D.cutoff := by
    intro x hx
    exact (GlobalList.prune_qual D.list hx).trans (D.labels x (hsub hx))
  have hlength : K'.indices.card ≤ 5 := by
    obtain ⟨Z, hZ⟩ := D.targetActual
    apply GlobalList.pruned_length D.upsets D.disjoint (B := Z)
    · intro z hz
      have ht : p.time z = bp := (show (Boundary.actual Z).At p.time
        (Fintype.card J / 3) bp from hZ ▸ D.targetAt).2.2 z |>.mp hz
      rw [D.parent]
      exact ⟨by have := D.start_le; have := D.strict; omega,
        by have := D.target_le; have := D.center_lt; omega⟩
    · intro x hx hq
      have h := hhigh x hx ((D.labels x (hsub hx)).mp hq)
      simpa only [hZ, Boundary.pred, Set.mem_ofPred_eq] using h
  have hpast : PastInvariant r p.time K' A' ap := past_prune D.past
  have hh := global_high_identity D.full.2 (p.time_bounds D.full.1)
    D.startAt D.targetAt hqual hhigh hpast
  have hl := global_low_identity D.full.2 (p.time_bounds D.full.1)
    D.startAt D.endAt D.targetAt D.centerAt D.start_le D.strict D.target_le D.center_lt
    (fun x hx => D.cutoffAgrees x (D.parent ▸ hx))
    (fun x hx => D.below x (D.parent ▸ hx))
    (D.parent ▸ D.centerSep) D.targetSep hlow
  have hsmall : Described atoms W' 406 := global_child_small hA
    (R'.qual_small hA hlength) D.cutoffSmall hh hl
  have hseedExists := reverse_seed_at_edge htrans D.full.2 (p.time_bounds D.full.1)
    D.endAt D.targetAt D.centerAt D.parent rfl rfl D.start_le D.strict D.target_le D.center_lt
    hhigh D.covers D.below D.centerSep D.targetSep D.downset D.lowAgrees D.lowSmall
    (hA.pred B) (hA.weakDesc B') (hA.weakDesc V)
  exact { full := D.full, a := ap, b := bp, left := A', right := B'
          leftAt := D.startAt, rightAt := D.targetAt, window := fun _ => Iff.rfl
          list := K', run := R', upsets := GlobalList.prune_upsets D.upsets
          second_upset := D.second_upset, disjoint := D.disjoint.prune hsub, length := hlength
          high := fun x hx hq => hhigh x hx ((hqual x hx).mp hq)
          low := fun x hx hn => (hlow x hx (by by_contra h; exact hn ((hqual x hx).mpr h))).1
          past := hpast, swap := swap_prune D.swap, small := hsmall, reverseSeed := Classical.choice hseedExists }

end EdgeData
end NodeCertificates
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace Boundary
variable {J : Type} {time : J → ℕ} {T s : ℕ}

end Boundary

section SameEdges
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J}

end SameEdges
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchedEdges
variable {J A : Type} [Fintype J] [DecidableEq J]

structure SwitchSeed (r : J → J → Prop) (time : J → ℕ) (atoms : A → Set J)
    (W : Set J) (B : Boundary J) (a : ℕ) where
  predicate : Set J
  upset : GlobalUpset r predicate
  small : Described atoms predicate 24
  cover : ∀ x ∈ W, x ∉ B.desc r → x ∈ predicate
  later : ∀ x ∈ predicate, a < time x

variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J}

def ReverseSeed.toSwitch {B : Boundary J} {b : ℕ}
    (D : ReverseSeed r p.time atoms W B b) (hfull : 3 ∣ Fintype.card J)
    (hb : b ≤ Fintype.card J / 3 + 1) :
    SwitchSeed (fun x y => r y x) p.reverse.time atoms W B.reverse
      (Fintype.card J / 3 + 1 - b) := by
  refine { predicate := D.predicate, upset := D.downset, small := D.small
           cover := ?_, later := ?_ }
  · simpa only [Boundary.desc_reverse] using D.cover
  · intro x hx
    rw [Layout.reverse_time p hfull]
    have := D.earlier x hx
    have := p.time_bounds hfull x
    omega

end SwitchedEdges
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Centers
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J}

end Centers
end ThreeMachine.Structure

end

end OAI
end


section
-- module SplitPaths
namespace OAI

section

namespace ThreeMachine.Structure
section SplitGraph
variable {J A : Type}

def RelativeDescription (atoms : A → Set J) (W L : Set J) (k : ℕ) : Prop :=
  ∃ F, Described atoms F k ∧ L = W ∩ F

structure SplitVertex (r : J → J → Prop) (atoms : A → Set J) (W : Set J) where
  left : Set J
  middle : Triple J
  right : Set J
  partition : ∀ x, x ∈ W ↔ x ∈ left ∨ x ∈ middle.val ∨ x ∈ right
  left_middle : Disjoint left (middle.val : Set J)
  left_right : Disjoint left right
  middle_right : Disjoint (middle.val : Set J) right
  antichain : ∀ x ∈ middle.val, ∀ y ∈ middle.val, ¬r x y
  no_middle_left : ∀ x ∈ middle.val, ∀ y ∈ left, ¬r x y
  no_right_left : ∀ x ∈ right, ∀ y ∈ left, ¬r x y
  no_right_middle : ∀ x ∈ right, ∀ y ∈ middle.val, ¬r x y
  small_left : RelativeDescription atoms W left 10000
  small_right : RelativeDescription atoms W right 10000

namespace SplitVertex
variable {r : J → J → Prop} {atoms : A → Set J} {W : Set J}

@[ext] theorem ext {u v : SplitVertex r atoms W}
    (hl : u.left = v.left) (hm : u.middle = v.middle) (hr : u.right = v.right) : u = v := by
  cases u
  cases v
  cases hl
  cases hm
  cases hr
  rfl

def reverse (v : SplitVertex r atoms W) : SplitVertex (fun x y => r y x) atoms W :=
  { left := v.right, middle := v.middle, right := v.left
    partition := fun x => (v.partition x).trans (by tauto)
    left_middle := v.middle_right.symm, left_right := v.left_right.symm
    middle_right := v.left_middle.symm
    antichain := fun x hx y hy => v.antichain y hy x hx
    no_middle_left := fun x hx y hy => v.no_right_middle y hy x hx
    no_right_left := fun x hx y hy => v.no_right_left y hy x hx
    no_right_middle := fun x hx y hy => v.no_middle_left y hy x hx
    small_left := v.small_right, small_right := v.small_left }

@[simp] theorem reverse_reverse (v : SplitVertex r atoms W) : v.reverse.reverse = v := by
  apply ext <;> rfl

def AtTime (v : SplitVertex r atoms W) (time : J → ℕ) (s : ℕ) : Prop :=
  (∀ x, x ∈ v.left ↔ x ∈ W ∧ time x < s) ∧
  (∀ x, x ∈ v.middle.val ↔ x ∈ W ∧ time x = s) ∧
  (∀ x, x ∈ v.right ↔ x ∈ W ∧ s < time x)

theorem left_subset (v : SplitVertex r atoms W) : v.left ⊆ W :=
  fun x hx => (v.partition x).mpr (Or.inl hx)

theorem right_subset (v : SplitVertex r atoms W) : v.right ⊆ W :=
  fun x hx => (v.partition x).mpr (Or.inr (Or.inr hx))

theorem right_eq (v : SplitVertex r atoms W) : v.right = W \ (v.left ∪ v.middle.val) := by
  ext x
  have hlm := Set.disjoint_left.mp v.left_middle
  have hlr := Set.disjoint_left.mp v.left_right
  have hmr := Set.disjoint_left.mp v.middle_right
  constructor
  · intro hx
    exact ⟨v.right_subset hx, fun h => h.elim (fun hl => hlr hl hx) (fun hm => hmr hm hx)⟩
  · rintro ⟨hx, hn⟩
    rcases (v.partition x).mp hx with hl | hm | hr
    · exact (hn (Or.inl hl)).elim
    · exact (hn (Or.inr hm)).elim
    · exact hr

def Step (P : Set J → Prop) (u v : SplitVertex r atoms W) : Prop :=
  u.left ∪ u.middle.val ⊆ v.left ∧ P (v.left \ (u.left ∪ u.middle.val))

end SplitVertex

def AcceptedAt (r : J → J → Prop) (atoms : A → Set J) : ℕ → Set J → Prop
  | 0, W => Described atoms W 10000 ∧ W = ∅
  | n+1, W => Described atoms W 10000 ∧ (W = ∅ ∨
      ∃ u v : SplitVertex r atoms W, AcceptedAt r atoms n u.left ∧
        Relation.ReflTransGen (SplitVertex.Step (AcceptedAt r atoms n)) u v ∧
        AcceptedAt r atoms n v.right)

namespace AcceptedAt
variable {r : J → J → Prop} {atoms : A → Set J}

end AcceptedAt
end SplitGraph
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section TemporalSplits
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p q : Layout J} {W : Set J}

omit [Fintype J] in

theorem before_small (hA : AtomSupport atoms r rank) {H : Set J} {k : ℕ}
    (hH : Described atoms H k) (B : Boundary J) :
    Described atoms (B.before r H) (k+2) := by
  have h := (hA.pred B).union (hH.diff (hA.weakDesc B))
  simpa only [Boundary.before, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

noncomputable def SplitVertex.ofTime {a b s k : ℕ} {Z : Triple J} {F : Set J}
    (hp : p.Full r) (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hs : a < s ∧ s < b) (hZ : (Boundary.actual Z).At p.time (Fintype.card J / 3) s)
    (hF : Described atoms F k) (hk : k+1 ≤ 10000)
    (hZA : Described atoms (Z.val : Set J) 1)
    (hbefore : ∀ x ∈ W, x ∈ F ↔ p.time x < s) : SplitVertex r atoms W := by
  let L : Set J := {x | x ∈ W ∧ p.time x < s}
  let R : Set J := {x | x ∈ W ∧ s < p.time x}
  have hZm : ∀ x, x ∈ Z.val ↔ x ∈ W ∧ p.time x = s := by
    intro x
    rw [hZ.2.2 x]
    constructor
    · intro hx
      exact ⟨(hW x).mpr ⟨by omega, by omega⟩, hx⟩
    · exact And.right
  refine {
    left := L, middle := Z, right := R
    partition := ?_, left_middle := ?_, left_right := ?_, middle_right := ?_
    antichain := ?_, no_middle_left := ?_, no_right_left := ?_, no_right_middle := ?_
    small_left := ?_, small_right := ?_ }
  · intro x
    change x ∈ W ↔ (x ∈ W ∧ p.time x < s) ∨ x ∈ Z.val ∨ (x ∈ W ∧ s < p.time x)
    rw [hZm x]
    constructor
    · intro hx
      rcases lt_trichotomy (p.time x) s with h | h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inr ⟨hx, h⟩)
    · tauto
  · apply Set.disjoint_left.mpr
    intro x hx hm
    have := (hZm x).mp hm
    exact (ne_of_lt hx.2) this.2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2.le) hy.2
  · apply Set.disjoint_left.mpr
    intro x hm hr
    have := (hZm x).mp hm
    exact (ne_of_gt hr.2) this.2
  · intro x hx y hy hxy
    have := (hZ.2.2 x).mp hx
    have := (hZ.2.2 y).mp hy
    have := hp.2 x y hxy
    omega
  · intro x hx y hy hxy
    have := (hZ.2.2 x).mp hx
    have := hy.2
    have := hp.2 x y hxy
    omega
  · intro x hx y hy hxy
    have := hx.2
    have := hy.2
    have := hp.2 x y hxy
    omega
  · intro x hx y hy hxy
    have := hx.2
    have := (hZ.2.2 y).mp hy
    have := hp.2 x y hxy
    omega
  · refine ⟨F, hF.mono (by omega), ?_⟩
    ext x
    change (x ∈ W ∧ p.time x < s) ↔ x ∈ W ∧ x ∈ F
    exact and_congr_right (fun hx => (hbefore x hx).symm)
  · refine ⟨Fᶜ \ (Z.val : Set J), (hF.compl.diff hZA).mono hk, ?_⟩
    ext x
    change (x ∈ W ∧ s < p.time x) ↔ x ∈ W ∧ x ∉ F ∧ x ∉ Z.val
    rw [hZ.2.2 x]
    constructor
    · rintro ⟨hx, ht⟩
      exact ⟨hx, fun h => (not_lt_of_ge ht.le) ((hbefore x hx).mp h), (ne_of_gt ht)⟩
    · rintro ⟨hx, hn, he⟩
      have ht : ¬p.time x < s := fun h => hn ((hbefore x hx).mpr h)
      exact ⟨hx, by omega⟩

theorem EdgeData.target_description [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1) :
    ∃ F, Described atoms F 210 ∧ ∀ x ∈ W, x ∈ F ↔ p.time x < bp := by
  let F := V.before r D.finalCutoff ∩ B'.before r D.globalCutoff
  refine ⟨F, ?_, ?_⟩
  · exact (before_small hA hFinal V).inter (before_small hA D.cutoffSmall B')
  · intro x hx
    have hW : a < p.time x ∧ p.time x < b :=
      show x ∈ Window p.time a b from D.parent ▸ hx
    have hc := Boundary.separates_description D.full.2 (p.time_bounds D.full.1)
      D.centerAt D.centerSep (fun _ _ => Iff.rfl) x hx
    change x ∈ V.before r D.finalCutoff ∧ x ∈ B'.before r D.globalCutoff ↔ p.time x < bp
    constructor
    · rintro ⟨hv, hb⟩
      have hxE : x ∈ Window p.time a v := ⟨hW.1, hc.mp hv⟩
      exact (Boundary.separates_description D.full.2 (p.time_bounds D.full.1)
        D.targetAt D.targetSep (fun y hy => D.cutoffAgrees y (D.parent.symm ▸
          show y ∈ Window p.time a b from ⟨hy.1, hy.2.trans D.center_lt⟩)) x hxE).mp hb
    · intro ht
      have hxE : x ∈ Window p.time a v := ⟨hW.1, ht.trans_le D.target_le⟩
      refine ⟨hc.mpr hxE.2, ?_⟩
      exact (Boundary.separates_description D.full.2 (p.time_bounds D.full.1)
        D.targetAt D.targetSep (fun y hy => D.cutoffAgrees y (D.parent.symm ▸
          show y ∈ Window p.time a b from ⟨hy.1, hy.2.trans D.center_lt⟩)) x hxE).mpr ht

noncomputable def EdgeData.targetVertex [DecidableEq J]
    {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (hA : AtomSupport atoms r rank) (hFinal : Described atoms D.finalCutoff 1) :
    SplitVertex r atoms W := by
  let Z := Classical.choose D.targetActual
  have hZ : B' = Boundary.actual Z := Classical.choose_spec D.targetActual
  let F := Classical.choose (D.target_description hA hFinal)
  have hF := Classical.choose_spec (D.target_description hA hFinal)
  exact SplitVertex.ofTime D.full (fun x => D.parent ▸ Iff.rfl)
    ⟨D.start_le.trans_lt D.strict, D.target_le.trans_lt D.center_lt⟩
    (hZ ▸ D.targetAt) hF.1 (by omega) (hA.triple Z) hF.2

end TemporalSplits
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section PrefixPaths
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p q : Layout J} {W : Set J} {P : Set J → Prop}

def Reached (P : Set J → Prop) (r : J → J → Prop) (atoms : A → Set J)
    (W : Set J) (time : J → ℕ) (a s : ℕ) : Prop :=
  s = a ∨ ∃ u v : SplitVertex r atoms W, P u.left ∧
    Relation.ReflTransGen (SplitVertex.Step P) u v ∧ v.AtTime time s

end PrefixPaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section WalkPaths
variable {J A : Type} [Fintype J] {r : J → J → Prop} {rank : J → ℕ}
    {atoms : A → Set J} {p : Layout J} {W : Set J} {P : Set J → Prop}

end WalkPaths
end ThreeMachine.Structure

end

end OAI
end


section
-- module HierarchyCompleteness
namespace OAI

section

namespace ThreeMachine.Structure
section SamePaths
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {P : Set J → Prop}

end SamePaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchPaths
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J} {P : Set J → Prop}

omit [DecidableEq J] in
def SwitchSeed.reorder {L : Boundary J} {a b : ℕ}
    (G : SwitchSeed r p.time atoms W L a)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) (hfix : p.FixedOutside q W) :
    SwitchSeed r q.time atoms W L a := by
  refine { G with later := ?_ }
  intro x hx
  by_cases hxW : x ∈ W
  · exact ((hfix.window hW x).mp hxW).1
  · rw [hfix.time hxW]
    exact G.later x hx

end SwitchPaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SideNormalization
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {P : Set J → Prop}

end SideNormalization
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ReversePaths
variable {J A : Type} [Fintype J] {r : J → J → Prop}
    {atoms : A → Set J} {p : Layout J} {W S : Set J}

end ReversePaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] {atoms : A → Set J}

end Completeness
end ThreeMachine.Structure

end

end OAI
end


section
-- module HierarchySoundness
namespace OAI

section

namespace ThreeMachine.Structure
section Soundness
variable {J A : Type} [Fintype J] {r : J → J → Prop} {atoms : A → Set J}

structure FullBlock (r : J → J → Prop) (W : Set J) where
  length : ℕ
  time : J → ℕ
  bounds : ∀ x ∈ W, 1 ≤ time x ∧ time x ≤ length
  capacity : ∀ t, {x | x ∈ W ∧ time x = t}.ncard ≤ 3
  respects : ∀ x ∈ W, ∀ y ∈ W, r x y → time x < time y
  size : W.ncard = 3 * length

namespace FullBlock
variable {U V W : Set J}

def empty : FullBlock r (∅ : Set J) where
  length := 0
  time := fun _ => 0
  bounds := by simp
  capacity := by simp
  respects := by simp
  size := by simp

def triple (Z : Triple J) (hZ : ∀ x ∈ Z.val, ∀ y ∈ Z.val, ¬r x y) :
    FullBlock r (Z.val : Set J) where
  length := 1
  time := fun _ => 1
  bounds := by simp
  capacity := fun _ => (Set.ncard_le_ncard (fun _ hx => hx.1)).trans (by simpa using Z.property.le)
  respects := fun x hx y hy h => (hZ x hx y hy h).elim
  size := by simpa using Z.property

noncomputable def append (s : FullBlock r U) (t : FullBlock r V)
    (hd : Disjoint U V) (hback : ∀ x ∈ V, ∀ y ∈ U, ¬r x y) :
    FullBlock r (U ∪ V) := by
  classical
  let time : J → ℕ := fun x => if x ∈ U then s.time x else s.length + t.time x
  have htimeU (x : J) (hx : x ∈ U) : time x = s.time x := ite_eq_left hx
  have htimeV (x : J) (hx : x ∈ V) : time x = s.length + t.time x :=
    ite_eq_right (fun hu => Set.disjoint_left.mp hd hu hx)
  refine ⟨s.length + t.length, time, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [htimeU x hx]
      have := s.bounds x hx
      omega
    · rw [htimeV x hx]
      have := t.bounds x hx
      omega
  · intro k
    by_cases hk : k ≤ s.length
    · have he : {x | x ∈ U ∪ V ∧ time x = k} = {x | x ∈ U ∧ s.time x = k} := by
        ext x
        constructor
        · rintro ⟨hx | hx, he⟩
          · exact ⟨hx, (htimeU x hx).symm.trans he⟩
          · rw [htimeV x hx] at he
            have := t.bounds x hx
            omega
        · rintro ⟨hx, he⟩
          exact ⟨Or.inl hx, (htimeU x hx).trans he⟩
      rw [he]
      exact s.capacity k
    · have he : {x | x ∈ U ∪ V ∧ time x = k} =
          {x | x ∈ V ∧ t.time x = k - s.length} := by
        ext x
        constructor
        · rintro ⟨hx | hx, he⟩
          · rw [htimeU x hx] at he
            have := s.bounds x hx
            omega
          · rw [htimeV x hx] at he
            exact ⟨hx, by omega⟩
        · rintro ⟨hx, he⟩
          refine ⟨Or.inr hx, ?_⟩
          rw [htimeV x hx, he]
          omega
      rw [he]
      exact t.capacity (k-s.length)
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · simpa only [htimeU x hx, htimeU y hy] using s.respects x hx y hy hxy
    · rw [htimeU x hx, htimeV y hy]
      have := s.bounds x hx
      have := t.bounds y hy
      omega
    · exact (hback x hx y hy hxy).elim
    · simpa only [htimeV x hx, htimeV y hy, Nat.add_lt_add_iff_left] using
        t.respects x hx y hy hxy
  · rw [Set.ncard_union_eq hd, s.size, t.size, Nat.mul_add]

end FullBlock

namespace SplitVertex
variable {W : Set J} {u v : SplitVertex r atoms W}

omit [Fintype J] in
theorem gap_subset_right (_huv : u.left ∪ u.middle.val ⊆ v.left) :
    v.left \ (u.left ∪ u.middle.val) ⊆ u.right := by
  intro x hx
  rw [u.right_eq]
  exact ⟨v.left_subset hx.1, hx.2⟩

omit [Fintype J] in
theorem left_union_gap (huv : u.left ∪ u.middle.val ⊆ v.left) :
    (u.left ∪ u.middle.val) ∪ (v.left \ (u.left ∪ u.middle.val)) = v.left := by
  ext x
  constructor
  · intro hx
    exact hx.elim (fun h => huv h) (fun h => h.1)
  · intro hx
    by_cases hu : x ∈ u.left ∪ u.middle.val
    · exact Or.inl hu
    · exact Or.inr ⟨hx, hu⟩

noncomputable def add_middle (v : SplitVertex r atoms W) (s : FullBlock r v.left) :
    FullBlock r (v.left ∪ v.middle.val) :=
  s.append (FullBlock.triple v.middle v.antichain) v.left_middle v.no_middle_left

noncomputable def advance (s : FullBlock r u.left)
    (huv : u.left ∪ u.middle.val ⊆ v.left)
    (t : FullBlock r (v.left \ (u.left ∪ u.middle.val))) : FullBlock r v.left := by
  have hd : Disjoint (u.left ∪ u.middle.val) (v.left \ (u.left ∪ u.middle.val)) := by
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have hback : ∀ x ∈ v.left \ (u.left ∪ u.middle.val),
      ∀ y ∈ u.left ∪ u.middle.val, ¬r x y := by
    intro x hx y hy
    have hxr := gap_subset_right huv hx
    exact hy.elim (u.no_right_left x hxr y) (u.no_right_middle x hxr y)
  exact left_union_gap huv ▸ (u.add_middle s).append t hd hback

noncomputable def finish (v : SplitVertex r atoms W)
    (s : FullBlock r v.left) (t : FullBlock r v.right) : FullBlock r W := by
  have hd : Disjoint (v.left ∪ v.middle.val) v.right := v.left_right.union_left v.middle_right
  have hback : ∀ x ∈ v.right, ∀ y ∈ v.left ∪ v.middle.val, ¬r x y := by
    intro x hx y hy
    exact hy.elim (v.no_right_left x hx y) (v.no_right_middle x hx y)
  have he : (v.left ∪ v.middle.val) ∪ v.right = W := by
    ext x
    simpa only [Set.mem_union, Finset.mem_coe, or_assoc] using (v.partition x).symm
  exact he ▸ (v.add_middle s).append t hd hback

end SplitVertex

end Soundness
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section AtomicFamily
variable {J : Type} [Fintype J]

inductive Atomic (J : Type) [Fintype J]
  | constant (value : Bool)
  | threshold (frame upper : Bool) (k : Fin (Fintype.card J + 2))
  | cone (frame : Bool) (kind : Fin 5) (Z : Triple J)
  deriving Fintype

namespace Atomic

def eval (r : J → J → Prop) (rank reverseRank : J → ℕ) : Atomic J → Set J
  | .constant b => if b then Set.univ else ∅
  | .threshold frame upper k =>
    let ρ := if frame then reverseRank else rank
    if upper then {x | ρ x ≤ k.val} else {x | k.val ≤ ρ x}
  | .cone frame kind Z =>
    let R := if frame then (fun x y => r y x) else r
    match kind.val with
    | 0 => Z.val
    | 1 => (Boundary.actual Z).pred R
    | 2 => (Boundary.actual Z).desc R
    | 3 => (Boundary.actual Z).weakPred R
    | _ => (Boundary.actual Z).weakDesc R

end Atomic
end AtomicFamily
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Ranks
variable {J K : Type} [Fintype J] [LinearOrder K]

def rankOfKey (key : J → K) (x : J) : ℕ :=
  (Finset.univ.filter (fun y => key y < key x)).card + 1

end Ranks

section IndexedRanks
variable {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]

def predecessorCount (x : Fin n) : ℕ := (Finset.univ.filter (fun y => r y x)).card

def jobKey (x : Fin n) : Lex (ℕ × Fin n) := toLex (predecessorCount r x, x)

def jobRank : Fin n → ℕ := rankOfKey (jobKey r)

def reverseJobRank (x : Fin n) : ℕ := n+1-jobRank r x

end IndexedRanks
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ScheduleLayouts
variable {J : Type} [Fintype J]

end ScheduleLayouts
end ThreeMachine.Structure

end

end OAI
end


section
-- module Padding
namespace OAI

section

namespace ThreeMachine

def Instance.order {n : ℕ} (G : Instance n) : Fin n → Fin n → Prop := Relation.TransGen G.edge

def paddedOrder {n : ℕ} (r : Fin n → Fin n → Prop) (m : ℕ) (u v : Fin m) : Prop :=
  ∃ x y : Fin n, u.val = x.val ∧ v.val = y.val ∧ r x y

namespace Structure

end Structure

end ThreeMachine

end

end OAI
end


section
-- module EffectiveFamily
namespace OAI

section

namespace ThreeMachine.Structure
namespace Formula
variable {A B C : Type}

def map (f : A → B) : Formula A → Formula B
  | .leaf a s => .leaf (f a) s
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)

@[simp] theorem leaves_map (f : A → B) (p : Formula A) : (p.map f).leaves = p.leaves := by
  induction p with
  | leaf => rfl
  | conj p q hp hq | disj p q hp hq => simp only [map, leaves, hp, hq]

@[simp] theorem map_comp (f : A → B) (g : B → C) (p : Formula A) :
    (p.map f).map g = p.map (g ∘ f) := by
  induction p with
  | leaf => rfl
  | conj p q hp hq | disj p q hp hq => simp only [map, hp, hq]

@[simp] theorem map_id (p : Formula A) : p.map id = p := by
  induction p with
  | leaf => rfl
  | conj p q hp hq | disj p q hp hq => simp only [map, hp, hq]

def depthEnum (alphabet : List A) : ℕ → List (Formula A)
  | 0 => []
  | n+1 => alphabet.flatMap (fun a => [.leaf a false, .leaf a true]) ++
    (depthEnum alphabet n).flatMap (fun p =>
      (depthEnum alphabet n).flatMap (fun q => [.conj p q, .disj p q]))

def templates (K : ℕ) : List (Formula (Fin K)) :=
  (depthEnum (List.finRange K) K).filter (fun p => p.leaves ≤ K)

end Formula

def assignments {A : Type} (alphabet : List A) : (k : ℕ) → List (Fin k → A)
  | 0 => [Fin.elim0]
  | k+1 => alphabet.flatMap (fun a => (assignments alphabet k).map (Fin.cons a))

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section EffectiveAlphabet
variable {J : Type} [Fintype J] [DecidableEq J]

def tripleList (jobs : List J) : List (Triple J) :=
  (jobs.flatMap (fun a => jobs.flatMap (fun b => jobs.map (fun c => ({a,b,c} : Finset J))))).filterMap
    (fun Z => if h : Z.card = 3 then some ⟨Z, h⟩ else none)

def Atomic.alphabet (jobs : List J) : List (Atomic J) :=
  [.constant false, .constant true] ++
  [false,true].flatMap (fun frame => [false,true].flatMap (fun upper =>
    (List.finRange (Fintype.card J + 2)).map (.threshold frame upper))) ++
  [false,true].flatMap (fun frame => (List.finRange 5).flatMap (fun kind =>
    (tripleList jobs).map (.cone frame kind)))

end EffectiveAlphabet
end ThreeMachine.Structure

end

end OAI
end


section
-- module DynamicProgram
namespace OAI

section

namespace ThreeMachine.Algorithm
open Structure

structure Block (J : Type) where
  length : ℕ
  time : J → ℕ

namespace Block
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

def Valid (r : J → J → Prop) (W : Finset J) (s : Block J) : Prop :=
  ∃ b : FullBlock r (W : Set J), b.length = s.length ∧ b.time = s.time

def empty : Block J := ⟨0, fun _ => 0⟩
def triple : Block J := ⟨1, fun _ => 1⟩
def append (U : Finset J) (s t : Block J) : Block J :=
  ⟨s.length + t.length, fun x => if x ∈ U then s.time x else s.length + t.time x⟩

end Block

structure State (J : Type) where
  left : Finset J
  middle : Finset J
  right : Finset J
  deriving DecidableEq

namespace State
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

def candidate (W F Z : Finset J) : State J :=
  ⟨W ∩ F, Z, W \ ((W ∩ F) ∪ Z)⟩

def Compatible (r : J → J → Prop) (W : Finset J) (s : State J) : Prop :=
  (s.left ∪ s.middle) ∪ s.right = W ∧
  Disjoint s.left s.middle ∧ Disjoint s.left s.right ∧ Disjoint s.middle s.right ∧
  s.middle.card = 3 ∧
  (∀ x ∈ s.middle, ∀ y ∈ s.middle, ¬r x y) ∧
  (∀ x ∈ s.middle, ∀ y ∈ s.left, ¬r x y) ∧
  (∀ x ∈ s.right, ∀ y ∈ s.left, ¬r x y) ∧
  (∀ x ∈ s.right, ∀ y ∈ s.middle, ¬r x y)

instance [DecidableRel r] (W : Finset J) (s : State J) : Decidable (s.Compatible r W) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def upto (s : State J) : Finset J := s.left ∪ s.middle

def advance (u : State J) (s t : Block J) : Block J :=
  Block.append u.upto (Block.append u.left s Block.triple) t

def finish (u : State J) (s t : Block J) : Block J := advance u s t

end State
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm

def lookup {K V : Type} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (a,b)::xs, k => if a = k then some b else lookup xs k

def Has {K V : Type} [DecidableEq K] (tab : List (K × V)) (k : K) : Prop :=
  ∃ v, lookup tab k = some v

def firstResult {K V : Type} (f : K → Option V) : List K → Option V
  | [] => none
  | k::ks => match f k with
    | some v => some v
    | none => firstResult f ks

def tableOf {K V : Type} (ks : List K) (f : K → Option V) : List (K × V) :=
  ks.filterMap (fun k => (f k).map (fun v => (k,v)))

inductive Walk {K : Type} (r : K → K → Prop) : ℕ → K → K → Prop
  | refl (a : K) : Walk r 0 a a
  | tail {n a b c} : Walk r n a b → r b c → Walk r (n+1) a c

namespace Walk
variable {K : Type} {r : K → K → Prop}

end Walk
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
section DynamicProgram
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

def states (family triples : List (Finset J)) (W : Finset J) : List (State J) :=
  (family.flatMap (fun F => triples.map (State.candidate W F))).filter (fun s => s.Compatible r W)

def tryAdvance (tab : List (Finset J × Block J)) (u : State J × Block J)
    (v : State J) : Option (Block J) :=
  if u.1.upto ⊆ v.left then (lookup tab (v.left \ u.1.upto)).map (u.1.advance u.2) else none

def expand (tab : List (Finset J × Block J)) (sts : List (State J))
    (marks : List (State J × Block J)) : List (State J × Block J) :=
  tableOf sts (fun v => match lookup marks v with
    | some s => some s
    | none => firstResult (fun u => tryAdvance tab u v) marks)

def markings (tab : List (Finset J × Block J)) (sts : List (State J)) :
    ℕ → List (State J × Block J)
  | 0 => tableOf sts (fun v => lookup tab v.left)
  | k+1 => expand tab sts (markings tab sts k)

def solve (tab : List (Finset J × Block J)) (family triples : List (Finset J))
    (W : Finset J) : Option (Block J) :=
  if W = ∅ then some Block.empty else
    firstResult (fun v => (lookup tab v.1.right).map (v.1.finish v.2))
      (markings tab (states r family triples W) (Fintype.card J))

def layers (family triples : List (Finset J)) : ℕ → List (Finset J × Block J)
  | 0 => [(∅, Block.empty)]
  | k+1 => tableOf family (solve r (layers family triples k) family triples)

def TableGood (tab : List (Finset J × Block J)) : Prop :=
  ∀ W s, (W,s) ∈ tab → s.Valid r W

def MarksGood (W : Finset J) (marks : List (State J × Block J)) : Prop :=
  ∀ u s, (u,s) ∈ marks → u.Compatible r W ∧ s.Valid r u.left

def Arc (tab : List (Finset J × Block J)) (sts : List (State J)) (u v : State J) : Prop :=
  u ∈ sts ∧ v ∈ sts ∧ u.upto ⊆ v.left ∧ Has tab (v.left \ u.upto)

end DynamicProgram
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
open scoped Classical
section EraseSplits
variable {J A : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}
    {atoms : A → Set J} {W : Set J}

omit [Fintype J] [DecidableEq J] in
@[ext] theorem State.ext {u v : State J} (hL : u.left = v.left)
    (hM : u.middle = v.middle) (hR : u.right = v.right) : u = v := by
  cases u
  cases v
  cases hL
  cases hM
  cases hR
  rfl

noncomputable def State.erase (v : SplitVertex r atoms W) : State J :=
  ⟨v.left.toFinset, v.middle.val, v.right.toFinset⟩

end EraseSplits

section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]
    (atoms : A → Set J) (family triples : List (Finset J))
    (hfamily : ∀ F, Described atoms F 10000 → F.toFinset ∈ family)
    (htriples : ∀ Z : Triple J, Z.val ∈ triples)

end Completeness
end ThreeMachine.Algorithm

end

end OAI
end


section
-- module SchedulingAlgorithm
namespace OAI

section

namespace ThreeMachine.Algorithm
section Closure
variable {n : ℕ}

def closureStep (E R : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  R ∪ Finset.univ.filter (fun p => ∃ v : Fin n, (p.1,v) ∈ R ∧ (v,p.2) ∈ E)

def closureTable (G : Instance n) (k : ℕ) : Finset (Fin n × Fin n) :=
  (closureStep G.edges.toFinset)^[k] G.edges.toFinset

def reachable (G : Instance n) (x y : Fin n) : Prop := (x,y) ∈ closureTable G n

instance (G : Instance n) : DecidableRel (reachable G) := fun x y =>
  inferInstanceAs (Decidable ((x,y) ∈ closureTable G n))

@[simp] theorem closureTable_zero (G : Instance n) : closureTable G 0 = G.edges.toFinset := rfl
@[simp] theorem closureTable_succ (G : Instance n) (k : ℕ) :
    closureTable G (k+1) = closureStep G.edges.toFinset (closureTable G k) :=
  Function.iterate_succ_apply' _ _ _

end Closure
end ThreeMachine.Algorithm

namespace ThreeMachine.Structure
section EffectiveFamily
variable {J : Type} [Fintype J] [DecidableEq J]

def Atomic.finsetEval (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) : Atomic J → Finset J
  | .constant b => if b then Finset.univ else ∅
  | .threshold frame upper k =>
    let ρ := if frame then reverseRank else rank
    Finset.univ.filter (fun x => if upper then ρ x ≤ k.val else k.val ≤ ρ x)
  | .cone frame kind Z =>
    let R := fun x y => if frame then r y x else r x y
    letI : DecidableRel R := fun x y => inferInstanceAs (Decidable (if frame then r y x else r x y))
    match kind.val with
    | 0 => Z.val
    | 1 => Finset.univ.filter (fun x => ∃ y ∈ Z.val, R x y)
    | 2 => Finset.univ.filter (fun x => ∃ y ∈ Z.val, R y x)
    | 3 => (Finset.univ.filter (fun x => ∃ y ∈ Z.val, R x y)) ∪ Z.val
    | _ => (Finset.univ.filter (fun x => ∃ y ∈ Z.val, R y x)) ∪ Z.val

theorem Atomic.coe_finsetEval (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (a : Atomic J) :
    (finsetEval r rank reverseRank a : Set J) = eval r rank reverseRank a := by
  cases a with
  | constant b => cases b <;> simp [finsetEval,eval]
  | threshold frame upper k =>
    cases frame <;> cases upper <;> ext x <;> simp [finsetEval,eval]
  | cone frame kind Z =>
    fin_cases kind <;> cases frame <;> ext x <;>
      simp [finsetEval,eval,Boundary.pred,Boundary.desc,Boundary.weakPred,Boundary.weakDesc]

instance Atomic.decideEval (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (a : Atomic J) : DecidablePred (eval r rank reverseRank a) :=
  fun x => decidable_of_iff (x ∈ finsetEval r rank reverseRank a) (by
    change x ∈ (finsetEval r rank reverseRank a : Set J) ↔ _
    rw [coe_finsetEval]
    rfl)

def Formula.evalFinset {A : Type} (atoms : A → Finset J) : Formula A → Finset J
  | .leaf a b => if b then (atoms a)ᶜ else atoms a
  | .conj p q => p.evalFinset atoms ∩ q.evalFinset atoms
  | .disj p q => p.evalFinset atoms ∪ q.evalFinset atoms

def effectiveFamily (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (jobs : List J) (K : ℕ) : List (Finset J) :=
  (assignments (Atomic.alphabet jobs) K).flatMap (fun f =>
    (Formula.templates K).map (fun s =>
      (s.map f).evalFinset (fun a => Finset.univ.filter (Atomic.eval r rank reverseRank a))))

end EffectiveFamily
end ThreeMachine.Structure

namespace ThreeMachine
instance {n m : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r] :
    DecidableRel (paddedOrder r m) := fun x y =>
  inferInstanceAs (Decidable (∃ a b : Fin n, x.val = a.val ∧ y.val = b.val ∧ r a b))
end ThreeMachine

namespace ThreeMachine.Algorithm
open Structure

def fullSolve {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r] : Option (Block (Fin m)) :=
  lookup (layers r
    (effectiveFamily r (jobRank r) (reverseJobRank r) (List.finRange m) 10000)
    ((tripleList (List.finRange m)).map Subtype.val) m) Finset.univ

def scheduleAt {n : ℕ} (G : Instance n) (T : ℕ) : Option (Fin n → ℕ) :=
  if hn : n ≤ 3*T then
    (fullSolve (paddedOrder (reachable G) (3*T))).map
      (fun s x => s.time (Fin.castLE hn x))
  else none

end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure

def best {n : ℕ} (G : Instance n) : ℕ → Option (ℕ × (Fin n → ℕ))
  | 0 => none
  | k+1 => match best G k with
    | some a => some a
    | none => (scheduleAt G (k+1)).map (fun time => (k+1,time))

def BestSpec {n : ℕ} (G : Instance n) (k : ℕ) : Option (ℕ × (Fin n → ℕ)) → Prop
  | none => ∀ T, 1 ≤ T → T ≤ k → ¬∃ time, Feasible G T time
  | some (T,time) => 1 ≤ T ∧ T ≤ k ∧ Feasible G T time ∧
      ∀ T' time', 1 ≤ T' → T' ≤ k → Feasible G T' time' → T ≤ T'

def output {n : ℕ} (G : Instance n) : Option ℕ → List Bool
  | some T => encodeAnswer ((scheduleAt G T).map slots)
  | none => encodeAnswer ((best G n).map (fun a => slots a.2))

end ThreeMachine.Algorithm

end

end OAI
end


section
-- module StackMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

inductive Action
  | stay
  | pop
  | push (b : Bool)
  deriving DecidableEq, Fintype

def Action.apply : Action → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

abbrev Store (k : ℕ) := Fin (k+1) → List Bool
abbrev Heads (k : ℕ) := Fin (k+1) → Option Bool
abbrev Actions (k : ℕ) := Fin (k+1) → Action

structure Program (k : ℕ) (Q : Type) where
  initial : Q
  transition : Q → Heads k → Option (Q × Actions k)

structure State (k : ℕ) (Q : Type) where
  control : Q
  store : Store k

def Program.step {k Q} (P : Program k Q) (c : State k Q) : Option (State k Q) := do
  let (q,a) ← P.transition c.control (fun i => (c.store i).head?)
  return ⟨q, fun i => (a i).apply (c.store i)⟩

def Program.run {k Q} (P : Program k Q) (s : Store k) (t : ℕ) : State k Q :=
  (fun c => (P.step c).getD c)^[t] ⟨P.initial,s⟩

def Program.Computes {k Q} (P : Program k Q) (s t : Store k) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, (P.run s n).store = t ∧ P.step (P.run s n) = none

def symbol (b : Bool) : Fin 3 := bitSymbol b

def unsymbol (a : Fin 3) : Option Bool :=
  if a = 0 then none else some (a = 2)

@[simp] theorem unsymbol_symbol (b : Bool) : unsymbol (symbol b) = some b := by
  cases b <;> decide

@[simp] theorem unsymbol_zero : unsymbol 0 = none := rfl

def stackTape (xs : List Bool) : Turing.Tape (Fin 3) :=
  Turing.Tape.mk₁ (xs.map symbol)

def phaseOne (a : Action) (head : Fin 3) : Fin 3 × Option Turing.Dir :=
  match a with
  | .stay => (head,none)
  | .pop => (0,some .right)
  | .push _ => (head,some .left)

def phaseTwo (a : Action) (head : Fin 3) : Fin 3 × Option Turing.Dir :=
  match a with
  | .push b => (symbol b,none)
  | _ => (head,none)

def applyTape (a : Fin 3 × Option Turing.Dir) (t : Turing.Tape (Fin 3)) :
    Turing.Tape (Fin 3) :=
  match a.2 with
  | none => t.write a.1
  | some d => (t.write a.1).move d

def middleTape (a : Action) (xs : List Bool) : Turing.Tape (Fin 3) :=
  applyTape (phaseOne a (stackTape xs).head) (stackTape xs)

@[simp] theorem blank_cons :
    (Turing.ListBlank.mk ([] : List (Fin 3))).cons 0 = Turing.ListBlank.mk [] := by
  exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])

abbrev Control (k : ℕ) (Q : Type) := Q ⊕ (Q × Actions k)

section Compilation
variable {k : ℕ} {Q : Type} [Fintype Q] (P : Program k Q)

noncomputable def numberControl (q : Control k Q) : Fin (Fintype.card (Control k Q) + 1) :=
  (Fintype.equivFin (Control k Q) q).succ

noncomputable def readControl (i : Fin (Fintype.card (Control k Q) + 1)) : Control k Q :=
  if h : i.val = 0 then .inl P.initial else
    (Fintype.equivFin (Control k Q)).symm ⟨i.val-1, by have := i.isLt; omega⟩

@[simp] theorem read_numberControl (q : Control k Q) : readControl P (numberControl q) = q := by
  simp [readControl, numberControl]

@[simp] theorem read_zero : readControl P 0 = .inl P.initial := by
  simp [readControl]

noncomputable def compile : Machine k (Fintype.card (Control k Q)) 0 where
  transition i heads :=
    match readControl P i with
    | .inl q => (P.transition q (fun j => unsymbol (heads j))).map
        (fun qa => (numberControl (.inr qa), fun j => phaseOne (qa.2 j) (heads j)))
    | .inr qa => some (numberControl (.inl qa.1), fun j => phaseTwo (qa.2 j) (heads j))

abbrev TapeCfg := Configuration k (Fintype.card (Control k Q)) 0

def Relates (c : TapeCfg (k := k) (Q := Q)) (s : State k Q) : Prop :=
  readControl P c.state = .inl s.control ∧ ∀ j, c.tapes j = stackTape (s.store j)

noncomputable def middleCfg (qa : Q × Actions k) (s : Store k) : TapeCfg (k := k) (Q := Q) :=
  ⟨numberControl (.inr qa), fun j => middleTape (qa.2 j) (s j)⟩

noncomputable def readyCfg (s : State k Q) : TapeCfg (k := k) (Q := Q) :=
  ⟨numberControl (.inl s.control), fun j => stackTape (s.store j)⟩

@[simp] theorem relates_ready (s : State k Q) : Relates P (readyCfg s) s :=
  ⟨read_numberControl P _, fun _ => rfl⟩

def initialStore (input : List Bool) : Store k := fun i => if i = 0 then input else []

end Compilation
namespace Program
variable {k : ℕ} {Q R S : Type}

inductive Exec (P : Program k Q) : State k Q → ℕ → State k Q → Prop
  | halt {s} : P.step s = none → Exec P s 0 s
  | next {s t u n} : P.step s = some t → Exec P t n u → Exec P s (n+1) u

def State.mapControl (f : Q → R) (s : State k Q) : State k R := ⟨f s.control,s.store⟩

def stayActions : Actions k := fun _ => .stay

def seq (P : Program k Q) (P' : Program k R) : Program k (Q ⊕ R) where
  initial := .inl P.initial
  transition q heads := match q with
    | .inl q => match P.transition q heads with
      | none => some (.inr P'.initial,stayActions)
      | some qa => some (.inl qa.1,qa.2)
    | .inr q => (P'.transition q heads).map (fun qa => (.inr qa.1,qa.2))

def instruction (a : Heads k → Actions k) : Program k Bool where
  initial := false
  transition q h := if q then none else some (true,a h)

def loop (test : Heads k → Bool) (P : Program k Q) : Program k (Option Q) where
  initial := none
  transition q h := match q with
    | none => if test h then some (some P.initial,stayActions) else none
    | some q => match P.transition q h with
      | none => some (none,stayActions)
      | some qa => some (some qa.1,qa.2)

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Program
variable {k : ℕ}

def transferActions (src dst : Fin (k+1)) (h : Heads k) : Actions k := fun i =>
  if i = src then .pop else if i = dst then .push ((h src).getD false) else .stay

def transfer (src dst : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h src).isSome) (instruction (transferActions src dst))

def transferResult (src dst : Fin (k+1)) (s : Store k) : Store k :=
  Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)

def transferOnce (src dst : Fin (k+1)) (b : Bool) (xs : List Bool) (s : Store k) : Store k :=
  Function.update (Function.update s src xs) dst (b :: s dst)

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

def popActions (src : Fin (k+1)) : Actions k := fun i => if i = src then .pop else .stay

def clear (src : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h src).isSome) (instruction (fun _ => popActions src))

def spreadActions (src dst₁ dst₂ : Fin (k+1)) (h : Heads k) : Actions k := fun i =>
  if i = src then .pop else if i = dst₁ ∨ i = dst₂ then .push ((h src).getD false) else .stay

def spread (src dst₁ dst₂ : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h src).isSome) (instruction (spreadActions src dst₁ dst₂))

def spreadResult (src dst₁ dst₂ : Fin (k+1)) (s : Store k) : Store k :=
  Function.update (Function.update (Function.update s src [])
    dst₁ ((s src).reverse ++ s dst₁)) dst₂ ((s src).reverse ++ s dst₂)

def spreadOnce (src dst₁ dst₂ : Fin (k+1)) (b : Bool) (xs : List Bool) (s : Store k) : Store k :=
  Function.update (Function.update (Function.update s src xs) dst₁ (b :: s dst₁)) dst₂ (b :: s dst₂)

def prepend (src dst tmp : Fin (k+1)) : Program k (Option Bool ⊕ Option Bool) :=
  seq (transfer src tmp) (spread tmp src dst)

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

def copy (src dst tmp : Fin (k+1)) : Program k (Option Bool ⊕ (Option Bool ⊕ Option Bool)) :=
  seq (clear dst) (prepend src dst tmp)

end ThreeMachine.StackCompiler.Program

end

end OAI
end


section
-- module TreeData
namespace OAI

section

namespace ThreeMachine.StackCompiler

inductive Data
  | nil
  | pair (head tail : Data)
  deriving DecidableEq

namespace Data

def encode : Data → List Bool
  | .nil => [false]
  | .pair a b => true :: a.encode ++ b.encode

def size (d : Data) : ℕ := d.encode.length

@[simp] theorem encode_nil : encode nil = [false] := rfl
@[simp] theorem encode_pair (a b : Data) : encode (pair a b) = true :: a.encode ++ b.encode := rfl
@[simp] theorem size_nil : size nil = 1 := rfl
@[simp] theorem size_pair (a b : Data) : size (pair a b) = a.size + b.size + 1 := by
  simp [size,encode,Nat.add_comm]

def head : Data → Data | .nil => .nil | .pair a _ => a
def tail : Data → Data | .nil => .nil | .pair _ b => b

end Data

namespace Program
variable {k : ℕ}

def scanActions (src dst ct : Fin (k+1)) (h : Heads k) : Actions k := fun i =>
  if i = src then .pop else if i = dst then .push ((h src).getD false)
  else if i = ct then if (h src).getD false then .push true else .pop else .stay

def scan (src dst ct : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h ct).isSome) (instruction (scanActions src dst ct))

def scanned (src dst ct : Fin (k+1)) (s : Store k) (rest word : List Bool) (c : ℕ) : Store k :=
  Function.update (Function.update (Function.update s src rest) dst (word.reverse ++ s dst))
    ct (List.replicate c true)

def scanOnce (src dst ct : Fin (k+1)) (s : Store k) (b : Bool) (rest : List Bool) : Store k :=
  Function.update (Function.update (Function.update s src rest) dst (b :: s dst))
    ct (if b then true :: s ct else (s ct).tail)

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q R : Type}

def Runs (P : Program k Q) (s t : Store k) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, ∃ q, Exec P ⟨P.initial,s⟩ n ⟨q,t⟩

def branch (test : Heads k → Bool) (P : Program k Q) (P' : Program k R) :
    Program k (Option (Q ⊕ R)) where
  initial := none
  transition q h := match q with
    | none => some (some (if test h then .inl P.initial else .inr P'.initial),stayActions)
    | some (.inl q) => (P.transition q h).map (fun qa => (some (.inl qa.1),qa.2))
    | some (.inr q) => (P'.transition q h).map (fun qa => (some (.inr qa.1),qa.2))

def move (src dst tmp : Fin (k+1)) : Program k (Option Bool ⊕ (Option Bool ⊕ Option Bool)) :=
  seq (clear dst) (seq (transfer src tmp) (transfer tmp dst))

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

def push (dst : Fin (k+1)) (b : Bool) : Program k Bool :=
  instruction (fun _ i => if i = dst then .push b else .stay)

def setNil (dst : Fin (k+1)) := seq (clear dst) (push dst false)

def setPair (dst a b tmp buf : Fin (k+1)) :=
  seq (prepend b tmp buf) (seq (prepend a tmp buf)
    (seq (push tmp true) (move tmp dst buf)))

end ThreeMachine.StackCompiler.Program

end

end OAI
end


section
-- module RegisterMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

structure Packed (k : ℕ) where
  Control : Type
  finiteControl : Fintype Control
  program : Program k Control

attribute [instance] Packed.finiteControl

namespace Packed
variable {k : ℕ}

def ofProgram {Q : Type} [Fintype Q] (p : Program k Q) : Packed k := ⟨Q,inferInstance,p⟩
def seq (P P' : Packed k) : Packed k := ofProgram (Program.seq P.program P'.program)
def branch (test : Heads k → Bool) (P P' : Packed k) : Packed k :=
  ofProgram (Program.branch test P.program P'.program)
def loop (test : Heads k → Bool) (P : Packed k) : Packed k :=
  ofProgram (Program.loop test P.program)

def Runs (P : Packed k) := P.program.Runs

end Packed

namespace Tree
variable {r : ℕ}
abbrev Registers (r : ℕ) := Fin r → Data

def reg (i : Fin r) : Fin (r+4) := i.castAdd 4
def temp (i : Fin 4) : Fin (r+4) := i.natAdd r

def memory (s : Registers r) : Store (r+3) :=
  Fin.append (m := r) (n := 4) (fun i : Fin r => (s i).encode) (fun _ : Fin 4 => [])

@[simp] theorem memory_reg (s : Registers r) (i : Fin r) : memory s (reg i) = (s i).encode :=
  Fin.append_left _ _ _
@[simp] theorem memory_temp (s : Registers r) (i : Fin 4) : memory s (temp i) = [] :=
  Fin.append_right _ _ _
@[simp] theorem reg_ne_temp (i : Fin r) (j : Fin 4) : reg i ≠ temp j := by
  intro he
  have hv := congrArg Fin.val he
  simp only [reg,temp,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
@[simp] theorem temp_ne_reg (i : Fin r) (j : Fin 4) : temp j ≠ reg i := (reg_ne_temp i j).symm
@[simp] theorem reg_eq_reg (i j : Fin r) : reg i = reg j ↔ i = j := Fin.castAdd_inj
@[simp] theorem temp_eq_temp (i j : Fin 4) : (temp i : Fin (r+4)) = temp j ↔ i = j := Fin.natAdd_inj r

def nil (dst : Fin r) : Packed (r+3) := Packed.ofProgram (Program.setNil (reg dst))
def pair (dst a b : Fin r) : Packed (r+3) :=
  Packed.ofProgram (Program.setPair (reg dst) (reg a) (reg b) (temp 0) (temp 1))

end Tree
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

def work (s : Registers r) (t : Fin 4 → List Bool) : Store (r+3) :=
  Fin.append (m := r) (n := 4) (fun i : Fin r => (s i).encode) t

@[simp] theorem work_reg (s : Registers r) (t : Fin 4 → List Bool) (i : Fin r) :
    work s t (reg i) = (s i).encode := Fin.append_left _ _ _
@[simp] theorem work_temp (s : Registers r) (t : Fin 4 → List Bool) (i : Fin 4) :
    work s t (temp i) = t i := Fin.append_right _ _ _

@[simp] theorem work_empty (s : Registers r) : work s ![[],[],[],[]] = memory s := by
  have he : (![[],[],[],[]] : Fin 4 → List Bool) = fun _ => [] := by
    funext i; fin_cases i <;> rfl
  simp only [work,memory,he]

def selectFinish (head : Bool) : Packed (r+3) :=
  if head then Packed.ofProgram (Program.seq (Program.clear (temp 0)) (Program.transfer (temp 2) (temp 0)))
  else Packed.ofProgram (Program.seq (Program.clear (temp 2)) (Program.clear (temp 2)))

def selectPair (head : Bool) (dst : Fin r) : Packed (r+3) :=
  (Packed.ofProgram (Program.instruction (fun _ => Program.popActions (temp 0)))).seq
  ((Packed.ofProgram (Program.push (temp 3) true)).seq
  ((Packed.ofProgram (Program.scan (temp 0) (temp 2) (temp 3))).seq
  ((selectFinish head).seq (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1))))))

def selectAux (head : Bool) (dst : Fin r) : Packed (r+3) :=
  Packed.branch (fun h => (h (temp 0)).getD false) (selectPair head dst)
    (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1)))

def select (head : Bool) (dst src : Fin r) : Packed (r+3) :=
  (Packed.ofProgram (Program.copy (reg src) (temp 0) (temp 1))).seq (selectAux head dst)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q : Type}

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

def skip : Packed (r+3) := Packed.ofProgram (Program.instruction (fun _ => Program.stayActions))

def copy (dst src : Fin r) : Packed (r+3) :=
  if dst = src then skip else Packed.ofProgram (Program.copy (reg src) (reg dst) (temp 0))

inductive Code (V : Type)
  | skip
  | nil (dst : V)
  | pair (dst a b : V)
  | select (head : Bool) (dst src : V)
  | copy (dst src : V)
  | seq (first second : Code V)
  | branch (src : V) (nonempty empty : Code V)
  | loop (src : V) (body : Code V)

def _root_.OAI.ThreeMachine.StackCompiler.Data.nonempty : Data → Bool | .nil => false | .pair _ _ => true

@[simp] theorem _root_.OAI.ThreeMachine.StackCompiler.Data.encode_head (d : Data) : d.encode.head?.getD false = d.nonempty := by
  cases d <;> rfl

inductive Eval {V : Type} [DecidableEq V] : Code V → (V → Data) → (V → Data) → ℕ → Prop
  | skip (s) : Eval .skip s s 1
  | nil (dst) (s) : Eval (.nil dst) s (Function.update s dst .nil) (1+(s dst).size)
  | pair (dst a b) (s) : Eval (.pair dst a b) s (Function.update s dst (.pair (s a) (s b))) (1+(s dst).size+(s a).size+(s b).size)
  | select (head dst src) (s) :
      Eval (.select head dst src) s (Function.update s dst (if head then (s src).head else (s src).tail)) (1+(s dst).size+(s src).size)
  | copy (dst src) (s) : Eval (.copy dst src) s (Function.update s dst (s src)) (1+(s dst).size+(s src).size)
  | seq {p q s t u n m} : Eval p s t n → Eval q t u m → Eval (.seq p q) s u (n+m+1)
  | branch_true {src p q s t n} : (s src).nonempty = true → Eval p s t n → Eval (.branch src p q) s t (n+1)
  | branch_false {src p q s t n} : (s src).nonempty = false → Eval q s t n → Eval (.branch src p q) s t (n+1)
  | loop_stop {src p s} : (s src).nonempty = false → Eval (.loop src p) s s 1
  | loop_step {src p s t u n m} : (s src).nonempty = true → Eval p s t n →
      Eval (.loop src p) t u m → Eval (.loop src p) s u (n+m+1)

namespace Code

def compile : Code (Fin r) → Packed (r+3)
  | .skip => Tree.skip
  | .nil dst => Tree.nil dst
  | .pair dst a b => Tree.pair dst a b
  | .select head dst src => Tree.select head dst src
  | .copy dst src => Tree.copy dst src
  | .seq p q => p.compile.seq q.compile
  | .branch src p q => Packed.branch (fun h => (h (reg src)).getD false) p.compile q.compile
  | .loop src p => Packed.loop (fun h => (h (reg src)).getD false) p.compile

end Code

end ThreeMachine.StackCompiler.Tree

end

end OAI
end


section
-- module RoutineCompiler
namespace OAI

section

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def Code.rename (f : V → W) : Code V → Code W
  | .skip => .skip
  | .nil dst => .nil (f dst)
  | .pair dst a b => .pair (f dst) (f a) (f b)
  | .select head dst src => .select head (f dst) (f src)
  | .copy dst src => .copy (f dst) (f src)
  | .seq p q => .seq (p.rename f) (q.rename f)
  | .branch src p q => .branch (f src) (p.rename f) (q.rename f)
  | .loop src p => .loop (f src) (p.rename f)

noncomputable def overlay (f : V → W) (s : V → Data) (base : W → Data) : W → Data :=
  Function.extend f s base

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_apply {f : V → W} (hf : Function.Injective f) (s : V → Data) (base : W → Data) (i : V) :
    overlay f s base (f i) = s i := hf.extend_apply s base i

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_out {f : V → W} (s : V → Data) (base : W → Data) {j : W} (hj : ¬∃ i, f i = j) :
    overlay f s base j = base j := Function.extend_apply' s base j hj

theorem overlay_update {f : V → W} (hf : Function.Injective f) (s : V → Data) (base : W → Data)
    (i : V) (d : Data) :
    overlay f (Function.update s i d) base = Function.update (overlay f s base) (f i) d := by
  funext j
  by_cases hj : ∃ a, f a = j
  · obtain ⟨a,rfl⟩ := hj
    by_cases ha : a = i <;> simp [overlay_apply hf,ha,hf.eq_iff]
  · have hn : j ≠ f i := fun h => hj ⟨i,h.symm⟩
    rw [overlay_out _ _ hj,Function.update_of_ne hn,overlay_out _ _ hj]

theorem Eval.rename {p : Code V} {s t : V → Data} {n : ℕ} (h : Eval p s t n)
    {f : V → W} (hf : Function.Injective f) (base : W → Data) :
    Eval (p.rename f) (overlay f s base) (overlay f t base) n := by
  induction h with
  | skip s => exact Eval.skip _
  | nil dst s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.nil (f dst) (overlay f s base)
  | pair dst a b s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.pair (f dst) (f a) (f b) (overlay f s base)
  | select head dst src s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.select head (f dst) (f src) (overlay f s base)
  | copy dst src s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.copy (f dst) (f src) (overlay f s base)
  | seq _ _ ih ih' => exact Eval.seq ih ih'
  | branch_true hs _ ih => exact Eval.branch_true (by simpa only [overlay_apply hf] using hs) ih
  | branch_false hs _ ih => exact Eval.branch_false (by simpa only [overlay_apply hf] using hs) ih
  | loop_stop hs => exact Eval.loop_stop (by simpa only [overlay_apply hf] using hs)
  | loop_step hs _ _ ih ih' => exact Eval.loop_step (by simpa only [overlay_apply hf] using hs) ih ih'

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def Bounded (p : Code V) (s t : V → Data) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, Eval p s t n

theorem Eval.bounded {p : Code V} {s t : V → Data} {n : ℕ} (h : Eval p s t n) : Bounded p s t n :=
  ⟨n,le_rfl,h⟩

theorem Bounded.mono {p : Code V} {s t : V → Data} {n m : ℕ} (h : Bounded p s t n) (h' : n ≤ m) :
    Bounded p s t m := by
  obtain ⟨a,ha,he⟩ := h
  exact ⟨a,ha.trans h',he⟩

theorem Bounded.seq {p q : Code V} {s t u : V → Data} {n m : ℕ}
    (h : Bounded p s t n) (h' : Bounded q t u m) : Bounded (.seq p q) s u (n+m+1) := by
  obtain ⟨a,ha,he⟩ := h
  obtain ⟨b,hb,he'⟩ := h'
  exact ⟨a+b+1,by omega,Eval.seq he he'⟩

def join (s : V → Data) (t : W → Data) : V ⊕ W → Data := Sum.elim s t

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem join_inl (s : V → Data) (t : W → Data) (i : V) : join s t (.inl i) = s i := rfl
omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem join_inr (s : V → Data) (t : W → Data) (i : W) : join s t (.inr i) = t i := rfl

theorem join_update_left (s : V → Data) (t : W → Data) (i : V) (d : Data) :
    Function.update (join s t) (.inl i) d = join (Function.update s i d) t := by
  funext j
  cases j with
  | inl j => by_cases hj : j = i <;> simp [hj]
  | inr j => simp

theorem join_update_right (s : V → Data) (t : W → Data) (i : W) (d : Data) :
    Function.update (join s t) (.inr i) d = join s (Function.update t i d) := by
  funext j
  cases j with
  | inl j => simp
  | inr j => by_cases hj : j = i <;> simp [hj]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_left (s s' : V → Data) (t : W → Data) : overlay Sum.inl s (join s' t) = join s t := by
  funext j
  cases j with
  | inl j => exact overlay_apply Sum.inl_injective _ _ _
  | inr j => exact overlay_out _ _ (by simp)

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_right (s : V → Data) (t t' : W → Data) : overlay Sum.inr t (join s t') = join s t := by
  funext j
  cases j with
  | inl j => exact overlay_out _ _ (by simp)
  | inr j => exact overlay_apply Sum.inr_injective _ _ _

theorem Bounded.left {p : Code V} {s t : V → Data} {n : ℕ}
    (h : Bounded p s t n) (u : W → Data) : Bounded (p.rename Sum.inl) (join s u) (join t u) n := by
  obtain ⟨m,hm,he⟩ := h
  refine ⟨m,hm,?_⟩
  simpa only [overlay_left] using he.rename Sum.inl_injective (join s u)

theorem Bounded.right {p : Code W} {s t : W → Data} {n : ℕ}
    (h : Bounded p s t n) (u : V → Data) : Bounded (p.rename Sum.inr) (join u s) (join u t) n := by
  obtain ⟨m,hm,he⟩ := h
  refine ⟨m,hm,?_⟩
  simpa only [overlay_right] using he.rename Sum.inr_injective (join u s)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

def zeroStore (V : Type) : V → Data := fun _ => .nil

def start {V : Type} [DecidableEq V] (input : V) (x : Data) : V → Data :=
  Function.update (zeroStore V) input x

def finish {V : Type} [DecidableEq V] (input output : V) (x y : Data) : V → Data :=
  Function.update (start input x) output y

structure Routine (f : Data → Data) (charge : Data → ℕ) where
  Vars : Type
  finiteVars : Fintype Vars
  decVars : DecidableEq Vars
  input : Vars
  output : Vars
  distinct : input ≠ output
  code : Code Vars
  correct : ∀ x, Bounded code (start input x) (finish input output x (f x)) (charge x)

attribute [instance] Routine.finiteVars Routine.decVars

namespace Routine
variable {f g : Data → Data} {charge charge' : Data → ℕ}

def mono (R : Routine f charge) (h : ∀ x, charge x ≤ charge' x) : Routine f charge' :=
  { R with correct := fun x => (R.correct x).mono (h x) }

def identity : Routine id (fun x => x.size+2) where
  Vars := Bool
  finiteVars := inferInstance
  decVars := inferInstance
  input := false
  output := true
  distinct := by decide
  code := .copy true false
  correct x := by
    simpa [finish,start,zeroStore,Nat.add_comm] using (Eval.copy true false (start false x)).bounded

def nil : Routine (fun _ => Data.nil) (fun _ => 2) where
  Vars := Bool
  finiteVars := inferInstance
  decVars := inferInstance
  input := false
  output := true
  distinct := by decide
  code := .nil true
  correct x := by
    simpa [finish,start,zeroStore] using (Eval.nil true (start false x)).bounded

def select (head : Bool) : Routine (fun x => if head then x.head else x.tail) (fun x => x.size+2) where
  Vars := Bool
  finiteVars := inferInstance
  decVars := inferInstance
  input := false
  output := true
  distinct := by decide
  code := .select head true false
  correct x := by
    simpa [finish,start,zeroStore,Nat.add_comm] using (Eval.select head true false (start false x)).bounded

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

@[simp] theorem start_input (input : V) (x : Data) : start input x input = x := by simp [start]
@[simp] theorem start_other {input i : V} (x : Data) (hi : i ≠ input) : start input x i = .nil := by simp [start,hi,zeroStore]
@[simp] theorem finish_output (input output : V) (x y : Data) : finish input output x y output = y := by simp [finish]
@[simp] theorem finish_input {input output : V} (h : input ≠ output) (x y : Data) : finish input output x y input = x := by simp [finish,start,h]

theorem start_left (input : V) (x : Data) :
    start (Sum.inl input : V ⊕ W) x = join (start input x) (zeroStore W) := by
  funext j
  cases j with
  | inl j => by_cases hj : j = input <;> simp [hj,start,zeroStore]
  | inr j => simp [start,zeroStore]

theorem finish_lr (input : V) (output : W) (x y : Data) :
    finish (Sum.inl input) (Sum.inr output) x y = join (start input x) (start output y) := by
  rw [finish,start_left,join_update_right]
  rfl

theorem reset_output {input output : V} (h : input ≠ output) (x y : Data) :
    Function.update (finish input output x y) output .nil = start input x := by
  have he : start input x output = .nil := start_other x h.symm
  rw [finish,Function.update_idem,← he,Function.update_eq_self]

theorem reset_input {input output : V} (h : input ≠ output) (x y : Data) :
    Function.update (finish input output x y) input .nil = start output y := by
  funext i
  by_cases hi : i = input
  · subst i; simp [start,h,zeroStore]
  · by_cases ho : i = output
    · subst i; simp [hi,start]
    · simp [finish,start,hi,ho,zeroStore]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

def compCode (R : Routine f c) (S : Routine g d) : Code (R.Vars ⊕ S.Vars) :=
  .seq (R.code.rename Sum.inl)
    (.seq (.copy (.inr S.input) (.inl R.output))
    (.seq (S.code.rename Sum.inr)
    (.seq (.nil (.inl R.output)) (.nil (.inr S.input)))))

def comp (R : Routine f c) (S : Routine g d) :
    Routine (g ∘ f) (fun x => c x+d (f x)+10*((f x).size+1)) where
  Vars := R.Vars ⊕ S.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl R.input
  output := .inr S.output
  distinct := by simp
  code := compCode R S
  correct x := by
    let a := start R.input x
    let a' := finish R.input R.output x (f x)
    let b := start S.input (f x)
    let b' := finish S.input S.output (f x) (g (f x))
    have h₁ : Bounded (R.code.rename Sum.inl) (join a (zeroStore S.Vars)) (join a' (zeroStore S.Vars)) (c x) :=
      (R.correct x).left _
    have h₂ : Bounded (.copy (.inr S.input) (.inl R.output))
        (join a' (zeroStore S.Vars)) (join a' b) ((f x).size+2) := by
      simpa [join_update_right,a',b,zeroStore,start,Nat.add_comm] using
        (Eval.copy (.inr S.input) (.inl R.output) (join a' (zeroStore S.Vars))).bounded
    have h₃ : Bounded (S.code.rename Sum.inr) (join a' b) (join a' b') (d (f x)) :=
      (S.correct (f x)).right _
    have h₄ : Bounded (.nil (.inl R.output)) (join a' b') (join a b') (1+(f x).size) := by
      simpa only [join_update_left,a',a,reset_output R.distinct,join_inl,finish_output] using
        (Eval.nil (.inl R.output) (join a' b')).bounded
    have h₅ : Bounded (.nil (.inr S.input)) (join a b') (join a (start S.output (g (f x)))) (1+(f x).size) := by
      simpa only [join_update_right,b',reset_input S.distinct,join_inr,finish_input S.distinct] using
        (Eval.nil (.inr S.input) (join a b')).bounded
    have hh := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
    simpa only [start_left,finish_lr,Function.comp_apply] using
      (show Bounded (compCode R S) (join a (zeroStore S.Vars)) (join a (start S.output (g (f x))))
        (c x+d (f x)+10*((f x).size+1)) from hh.mono (by omega))

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

variable {V : Type} [DecidableEq V]
theorem reset_start (input : V) (x : Data) :
    Function.update (start input x) input .nil = zeroStore V := by
  funext i
  by_cases h : i = input <;> simp [start,zeroStore,h]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

def pairCode (R : Routine f c) (S : Routine g d) : Code ((R.Vars ⊕ S.Vars) ⊕ Unit) :=
  .seq ((R.code.rename Sum.inl).rename Sum.inl)
    (.seq (.copy (.inl (.inr S.input)) (.inl (.inl R.input)))
    (.seq ((S.code.rename Sum.inr).rename Sum.inl)
    (.seq (.pair (.inr ()) (.inl (.inl R.output)) (.inl (.inr S.output)))
    (.seq (.nil (.inl (.inl R.output)))
    (.seq (.nil (.inl (.inr S.output))) (.nil (.inl (.inr S.input))))))))

def pair (R : Routine f c) (S : Routine g d) :
    Routine (fun x => Data.pair (f x) (g x))
      (fun x => c x+d x+20*(x.size+(f x).size+(g x).size+1)) where
  Vars := (R.Vars ⊕ S.Vars) ⊕ Unit
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl (.inl R.input)
  output := .inr ()
  distinct := by simp
  code := pairCode R S
  correct x := by
    let a := start R.input x
    let a' := finish R.input R.output x (f x)
    let b := start S.input x
    let b' := finish S.input S.output x (g x)
    let z := zeroStore Unit
    let o := start () (Data.pair (f x) (g x))
    have h₁ := ((R.correct x).left (zeroStore S.Vars)).left z
    have h₂ : Bounded (.copy (.inl (.inr S.input)) (.inl (.inl R.input)))
        (join (join a' (zeroStore S.Vars)) z) (join (join a' b) z) (x.size+2) := by
      simpa [join_update_left,join_update_right,a',b,zeroStore,start,R.distinct,Nat.add_comm] using
        (Eval.copy (.inl (.inr S.input)) (.inl (.inl R.input))
          (join (join a' (zeroStore S.Vars)) z)).bounded
    have h₃ := ((S.correct x).right a').left z
    have h₄ : Bounded (.pair (.inr ()) (.inl (.inl R.output)) (.inl (.inr S.output)))
        (join (join a' b') z) (join (join a' b') o) (2+(f x).size+(g x).size) := by
      simpa [join_update_right,o,z,zeroStore,start,a',b'] using
        (Eval.pair (.inr ()) (.inl (.inl R.output)) (.inl (.inr S.output))
          (join (join a' b') z)).bounded
    have h₅ : Bounded (.nil (.inl (.inl R.output)))
        (join (join a' b') o) (join (join a b') o) (1+(f x).size) := by
      simpa only [join_update_left,a',a,reset_output R.distinct,join_inl,finish_output] using
        (Eval.nil (.inl (.inl R.output)) (join (join a' b') o)).bounded
    have h₆ : Bounded (.nil (.inl (.inr S.output)))
        (join (join a b') o) (join (join a b) o) (1+(g x).size) := by
      simpa only [join_update_left,join_update_right,b',b,reset_output S.distinct,join_inr,join_inl,finish_output] using
        (Eval.nil (.inl (.inr S.output)) (join (join a b') o)).bounded
    have h₇ : Bounded (.nil (.inl (.inr S.input)))
        (join (join a b) o) (join (join a (zeroStore S.Vars)) o) (1+x.size) := by
      simpa only [join_update_left,join_update_right,b,reset_start,join_inr,join_inl,start_input] using
        (Eval.nil (.inl (.inr S.input)) (join (join a b) o)).bounded
    have hh := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))
    simpa only [start_left,finish_lr] using
      (show Bounded (pairCode R S) (join (join a (zeroStore S.Vars)) z)
        (join (join a (zeroStore S.Vars)) o)
        (c x+d x+20*(x.size+(f x).size+(g x).size+1)) from hh.mono (by omega))

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]
theorem Bounded.loop_stop (src : V) (p : Code V) (s : V → Data)
    (h : (s src).nonempty = false) : Bounded (.loop src p) s s 1 :=
  (Eval.loop_stop h).bounded

theorem Bounded.loop_step {src : V} {p : Code V} {s t u : V → Data} {n m : ℕ}
    (h : (s src).nonempty = true) (hp : Bounded p s t n)
    (hq : Bounded (.loop src p) t u m) : Bounded (.loop src p) s u (n+m+1) := by
  obtain ⟨n',hn,he⟩ := hp
  obtain ⟨m',hm,he'⟩ := hq
  exact ⟨n'+m'+1,by omega,Eval.loop_step h he he'⟩
end ThreeMachine.StackCompiler.Tree

end

end OAI
end


section
-- module Realizers
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
namespace Data

def fold (f : Data → Data) (acc : Data) : Data → Data
  | .nil => acc
  | .pair a xs => fold f (f (.pair a acc)) xs

def foldCost (f : Data → Data) (c : Data → ℕ) (acc : Data) : Data → ℕ
  | .nil => 1
  | .pair a xs => c (.pair a acc) + foldCost f c (f (.pair a acc)) xs +
      20*((Data.pair a xs).size+acc.size+(f (.pair a acc)).size+1)

end Data
namespace Routine
variable {f : Data → Data} {c : Data → ℕ}

def foldStore (x acc xs : Data) : Fin 3 → Data := ![x,acc,xs]
@[simp] theorem foldStore_zero (x acc xs : Data) : foldStore x acc xs 0 = x := rfl
@[simp] theorem foldStore_one (x acc xs : Data) : foldStore x acc xs 1 = acc := rfl
@[simp] theorem foldStore_two (x acc xs : Data) : foldStore x acc xs 2 = xs := rfl

theorem foldStore_update_one (x acc xs y : Data) :
    Function.update (foldStore x acc xs) 1 y = foldStore x y xs := by
  funext i; fin_cases i <;> simp [foldStore]

theorem foldStore_update_two (x acc xs y : Data) :
    Function.update (foldStore x acc xs) 2 y = foldStore x acc y := by
  funext i; fin_cases i <;> simp [foldStore]

def foldBody (R : Routine f c) : Code (Fin 3 ⊕ R.Vars) :=
  .seq (.select true (.inr R.input) (.inl 2))
    (.seq (.pair (.inr R.input) (.inr R.input) (.inl 1))
    (.seq (R.code.rename Sum.inr)
    (.seq (.copy (.inl 1) (.inr R.output))
    (.seq (.nil (.inr R.input))
    (.seq (.nil (.inr R.output)) (.select false (.inl 2) (.inl 2)))))))

def foldCode (R : Routine f c) : Code (Fin 3 ⊕ R.Vars) :=
  .seq (.select true (.inl 2) (.inl 0))
    (.seq (.select false (.inl 1) (.inl 0)) (.loop (.inl 2) (foldBody R)))

theorem foldBody_correct (R : Routine f c) (x acc a xs : Data) :
    Bounded (foldBody R)
      (join (foldStore x acc (.pair a xs)) (zeroStore R.Vars))
      (join (foldStore x (f (.pair a acc)) xs) (zeroStore R.Vars))
      (c (.pair a acc)+20*((Data.pair a xs).size+acc.size+(f (.pair a acc)).size+1)-1) := by
  let l := foldStore x acc (.pair a xs)
  let l' := foldStore x (f (.pair a acc)) (.pair a xs)
  let z := zeroStore R.Vars
  let r := start R.input (.pair a acc)
  let r' := finish R.input R.output (.pair a acc) (f (.pair a acc))
  have h₁ : Bounded (.select true (.inr R.input) (.inl 2))
      (join l z) (join l (start R.input a)) (2+(Data.pair a xs).size) := by
    simpa [join_update_right,l,z,start,zeroStore,Data.head] using
      (Eval.select true (.inr R.input) (.inl 2) (join l z)).bounded
  have h₂ : Bounded (.pair (.inr R.input) (.inr R.input) (.inl 1))
      (join l (start R.input a)) (join l r) (1+a.size+a.size+acc.size) := by
    simpa [join_update_right,l,r,start,Function.update_idem] using
      (Eval.pair (.inr R.input) (.inr R.input) (.inl 1) (join l (start R.input a))).bounded
  have h₃ : Bounded (R.code.rename Sum.inr) (join l r) (join l r') (c (.pair a acc)) :=
    (R.correct (.pair a acc)).right l
  have h₄ : Bounded (.copy (.inl 1) (.inr R.output)) (join l r') (join l' r')
      (1+acc.size+(f (.pair a acc)).size) := by
    simpa [join_update_left,l,l',r',foldStore_update_one] using
      (Eval.copy (.inl 1) (.inr R.output) (join l r')).bounded
  have h₅ : Bounded (.nil (.inr R.input)) (join l' r')
      (join l' (start R.output (f (.pair a acc)))) (1+(Data.pair a acc).size) := by
    simpa only [join_update_right,r',reset_input R.distinct,join_inr,finish_input R.distinct] using
      (Eval.nil (.inr R.input) (join l' r')).bounded
  have h₆ : Bounded (.nil (.inr R.output))
      (join l' (start R.output (f (.pair a acc)))) (join l' z) (1+(f (.pair a acc)).size) := by
    simpa only [join_update_right,reset_start,join_inr,start_input,z] using
      (Eval.nil (.inr R.output) (join l' (start R.output (f (.pair a acc))))).bounded
  have h₇ : Bounded (.select false (.inl 2) (.inl 2)) (join l' z)
      (join (foldStore x (f (.pair a acc)) xs) z) (1+(Data.pair a xs).size+(Data.pair a xs).size) := by
    simpa [join_update_left,l',foldStore_update_two,Data.tail] using
      (Eval.select false (.inl 2) (.inl 2) (join l' z)).bounded
  have hh := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))
  exact hh.mono (by simp only [Data.size_pair]; omega)

theorem foldLoop_correct (R : Routine f c) (x acc xs : Data) :
    Bounded (.loop (.inl 2) (foldBody R))
      (join (foldStore x acc xs) (zeroStore R.Vars))
      (join (foldStore x (Data.fold f acc xs) .nil) (zeroStore R.Vars))
      (Data.foldCost f c acc xs) := by
  induction xs generalizing acc with
  | nil => exact Bounded.loop_stop _ _ _ rfl
  | pair a xs _ ih =>
    have hh := Bounded.loop_step (by rfl :
      ((join (foldStore x acc (.pair a xs)) (zeroStore R.Vars)) (.inl 2)).nonempty = true)
      (foldBody_correct R x acc a xs) (ih (f (.pair a acc)))
    exact hh.mono (by simp only [Data.foldCost]; omega)

def fold (R : Routine f c) :
    Routine (fun x => Data.fold f x.tail x.head)
      (fun x => 2*x.size+6+Data.foldCost f c x.tail x.head) where
  Vars := Fin 3 ⊕ R.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl 0
  output := .inl 1
  distinct := by simp
  code := foldCode R
  correct x := by
    have es : start (0 : Fin 3) x = foldStore x .nil .nil := by
      funext i; fin_cases i <;> simp [start,zeroStore,foldStore]
    have ef : finish (Sum.inl (0 : Fin 3)) (Sum.inl (1 : Fin 3)) x (Data.fold f x.tail x.head) =
        join (foldStore x (Data.fold f x.tail x.head) .nil) (zeroStore R.Vars) := by
      rw [finish,start_left,es,join_update_left,foldStore_update_one]
    have h₁ : Bounded (.select true (.inl 2) (.inl 0))
        (join (foldStore x .nil .nil) (zeroStore R.Vars))
        (join (foldStore x .nil x.head) (zeroStore R.Vars)) (2+x.size) := by
      simpa [join_update_left,foldStore_update_two] using
        (Eval.select true (.inl 2) (.inl 0)
          (join (foldStore x .nil .nil) (zeroStore R.Vars))).bounded
    have h₂ : Bounded (.select false (.inl 1) (.inl 0))
        (join (foldStore x .nil x.head) (zeroStore R.Vars))
        (join (foldStore x x.tail x.head) (zeroStore R.Vars)) (2+x.size) := by
      simpa [join_update_left,foldStore_update_one] using
        (Eval.select false (.inl 1) (.inl 0)
          (join (foldStore x .nil x.head) (zeroStore R.Vars))).bounded
    have hh := h₁.seq (h₂.seq (foldLoop_correct R x x.tail x.head))
    rw [start_left,es,ef]
    exact hh.mono (by omega)

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

class Coding (α : Type u1) where
  encode : α → Data

def enc {α : Type u2} [Coding α] : α → Data := Coding.encode

def volume {α : Type u3} [Coding α] (x : α) : ℕ := (enc x).size

instance : Coding Data := ⟨id⟩
instance : Coding Unit := ⟨fun _ => .nil⟩
instance : Coding Bool := ⟨fun b => if b then .pair .nil .nil else .nil⟩
instance {α : Type u4} {β : Type u5} [Coding α] [Coding β] : Coding (α × β) :=
  ⟨fun x => .pair (enc x.1) (enc x.2)⟩

def encodeList {α : Type u6} [Coding α] : List α → Data
  | [] => .nil
  | x :: xs => .pair (enc x) (encodeList xs)
instance {α : Type u7} [Coding α] : Coding (List α) := ⟨encodeList⟩

def encodeUnary : ℕ → Data | 0 => .nil | n+1 => .pair .nil (encodeUnary n)
instance : Coding ℕ := ⟨encodeUnary⟩
instance {α : Type u8} [Coding α] : Coding (Option α) :=
  ⟨fun x => match x with | none => .nil | some a => .pair (enc a) .nil⟩

@[simp] theorem enc_data (x : Data) : enc x = x := rfl
@[simp] theorem enc_unit (x : Unit) : enc x = .nil := rfl
@[simp] theorem enc_false : enc false = .nil := rfl
@[simp] theorem enc_true : enc true = .pair .nil .nil := rfl
@[simp] theorem enc_pair {α : Type u9} {β : Type u10} [Coding α] [Coding β] (x : α) (y : β) :
    enc (x,y) = .pair (enc x) (enc y) := rfl
@[simp] theorem enc_nil {α : Type u11} [Coding α] : enc ([] : List α) = .nil := rfl
@[simp] theorem enc_cons {α : Type u12} [Coding α] (x : α) (xs : List α) :
    enc (x :: xs) = .pair (enc x) (enc xs) := rfl
@[simp] theorem enc_zero : enc (0 : ℕ) = .nil := rfl
@[simp] theorem enc_succ (n : ℕ) : enc (n+1) = .pair .nil (enc n) := rfl
@[simp] theorem enc_none {α : Type u13} [Coding α] : enc (none : Option α) = .nil := rfl
@[simp] theorem enc_some {α : Type u14} [Coding α] (x : α) : enc (some x) = .pair (enc x) .nil := rfl

@[simp] theorem volume_pair {α : Type u15} {β : Type u16} [Coding α] [Coding β] (x : α) (y : β) :
    volume (x,y) = volume x+volume y+1 := Data.size_pair _ _
@[simp] theorem volume_nil {α : Type u17} [Coding α] : volume ([] : List α) = 1 := rfl
@[simp] theorem volume_cons {α : Type u18} [Coding α] (x : α) (xs : List α) :
    volume (x :: xs) = volume x+volume xs+1 := Data.size_pair _ _
@[simp] theorem volume_nat (n : ℕ) : volume n = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Data.size (.pair .nil (enc n)) = _
    change (enc n).size = 2*n+1 at ih
    simp only [Data.size_pair,Data.size_nil,ih]
    omega

structure Realizer {α : Type u19} {β : Type u20} [Coding α] [Coding β] (f : α → β) where
  transform : Data → Data
  charge : Data → ℕ
  routine : Routine transform charge
  correct : ∀ x, transform (enc x) = enc (f x)

namespace Realizer
variable {α : Type u21} {β : Type u22} {γ : Type u23} {δ : Type u24} [Coding α] [Coding β] [Coding γ] [Coding δ]
variable {f : α → β} {g : β → γ}

def time (R : Realizer f) (x : α) : ℕ := R.charge (enc x)

def id : Realizer (_root_.id : α → α) :=
  ⟨_root_.id,_,Routine.identity,fun _ => rfl⟩

@[simp] theorem time_id (x : α) : (id : Realizer (_root_.id : α → α)).time x = volume x+2 := rfl

def unit : Realizer (fun _ : α => ()) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def nil : Realizer (fun _ : α => ([] : List β)) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def zero : Realizer (fun _ : α => (0 : ℕ)) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def false : Realizer (fun _ : α => Bool.false) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def comp (R : Realizer f) (S : Realizer g) : Realizer (g ∘ f) where
  transform := S.transform ∘ R.transform
  charge := _
  routine := R.routine.comp S.routine
  correct x := by simp only [Function.comp_apply,R.correct,S.correct]

theorem time_comp (R : Realizer f) (S : Realizer g) (x : α) :
    (R.comp S).time x = R.time x+S.time (f x)+10*(volume (f x)+1) := by
  simp only [comp,time,Routine.comp,R.correct,volume]

def pair {g : α → γ} (R : Realizer f) (S : Realizer g) : Realizer (fun x => (f x,g x)) where
  transform := fun x => .pair (R.transform x) (S.transform x)
  charge := _
  routine := R.routine.pair S.routine
  correct x := by simp only [R.correct,S.correct,enc_pair]

theorem time_pair {g : α → γ} (R : Realizer f) (S : Realizer g) (x : α) :
    (R.pair S).time x = R.time x+S.time x+20*(volume x+volume (f x)+volume (g x)+1) := by
  simp only [pair,time,Routine.pair,R.correct,S.correct,volume]

def fst : Realizer (Prod.fst : α × β → α) :=
  ⟨Data.head,_,Routine.select true,fun _ => rfl⟩

def snd : Realizer (Prod.snd : α × β → β) :=
  ⟨Data.tail,_,Routine.select Bool.false,fun _ => rfl⟩

@[simp] theorem time_fst (x : α × β) : (fst : Realizer (Prod.fst : α × β → α)).time x = volume x+2 := rfl
@[simp] theorem time_snd (x : α × β) : (snd : Realizer (Prod.snd : α × β → β)).time x = volume x+2 := rfl

def congr {f' : α → β} (R : Realizer f) (h : ∀ x, f x = f' x) : Realizer f' :=
  { R with correct := fun x => (R.correct x).trans (congrArg enc (h x)) }

@[simp] theorem time_congr {f' : α → β} (R : Realizer f) (h : ∀ x, f x = f' x) (x : α) :
    (R.congr h).time x = R.time x := rfl

theorem fold_correct {F : α × β → β} (R : Realizer F) (xs : List α) (b : β) :
    Data.fold R.transform (enc b) (enc xs) = enc (xs.foldl (fun b a => F (a,b)) b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    change Data.fold R.transform (R.transform (enc (a,b))) (enc xs) = _
    rw [R.correct,ih]
    rfl

def fold {F : α × β → β} (R : Realizer F) :
    Realizer (fun x : List α × β => x.1.foldl (fun b a => F (a,b)) x.2) where
  transform := fun x => Data.fold R.transform x.tail x.head
  charge := _
  routine := R.routine.fold
  correct x := fold_correct R x.1 x.2

def foldTime {F : α × β → β} (R : Realizer F) (b : β) : List α → ℕ
  | [] => 1
  | a :: xs => R.time (a,b)+foldTime R (F (a,b)) xs+
      20*(volume (a :: xs)+volume b+volume (F (a,b))+1)

theorem foldTime_eq {F : α × β → β} (R : Realizer F) (xs : List α) (b : β) :
    Data.foldCost R.transform R.charge (enc b) (enc xs) = foldTime R b xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    change R.time (a,b)+Data.foldCost R.transform R.charge (R.transform (enc (a,b))) (enc xs)+
      20*(volume (a :: xs)+volume b+(R.transform (enc (a,b))).size+1) = _
    rw [R.correct,ih]
    rfl

theorem time_fold {F : α × β → β} (R : Realizer F) (x : List α × β) :
    R.fold.time x = 2*volume x+6+foldTime R x.2 x.1 := by
  change 2*volume x+6+Data.foldCost R.transform R.charge (enc x.2) (enc x.1) = _
  rw [foldTime_eq]

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]
theorem Bounded.branch_true {src : V} {p q : Code V} {s t : V → Data} {n : ℕ}
    (h : (s src).nonempty = true) (hp : Bounded p s t n) : Bounded (.branch src p q) s t (n+1) := by
  obtain ⟨m,hm,he⟩ := hp
  exact ⟨m+1,by omega,Eval.branch_true h he⟩
theorem Bounded.branch_false {src : V} {p q : Code V} {s t : V → Data} {n : ℕ}
    (h : (s src).nonempty = false) (hq : Bounded q s t n) : Bounded (.branch src p q) s t (n+1) := by
  obtain ⟨m,hm,he⟩ := hq
  exact ⟨m+1,by omega,Eval.branch_false h he⟩
end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}
variable {V : Type} [DecidableEq V]

def invoke (R : Routine f c) (dst src : V) : Code (V ⊕ R.Vars) :=
  .seq (.copy (.inr R.input) (.inl src))
    (.seq (R.code.rename Sum.inr)
    (.seq (.copy (.inl dst) (.inr R.output))
    (.seq (.nil (.inr R.input)) (.nil (.inr R.output)))))

theorem invoke_correct (R : Routine f c) (dst src : V) (s : V → Data) :
    Bounded (R.invoke dst src) (join s (zeroStore R.Vars))
      (join (Function.update s dst (f (s src))) (zeroStore R.Vars))
      (c (s src)+10*((s src).size+(s dst).size+(f (s src)).size+1)) := by
  let a := start R.input (s src)
  let b := finish R.input R.output (s src) (f (s src))
  let t := Function.update s dst (f (s src))
  have h₁ : Bounded (.copy (.inr R.input) (.inl src))
      (join s (zeroStore R.Vars)) (join s a) (2+(s src).size) := by
    simpa [join_update_right,a,start,zeroStore] using
      (Eval.copy (.inr R.input) (.inl src) (join s (zeroStore R.Vars))).bounded
  have h₂ := (R.correct (s src)).right s
  have h₃ : Bounded (.copy (.inl dst) (.inr R.output)) (join s b) (join t b)
      (1+(s dst).size+(f (s src)).size) := by
    simpa [join_update_left,t,b] using (Eval.copy (.inl dst) (.inr R.output) (join s b)).bounded
  have h₄ : Bounded (.nil (.inr R.input)) (join t b)
      (join t (start R.output (f (s src)))) (1+(s src).size) := by
    simpa only [join_update_right,b,reset_input R.distinct,join_inr,finish_input R.distinct] using
      (Eval.nil (.inr R.input) (join t b)).bounded
  have h₅ : Bounded (.nil (.inr R.output)) (join t (start R.output (f (s src))))
      (join t (zeroStore R.Vars)) (1+(f (s src)).size) := by
    simpa only [join_update_right,reset_start,join_inr,start_input] using
      (Eval.nil (.inr R.output) (join t (start R.output (f (s src))))).bounded
  exact (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono (by omega)

def chooseCode (R : Routine f c) (S : Routine g d) : Code ((Fin 3 ⊕ R.Vars) ⊕ S.Vars) :=
  .seq (.select true (.inl (.inl 2)) (.inl (.inl 0)))
    (.seq (.branch (.inl (.inl 2))
      ((R.invoke (1 : Fin 3) 0).rename Sum.inl)
      (S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)))
      (.nil (.inl (.inl 2))))

def choose (R : Routine f c) (S : Routine g d) :
    Routine (fun x => if x.head.nonempty then f x else g x)
      (fun x => c x+d x+30*(x.size+(f x).size+(g x).size+1)) where
  Vars := (Fin 3 ⊕ R.Vars) ⊕ S.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl (.inl 0)
  output := .inl (.inl 1)
  distinct := by simp
  code := chooseCode R S
  correct x := by
    let z := zeroStore R.Vars
    let w := zeroStore S.Vars
    let s := foldStore x .nil .nil
    let s' := foldStore x .nil x.head
    let y := if x.head.nonempty then f x else g x
    let t := foldStore x y x.head
    have es : start (0 : Fin 3) x = s := by
      funext i; fin_cases i <;> simp [s,start,zeroStore,foldStore]
    have ef : finish (Sum.inl (Sum.inl (0 : Fin 3))) (Sum.inl (Sum.inl (1 : Fin 3))) x y =
        join (join (foldStore x y .nil) z) w := by
      rw [finish,start_left,start_left,es,join_update_left,join_update_left]
      simp only [s,foldStore_update_one]
      rfl
    have h₁ : Bounded (.select true (.inl (.inl 2)) (.inl (.inl 0)))
        (join (join s z) w) (join (join s' z) w) (2+x.size) := by
      simpa [join_update_left,s,s',foldStore_update_two] using
        (Eval.select true (.inl (.inl 2)) (.inl (.inl 0)) (join (join s z) w)).bounded
    have h₂ : Bounded (.branch (.inl (.inl 2)) ((R.invoke (1 : Fin 3) 0).rename Sum.inl)
        (S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)))
        (join (join s' z) w) (join (join t z) w)
        (c x+d x+10*(x.size+(f x).size+(g x).size+2)+1) := by
      cases he : x.head.nonempty with
      | false =>
        have hh := (S.invoke_correct (Sum.inl (1 : Fin 3)) (Sum.inl 0) (join s' z)).branch_false
          (src := Sum.inl (Sum.inl (2 : Fin 3))) (p := ((R.invoke (1 : Fin 3) 0).rename Sum.inl)) (by simpa [s'] using he)
        simpa only [join_update_left,s',foldStore_update_one,t,y,he,Bool.false_eq_true,ite_false,join_inl,foldStore_zero] using
          (hh.mono (m := c x+d x+10*(x.size+(f x).size+(g x).size+2)+1)
            (by simp only [join_inl,foldStore_zero,foldStore_one,s',Data.size_nil]; omega))
      | true =>
        have hh := ((R.invoke_correct (1 : Fin 3) 0 s').left w).branch_true
          (src := Sum.inl (Sum.inl (2 : Fin 3))) (q := S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)) (by simpa [s'] using he)
        simpa only [s',foldStore_update_one,t,y,he,ite_true,foldStore_zero] using
          (hh.mono (m := c x+d x+10*(x.size+(f x).size+(g x).size+2)+1)
            (by simp only [foldStore_zero,foldStore_one,s',Data.size_nil]; omega))
    have h₃ : Bounded (.nil (.inl (.inl 2))) (join (join t z) w)
        (join (join (foldStore x y .nil) z) w) (1+x.head.size) := by
      simpa only [join_update_left,t,foldStore_update_two,join_inl,foldStore_two] using
        (Eval.nil (.inl (.inl 2)) (join (join t z) w)).bounded
    rw [start_left,start_left,es,ef]
    have hh := h₁.seq (h₂.seq h₃)
    exact hh.mono (by
      have hx : x.head.size ≤ x.size := by cases x <;> simp [Data.head]; omega
      omega)

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Routine

def constant : (d : Data) → Routine (fun _ => d) (fun x => (2*d.size+1)*(20*x.size+50*d.size+50))
  | .nil => nil.mono (by intro x; simp only [Data.size_nil]; omega)
  | .pair a b => ((constant a).pair (constant b)).mono (by
      intro x
      simp only [Data.size_pair]
      nlinarith)

end Routine
namespace Realizer
variable {α : Type u25} {β : Type u26} {γ : Type u27} [Coding α] [Coding β] [Coding γ]

def constant (b : β) : Realizer (fun _ : α => b) :=
  ⟨fun _ => enc b,_,Routine.constant (enc b),fun _ => rfl⟩

def reinterpret (f : α → β) (h : ∀ x, enc (f x) = enc x) : Realizer f :=
  ⟨_root_.id,_,Routine.identity,fun x => (h x).symm⟩

@[simp] theorem time_reinterpret (f : α → β) (h : ∀ x, enc (f x) = enc x) (x : α) :
    (reinterpret f h).time x = volume x+2 := rfl

def cons : Realizer (fun x : α × List α => x.1 :: x.2) := reinterpret _ (fun _ => rfl)

def choose {f g : α → β} (R : Realizer f) (S : Realizer g) :
    Realizer (fun x : Bool × α => if x.1 then f x.2 else g x.2) where
  transform := fun x => if x.head.nonempty then (snd.comp R).transform x else (snd.comp S).transform x
  charge := _
  routine := (snd.comp R).routine.choose (snd.comp S).routine
  correct x := by
    rcases x with ⟨b,x⟩
    cases b <;> simp only [enc_pair,enc_false,enc_true,Data.head,Data.nonempty,
      Bool.false_eq_true,ite_false,ite_true]
    · exact (snd.comp S).correct (Bool.false,x)
    · exact (snd.comp R).correct (true,x)

theorem time_choose {f g : α → β} (R : Realizer f) (S : Realizer g) (x : Bool × α) :
    (R.choose S).time x = (snd.comp R).time x+(snd.comp S).time x+
      30*(volume x+volume (f x.2)+volume (g x.2)+1) := by
  change (snd.comp R).time x+(snd.comp S).time x+
    30*(volume x+((snd.comp R).transform (enc x)).size+((snd.comp S).transform (enc x)).size+1) = _
  rw [(snd.comp R).correct,(snd.comp S).correct]
  rfl

def succ : Realizer (fun n : ℕ => n+1) :=
  (unit.pair id).comp (reinterpret (fun x : Unit × ℕ => x.2+1) (by intro x; rfl)) |>.congr (fun _ => rfl)

end Realizer
end ThreeMachine.StackCompiler

end

end OAI
end


section
-- module UniformRoutines
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26

section

namespace ThreeMachine.StackCompiler
variable {α : Type u1} {β : Type u2} [Coding α] [Coding β]

theorem volume_pos (x : α) : 0 < volume x := by
  change 0 < (enc x).encode.length
  cases enc x <;> simp [Data.encode]

theorem volume_list_le (xs : List α) (M : ℕ) (h : ∀ a ∈ xs, volume a ≤ M) :
    volume xs ≤ xs.length*(M+1)+1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [volume_cons,List.length_cons]
    nlinarith

namespace Realizer
variable {F : α × β → β}

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Realizer
variable {α : Type u3} {β : Type u4} {γ : Type u5} [Coding α] [Coding β] [Coding γ]

def onFst {f : α → β} (R : Realizer f) : Realizer (fun x : α × γ => (f x.1,x.2)) :=
  (fst.comp R).pair snd

def swap : Realizer (fun x : α × β => (x.2,x.1)) := snd.pair fst

omit [Coding α] in
theorem fold_cons_eq (xs ys : List α) :
    xs.foldl (fun ys a => a :: ys) ys = xs.reverse ++ ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simp [ih,List.append_assoc]

def reverse : Realizer (fun xs : List α => xs.reverse) :=
  ((id.pair (nil : Realizer (fun _ : List α => ([] : List α)))).comp cons.fold).congr
    (fun xs => by simp only [Function.comp_apply,fold_cons_eq,List.append_nil,id_eq])

omit [Coding α] [Coding β] [Coding γ] in
theorem map_fold_eq (f : α × γ → β) (xs : List α) (e : γ) (ys : List β) :
    xs.foldl (fun s a => (s.1,f (a,s.1) :: s.2)) (e,ys) =
      (e,(xs.map (fun a => f (a,e))).reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simp [ih,List.append_assoc]

end ThreeMachine.StackCompiler.Realizer

namespace ThreeMachine.StackCompiler

structure Uniform {I : Type u6} {α : I → Type u7} {β : I → Type u8} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
    (f : ∀ i, α i → β i) where
  transform : Data → Data
  charge : Data → ℕ
  routine : Routine transform charge
  correct : ∀ i x, transform (enc x) = enc (f i x)

namespace Uniform
variable {I : Type u9} {α : I → Type u10} {β : I → Type u11} {γ : I → Type u12} {δ : I → Type u13}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)] [∀ i, Coding (δ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}

def specialize (R : Uniform f) (i : I) : Realizer (f i) :=
  ⟨R.transform,R.charge,R.routine,R.correct i⟩

def time (R : Uniform f) (i : I) (x : α i) : ℕ := R.charge (enc x)

def id : Uniform (fun (i : I) (x : α i) => x) :=
  ⟨_root_.id,_,Routine.identity,fun _ _ => rfl⟩

def unit : Uniform (fun (i : I) (_ : α i) => ()) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def nil : Uniform (fun (i : I) (_ : α i) => ([] : List (β i))) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def zero : Uniform (fun (i : I) (_ : α i) => (0 : ℕ)) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def false : Uniform (fun (i : I) (_ : α i) => Bool.false) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def comp (R : Uniform f) (S : Uniform g) : Uniform (fun i => g i ∘ f i) where
  transform := S.transform ∘ R.transform
  charge := _
  routine := R.routine.comp S.routine
  correct i x := by simp only [Function.comp_apply,R.correct,S.correct]

def pair {g : ∀ i, α i → γ i} (R : Uniform f) (S : Uniform g) :
    Uniform (fun i x => (f i x,g i x)) where
  transform := fun x => .pair (R.transform x) (S.transform x)
  charge := _
  routine := R.routine.pair S.routine
  correct i x := by simp only [R.correct,S.correct,enc_pair]

def fst : Uniform (fun (i : I) => (Prod.fst : α i × β i → α i)) :=
  ⟨Data.head,_,Routine.select true,fun _ _ => rfl⟩

def snd : Uniform (fun (i : I) => (Prod.snd : α i × β i → β i)) :=
  ⟨Data.tail,_,Routine.select Bool.false,fun _ _ => rfl⟩

def congr {f' : ∀ i, α i → β i} (R : Uniform f) (h : ∀ i x, f i x = f' i x) : Uniform f' :=
  { R with correct := fun i x => (R.correct i x).trans (congrArg enc (h i x)) }

def reinterpret (f : ∀ i, α i → β i) (h : ∀ i x, enc (f i x) = enc x) : Uniform f :=
  ⟨_root_.id,_,Routine.identity,fun i x => (h i x).symm⟩

def fold {F : ∀ i, α i × β i → β i} (R : Uniform F) :
    Uniform (fun i (x : List (α i) × β i) => x.1.foldl (fun b a => F i (a,b)) x.2) where
  transform := fun x => Data.fold R.transform x.tail x.head
  charge := _
  routine := R.routine.fold
  correct i x := (R.specialize i).fold_correct x.1 x.2

def choose {g : ∀ i, α i → β i} (R : Uniform f) (S : Uniform g) :
    Uniform (fun i (x : Bool × α i) => if x.1 then f i x.2 else g i x.2) where
  transform := fun x => if x.head.nonempty then ((snd (α := fun _ : I => Bool) (β := α)).comp R).transform x else ((snd (α := fun _ : I => Bool) (β := α)).comp S).transform x
  charge := _
  routine := ((snd (α := fun _ : I => Bool) (β := α)).comp R).routine.choose ((snd (α := fun _ : I => Bool) (β := α)).comp S).routine
  correct i x := ((R.specialize i).choose (S.specialize i)).correct x

def ite {p : ∀ i, α i → Bool} {g : ∀ i, α i → β i}
    (P : Uniform p) (R : Uniform f) (S : Uniform g) :
    Uniform (fun i x => if p i x then f i x else g i x) :=
  ((P.pair id).comp (R.choose S)).congr (fun _ _ => rfl)

def cons : Uniform (fun (i : I) (x : α i × List (α i)) => x.1 :: x.2) := reinterpret _ (fun _ _ => rfl)

def onFst (R : Uniform f) : Uniform (fun i (x : α i × γ i) => (f i x.1,x.2)) :=
  (fst.comp R).pair snd

def reverse : Uniform (fun (i : I) (xs : List (α i)) => xs.reverse) :=
  ((id.pair (nil : Uniform (fun (i : I) (_ : List (α i)) => ([] : List (α i))))).comp cons.fold).congr
    (fun _ _ => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.append_nil])

def mapBody {f : ∀ i, α i × γ i → β i} (R : Uniform f) :
    Uniform (fun i (x : α i × (γ i × List (β i))) => (x.2.1,f i (x.1,x.2.1) :: x.2.2)) :=
  (snd.comp fst).pair ((((fst.pair (snd.comp fst)).comp R).pair (snd.comp snd)).comp cons)

def map {f : ∀ i, α i × γ i → β i} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.map (fun a => f i (a,x.2))) :=
  (((fst.pair (snd.pair nil)).comp (mapBody R).fold).comp (snd.comp reverse)).congr (fun _ _ => by
    simp only [Function.comp_apply,Realizer.map_fold_eq,List.append_nil,List.reverse_reverse])

end Uniform

namespace Realizer
variable {α : Type u14} {β : Type u15} [Coding α] [Coding β] {f : α → β}
def uniform (R : Realizer f) (I : Type u16) : Uniform (fun (_ : I) => f) :=
  ⟨R.transform,R.charge,R.routine,fun _ => R.correct⟩
end Realizer

end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer
variable {α : Type u17} [Coding α]

def test (p : α → Bool) (h : ∀ x, (enc x).nonempty = p x) : Realizer p where
  transform := fun x => if x.nonempty then .pair .nil .nil else .nil
  charge := _
  routine := (Routine.identity.pair Routine.nil).comp
    ((Routine.constant (.pair .nil .nil)).choose Routine.nil)
  correct x := by rw [h]; cases p x <;> rfl

def not : Realizer Bool.not :=
  ((id.pair unit).comp ((false : Realizer (fun _ : Unit => Bool.false)).choose (constant true))).congr
    (fun b => by cases b <;> rfl)

def and : Realizer (fun x : Bool × Bool => x.1 && x.2) :=
  (id.choose false).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> rfl)

def or : Realizer (fun x : Bool × Bool => x.1 || x.2) :=
  ((constant true).choose id).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> rfl)

def positive : Realizer (fun n : ℕ => decide (0 < n)) :=
  test _ (by intro n; cases n <;> rfl)

def isZero : Realizer (fun n : ℕ => decide (n = 0)) :=
  (positive.comp not).congr (fun n => by cases n <;> rfl)

def pred : Realizer Nat.pred :=
  ⟨Data.tail,_,Routine.select Bool.false,fun n => by cases n <;> rfl⟩

theorem encode_replicate_unit (n : ℕ) : enc (List.replicate n ()) = enc n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,enc_cons,enc_unit,ih,enc_succ]

def unroll : Realizer (fun n : ℕ => List.replicate n ()) :=
  reinterpret _ encode_replicate_unit

omit [Coding α] in
theorem fold_replicate (f : α → α) (n : ℕ) (a : α) :
    (List.replicate n ()).foldl (fun a _ => f a) a = f^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.foldl_cons,Function.iterate_succ_apply] using ih (f a)

def iterate {f : α → α} (R : Realizer f) : Realizer (fun x : ℕ × α => f^[x.1] x.2) :=
  (unroll.onFst.comp (snd.comp R).fold).congr (fun x => fold_replicate f x.1 x.2)

theorem iterate_pred (n m : ℕ) : Nat.pred^[n] m = m-n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,ih,Nat.pred_eq_sub_one]; omega

theorem iterate_succ (n m : ℕ) : (fun k : ℕ => k+1)^[n] m = m+n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,ih]; omega

def add : Realizer (fun x : ℕ × ℕ => x.1+x.2) :=
  succ.iterate.congr (fun x => by rw [iterate_succ,Nat.add_comm])

def sub : Realizer (fun x : ℕ × ℕ => x.1-x.2) :=
  (swap.comp pred.iterate).congr (fun x => iterate_pred x.2 x.1)

def le : Realizer (fun x : ℕ × ℕ => decide (x.1 ≤ x.2)) :=
  (sub.comp isZero).congr (fun x => by simp only [Function.comp_apply,Nat.sub_eq_zero_iff_le])

def eqNat : Realizer (fun x : ℕ × ℕ => decide (x.1 = x.2)) :=
  ((le.pair (swap.comp le)).comp and).congr (fun x => by
    apply Bool.eq_iff_iff.mpr
    simp [le_antisymm_iff])

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u18} {α : I → Type u19} {β : I → Type u20} {γ : I → Type u21}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def test (p : ∀ i, α i → Bool) (h : ∀ i x, (enc x).nonempty = p i x) : Uniform p where
  transform := fun x => if x.nonempty then .pair .nil .nil else .nil
  charge := _
  routine := (Routine.identity.pair Routine.nil).comp
    ((Routine.constant (.pair .nil .nil)).choose Routine.nil)
  correct i x := by rw [h]; cases p i x <;> rfl

def isCons : Uniform (fun (i : I) (xs : List (α i)) => !xs.isEmpty) :=
  test _ (by intro _ xs; cases xs <;> rfl)

def head? : Uniform (fun (i : I) (xs : List (α i)) => xs.head?) where
  transform := fun x => if x.nonempty then .pair x.head .nil else .nil
  charge := _
  routine := (Routine.identity.pair Routine.nil).comp
    ((((Routine.select true).comp (Routine.select true)).pair Routine.nil).choose Routine.nil)
  correct i xs := by cases xs <;> rfl

def swap : Uniform (fun (i : I) (x : α i × β i) => (x.2,x.1)) := snd.pair fst

def append : Uniform (fun (i : I) (x : List (α i) × List (α i)) => x.1 ++ x.2) :=
  (((fst.comp reverse).pair snd).comp cons.fold).congr (fun _ _ => by
    simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

omit [∀ i, Coding (α i)] in
theorem flatten_fold_eq (i : I) (xs : List (List (α i))) (acc : List (α i)) :
    xs.foldl (fun ys zs => zs.foldl (fun ys a => a :: ys) ys) acc = xs.flatten.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons xs xss ih =>
    rw [List.foldl_cons,ih,Realizer.fold_cons_eq]
    simp only [List.flatten_cons,List.reverse_append,List.append_assoc]

def flatten : Uniform (fun (i : I) (xs : List (List (α i))) => xs.flatten) :=
  (((id.pair nil).comp cons.fold.fold).comp reverse).congr (fun _ _ => by
    simp only [Function.comp_apply,flatten_fold_eq,List.append_nil,List.reverse_reverse])

def flatMap {f : ∀ i, α i × γ i → List (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.flatMap (fun a => f i (a,x.2))) :=
  (R.map.comp flatten).congr (fun _ _ => rfl)

def filterBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : α i × (γ i × List (α i))) =>
      (x.2.1,if p i (x.1,x.2.1) then x.1 :: x.2.2 else x.2.2)) :=
  (snd.comp fst).pair
    (((fst.pair (snd.comp fst)).comp P).ite ((fst.pair (snd.comp snd)).comp cons) (snd.comp snd))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem filter_fold_eq (p : ∀ i, α i × γ i → Bool) (i : I)
    (xs : List (α i)) (e : γ i) (ys : List (α i)) :
    xs.foldl (fun s a => (s.1,if p i (a,s.1) then a :: s.2 else s.2)) (e,ys) =
      (e,(xs.filter (fun a => p i (a,e))).reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases he : p i (a,e) <;> simp [he,ih,List.append_assoc]

def filter {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.filter (fun a => p i (a,x.2))) :=
  (((fst.pair (snd.pair nil)).comp (filterBody P).fold).comp (snd.comp reverse)).congr (fun _ _ => by
    simp only [Function.comp_apply,filter_fold_eq,List.append_nil,List.reverse_reverse])

def optionToList : Uniform (fun (i : I) (x : Option (α i)) => x.toList) :=
  reinterpret _ (by intro i x; cases x <;> rfl)

def filterMap {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.filterMap (fun a => f i (a,x.2))) :=
  (R.comp optionToList).flatMap.congr (fun i x => by
    induction x.1 with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.flatMap_cons,List.filterMap_cons]
      cases he : f i (a,x.2) <;> simp_all)

def optionMap {f : ∀ i, α i × γ i → β i} (R : Uniform f) :
    Uniform (fun i (x : Option (α i) × γ i) => x.1.map (fun a => f i (a,x.2))) :=
  ((optionToList.onFst.comp R.map).comp head?).congr (fun i x => by
    rcases x with ⟨o,e⟩
    cases o <;> rfl)

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u22} {α : I → Type u23} {β : I → Type u24} {γ : I → Type u25}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def constant {δ : Type u26} [Coding δ] (a : δ) :
    Uniform (fun (i : I) (_ : α i) => a) where
  transform := fun _ => enc a
  charge := _
  routine := Routine.constant (enc a)
  correct _ _ := rfl

def some : Uniform (fun (i : I) (a : α i) => Option.some a) where
  transform := fun x => .pair x .nil
  charge := _
  routine := Routine.identity.pair Routine.nil
  correct _ _ := rfl

def none : Uniform (fun (i : I) (_ : α i) => (Option.none : Option (β i))) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def optionIsSome : Uniform (fun (i : I) (x : Option (α i)) => x.isSome) :=
  test _ (by intro _ x; cases x <;> rfl)

def getD : Uniform (fun (i : I) (x : Option (α i) × α i) => x.1.getD x.2) :=
  (((fst.comp optionToList).pair snd).comp fst.fold).congr (fun _ x => by
    rcases x with ⟨o,a⟩; cases o <;> rfl)

def length : Uniform (fun (i : I) (xs : List (α i)) => xs.length) :=
  ((id.pair zero).comp (snd.comp (Realizer.succ.uniform I)).fold).congr (fun i xs => by
    have h : ∀ (ys : List (α i)) (n : ℕ),
        ys.foldl (fun n _ => n+1) n = n+ys.length := by
      intro ys; induction ys with
      | nil => intro n; simp
      | cons a ys ih => intro n; simp [ih]; omega
    simpa only [Function.comp_apply,Nat.zero_add] using h xs 0)

def iterate {f : ∀ i, α i → α i} (R : Uniform f) :
    Uniform (fun i (x : ℕ × α i) => (f i)^[x.1] x.2) :=
  ((Realizer.unroll.uniform I).onFst.comp (snd.comp R).fold).congr (fun i x =>
    Realizer.fold_replicate (f i) x.1 x.2)

def anyBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : α i × (γ i × Bool)) =>
      (x.2.1,x.2.2 || p i (x.1,x.2.1))) :=
  (snd.comp fst).pair
    (((snd.comp snd).pair ((fst.pair (snd.comp fst)).comp P)).comp (Realizer.or.uniform I))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem any_fold_eq (p : ∀ i, α i × γ i → Bool) (i : I)
    (xs : List (α i)) (e : γ i) (b : Bool) :
    xs.foldl (fun s a => (s.1,s.2 || p i (a,s.1))) (e,b) =
      (e,b || xs.any (fun a => p i (a,e))) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.or_assoc]

def any {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.any (fun a => p i (a,x.2))) :=
  (((fst.pair (snd.pair false)).comp (anyBody P).fold).comp snd).congr (fun _ _ => by
    simp only [Function.comp_apply,any_fold_eq,Bool.false_or])

def all {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.all (fun a => p i (a,x.2))) :=
  ((P.comp (Realizer.not.uniform I)).any.comp (Realizer.not.uniform I)).congr (fun _ x => by
    simp only [Function.comp_apply,List.all_eq_not_any_not])

def find? {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.find? (fun a => p i (a,x.2))) :=
  (P.filter.comp head?).congr (fun _ x => by
    dsimp only [Function.comp_apply]
    induction x.1 with
    | nil => rfl
    | cons a xs ih => cases he : p _ (a,x.2) <;> simp_all)

def firstResult {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => (x.1.filterMap (fun a => f i (a,x.2))).head?) :=
  R.filterMap.comp head?

def tableOf {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) =>
      x.1.filterMap (fun a => (f i (a,x.2)).map (fun b => (a,b)))) :=
  ((R.pair fst).comp ((swap : Uniform (fun i (x : β i × α i) => (x.2,x.1))).optionMap)).filterMap

end ThreeMachine.StackCompiler.Uniform

end

end OAI
end


section
-- module FiniteRoutines
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15

section

namespace ThreeMachine.StackCompiler

instance (n : ℕ) : Coding (Fin n) := ⟨fun x => enc x.val⟩
instance (n : ℕ) : Coding (Finset (Fin n)) := ⟨fun s => enc (s.sort (· ≤ ·))⟩

@[simp] theorem enc_fin {n : ℕ} (x : Fin n) : enc x = enc x.val := rfl
@[simp] theorem volume_fin {n : ℕ} (x : Fin n) : volume x = 2*x.val+1 := volume_nat x.val
@[simp] theorem enc_finset {n : ℕ} (s : Finset (Fin n)) :
    enc s = enc (s.sort (· ≤ ·)) := rfl

structure Cardinal (n : ℕ) where
  trivial : Unit
instance (n : ℕ) : Coding (Cardinal n) := ⟨fun _ => enc n⟩

structure Universe (n : ℕ) where
  trivial : Unit
instance (n : ℕ) : Coding (Universe n) := ⟨fun _ => enc (List.finRange n)⟩

theorem enc_list_map {α : Type u1} {β : Type u2} [Coding α] [Coding β] (f : α → β)
    (hf : ∀ x, enc (f x) = enc x) (xs : List α) : enc (xs.map f) = enc xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,enc_cons,hf,ih]

theorem sort_filter {n : ℕ} (s : Finset (Fin n)) (p : Fin n → Bool) :
    (s.filter (fun x => p x)).sort (· ≤ ·) = (s.sort (· ≤ ·)).filter p := by
  have he : ((s.sort (· ≤ ·)).filter p).toFinset = s.filter (fun x => p x) := by
    ext x; simp
  rw [← he]
  exact (List.toFinset_sort (· ≤ ·) ((s.sort_nodup (· ≤ ·)).filter p)).mpr
    ((s.pairwise_sort (· ≤ ·)).filter p)

namespace Uniform

def finVal : Uniform (fun n (x : Fin n) => x.val) := reinterpret _ (fun _ _ => rfl)

def finEq : Uniform (fun n (x : Fin n × Fin n) => decide (x.1 = x.2)) :=
  (((fst.comp finVal).pair (snd.comp finVal)).comp (Realizer.eqNat.uniform ℕ)).congr
    (fun _ x => by simp only [Function.comp_apply,Fin.val_inj])

def universeList : Uniform (fun n (_ : Universe n) => List.finRange n) :=
  reinterpret _ (fun _ _ => rfl)

def universeSet : Uniform (fun n (_ : Universe n) => (Finset.univ : Finset (Fin n))) :=
  reinterpret _ (fun n _ => by simp only [enc_finset,Fin.sort_univ]; rfl)

def setList : Uniform (fun n (s : Finset (Fin n)) => s.sort (· ≤ ·)) :=
  reinterpret _ (fun _ _ => rfl)

def setEmpty : Uniform (fun n (_ : Universe n) => (∅ : Finset (Fin n))) where
  transform := fun _ => .nil
  charge := _
  routine := Routine.nil
  correct _ _ := by simp only [enc_finset,Finset.sort_empty]; rfl

def setIsEmpty : Uniform (fun n (s : Finset (Fin n)) => decide (s = ∅)) :=
  ((setList.comp isCons).comp (Realizer.not.uniform ℕ)).congr (fun _ x => by
    by_cases h : x = ∅
    · subst x; simp
    · have hh : x.sort (· ≤ ·) ≠ [] := by
        intro he; have := congrArg List.toFinset he
        exact h (by simpa only [Finset.sort_toFinset,List.toFinset_nil] using this)
      simp [Function.comp_apply,List.isEmpty_eq_false_iff,hh,h])

def setCard : Uniform (fun n (s : Finset (Fin n)) => s.card) :=
  (setList.comp length).congr (fun _ _ => Finset.length_sort (· ≤ ·))

def setFilter {γ : ℕ → Type u3} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) :
    Uniform (fun n (x : Finset (Fin n) × γ n) => x.1.filter (fun a => p n (a,x.2))) where
  transform := (setList.onFst.comp P.filter).transform
  charge := (setList.onFst.comp P.filter).charge
  routine := (setList.onFst.comp P.filter).routine
  correct n x := by
    rw [(setList.onFst.comp P.filter).correct]
    simp only [Function.comp_apply,enc_finset,sort_filter]

def setMem : Uniform (fun n (x : Fin n × Finset (Fin n)) => decide (x.1 ∈ x.2)) :=
  ((((snd.comp setList).pair fst).comp finEq.any)).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_eq_true,decide_eq_true_eq]
    simp)

def setInter : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => x.1 ∩ x.2) :=
  setMem.setFilter.congr (fun _ x => by ext a; simp)

def setDiff : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => x.1 \ x.2) :=
  (setMem.comp (Realizer.not.uniform ℕ)).setFilter.congr (fun _ x => by ext a; simp)

def setSubset : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => decide (x.1 ⊆ x.2)) :=
  ((setList.onFst).comp setMem.all).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_eq_true,decide_eq_true_eq,Finset.mem_sort]
    rfl)

def setEq : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => decide (x.1 = x.2)) :=
  ((setSubset.pair (swap.comp setSubset)).comp (Realizer.and.uniform ℕ)).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp [Finset.Subset.antisymm_iff])

def setDisjoint : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => decide (Disjoint x.1 x.2)) :=
  (setInter.comp setIsEmpty).congr (fun _ x => by
    simp only [Function.comp_apply,Finset.disjoint_iff_inter_eq_empty])

def setUnionBody : Uniform (fun n (x : Fin n × (Finset (Fin n) × Finset (Fin n))) =>
    decide (x.1 ∈ x.2.1 ∨ x.1 ∈ x.2.2)) :=
  ((((fst.pair (snd.comp fst)).comp setMem).pair
      ((fst.pair (snd.comp snd)).comp setMem)).comp (Realizer.or.uniform ℕ)).congr (fun _ _ => by simp)

def setUnion : Uniform (fun n (x : Universe n × (Finset (Fin n) × Finset (Fin n))) =>
    x.2.1 ∪ x.2.2) :=
  (((fst.comp universeSet).pair snd).comp setUnionBody.setFilter).congr (fun _ x => by
    ext a; simp)

def setCompl : Uniform (fun n (x : Universe n × Finset (Fin n)) => x.2ᶜ) :=
  (((fst.comp universeSet).pair snd).comp setDiff).congr (fun _ x => (Finset.compl_eq_univ_sdiff x.2).symm)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer

def rangeStep : Realizer (fun x : ℕ × List ℕ => (x.1+1,x.1 :: x.2)) :=
  (fst.comp succ).pair cons

theorem rangeStep_iterate (n : ℕ) :
    (fun x : ℕ × List ℕ => (x.1+1,x.1 :: x.2))^[n] (0,[]) = (n,(List.range n).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [List.range_succ]

def range : Realizer List.range :=
  (((id.pair (zero.pair nil)).comp rangeStep.iterate).comp (snd.comp reverse)).congr (fun n => by
    simp only [Function.comp_apply,rangeStep_iterate,List.reverse_reverse,id_eq])

end Realizer

theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last,List.map_append,List.map_map]
    simpa only [Function.comp_def,Fin.val_castSucc,List.map_cons,List.map_nil,Fin.val_last,ih]
      using (List.range_succ (n := n)).symm

namespace Uniform

def makeUniverse : Uniform (fun n (_ : Cardinal n) => (Universe.mk () : Universe n)) where
  transform := Realizer.range.transform
  charge := Realizer.range.charge
  routine := Realizer.range.routine
  correct n _ := by
    change Realizer.range.transform (enc n) = enc (List.finRange n)
    rw [Realizer.range.correct,← finRange_val]
    exact enc_list_map Fin.val (fun _ => rfl) _

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
variable {α : Type u4} [Coding α]

theorem volume_append (xs ys : List α) : volume (xs ++ ys)+1 = volume xs+volume ys := by
  induction xs with
  | nil => simp [Nat.add_comm]
  | cons a xs ih => simp only [List.cons_append,volume_cons]; omega

theorem volume_reverse (xs : List α) : volume xs.reverse = volume xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.reverse_cons]
    have := volume_append xs.reverse [a]
    simp only [volume_cons,volume_nil,ih] at this ⊢
    omega

namespace Uniform
variable {I : Type u5} {α : I → Type u6} {β : I → Type u7} {γ : I → Type u8}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}

@[simp] theorem time_id (i : I) (x : α i) :
    (id : Uniform (fun i (x : α i) => x)).time i x = volume x+2 := rfl
@[simp] theorem time_fst (i : I) (x : α i × β i) :
    (fst : Uniform (fun i (x : α i × β i) => x.1)).time i x = volume x+2 := rfl
@[simp] theorem time_snd (i : I) (x : α i × β i) :
    (snd : Uniform (fun i (x : α i × β i) => x.2)).time i x = volume x+2 := rfl
@[simp] theorem time_nil (i : I) (x : α i) :
    (nil : Uniform (fun i (_ : α i) => ([] : List (β i)))).time i x = 2 := rfl
@[simp] theorem time_unit (i : I) (x : α i) :
    (unit : Uniform (fun i (_ : α i) => ())).time i x = 2 := rfl
@[simp] theorem time_zero (i : I) (x : α i) :
    (zero : Uniform (fun i (_ : α i) => (0 : ℕ))).time i x = 2 := rfl
@[simp] theorem time_false (i : I) (x : α i) :
    (false : Uniform (fun i (_ : α i) => Bool.false)).time i x = 2 := rfl
@[simp] theorem time_congr {f' : ∀ i, α i → β i} (R : Uniform f)
    (h : ∀ i x, f i x = f' i x) (i : I) (x : α i) :
    (R.congr h).time i x = R.time i x := rfl
@[simp] theorem time_reinterpret (f : ∀ i, α i → β i) (h : ∀ i x, enc (f i x) = enc x)
    (i : I) (x : α i) : (reinterpret f h).time i x = volume x+2 := rfl
@[simp] theorem time_cons (i : I) (x : α i × List (α i)) : cons.time i x = volume x+2 := rfl

theorem time_comp (R : Uniform f) (S : Uniform g) (i : I) (x : α i) :
    (R.comp S).time i x = R.time i x+S.time i (f i x)+10*(volume (f i x)+1) := by
  simp only [comp,time,Routine.comp,R.correct,volume]

theorem time_pair {g : ∀ i, α i → γ i} (R : Uniform f) (S : Uniform g) (i : I) (x : α i) :
    (R.pair S).time i x = R.time i x+S.time i x+20*(volume x+volume (f i x)+volume (g i x)+1) := by
  simp only [pair,time,Routine.pair,R.correct,S.correct,volume]

theorem time_fold {F : ∀ i, α i × β i → β i} (R : Uniform F) (i : I) (x : List (α i) × β i) :
    R.fold.time i x = 2*volume x+6+Realizer.foldTime (R.specialize i) x.2 x.1 :=
  (R.specialize i).time_fold x

theorem time_choose {g : ∀ i, α i → β i} (R : Uniform f) (S : Uniform g)
    (i : I) (x : Bool × α i) :
    (R.choose S).time i x = ((snd (α := fun _ : I => Bool) (β := α)).comp R).time i x+
      ((snd (α := fun _ : I => Bool) (β := α)).comp S).time i x+
      30*(volume x+volume (f i x.2)+volume (g i x.2)+1) :=
  (R.specialize i).time_choose (S.specialize i) x

theorem time_constant {δ : Type u9} [Coding δ] (a : δ) (i : I) (x : α i) :
    (constant a : Uniform (fun i (_ : α i) => a)).time i x =
      (2*volume a+1)*(20*volume x+50*volume a+50) := rfl

theorem time_reverse (i : I) (xs : List (α i)) :
    reverse.time i xs ≤ 200*(xs.length+1)*(volume xs+1) := by
  have hf : ∀ (xs ys : List (α i)),
      Realizer.foldTime ((cons : Uniform (fun i (x : α i × List (α i)) => x.1 :: x.2)).specialize i) ys xs ≤
        xs.length * (100*(volume xs+volume ys+1))+1 := by
    intro xs; induction xs with
    | nil => intro ys; simp only [Realizer.foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
    | cons a xs ih =>
      intro ys
      have hh := ih (a :: ys)
      change volume (a,ys)+2+Realizer.foldTime _ (a :: ys) xs+
        20*(volume (a :: xs)+volume ys+volume (a :: ys)+1) ≤ _
      simp only [volume_pair,volume_cons,List.length_cons] at hh ⊢
      nlinarith [volume_pos a,volume_pos xs,volume_pos ys]
  simp only [reverse,time_congr,time_comp,time_pair,time_id,time_nil,time_fold,volume_pair,volume_nil]
  have hh := hf xs []
  simp only [volume_nil] at hh
  nlinarith [volume_pos xs]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

instance {α : Type u10} [Coding α] (n : ℕ) : Coding (Fin n → α) := ⟨fun f => enc (List.ofFn f)⟩

@[simp] theorem enc_function {α : Type u11} [Coding α] {n : ℕ} (f : Fin n → α) :
    enc f = enc (List.ofFn f) := rfl

namespace Uniform
variable {I : Type u12} {α : I → Type u13} [∀ i, Coding (α i)]

def tail : Uniform (fun (i : I) (xs : List (α i)) => xs.tail) :=
  ⟨Data.tail,_,Routine.select Bool.false,fun _ xs => by cases xs <;> rfl⟩

def drop : Uniform (fun (i : I) (x : List (α i) × ℕ) => x.1.drop x.2) :=
  (swap.comp tail.iterate).congr (fun i x => by
    dsimp only [Function.comp_apply]
    have h : ∀ (n : ℕ) (xs : List (α i)), List.tail^[n] xs = xs.drop n := by
      intro n; induction n with
      | zero => intro xs; rfl
      | succ n ih => intro xs; rw [Function.iterate_succ_apply,ih,List.drop_tail]
    exact h x.2 x.1)

def getElem? : Uniform (fun (i : I) (x : List (α i) × ℕ) => x.1[x.2]?) :=
  (drop.comp head?).congr (fun _ _ => by simp only [Function.comp_apply,List.head?_drop])

def getElemD : Uniform (fun (i : I) (x : (List (α i) × ℕ) × α i) => x.1.1.getD x.1.2 x.2) :=
  (getElem?.onFst.comp getD).congr (fun _ _ => List.getD_eq_getElem?_getD.symm)

end Uniform

namespace Uniform
variable {α : ℕ → Type u14} {β : ℕ → Type u15} [∀ n, Coding (α n)] [∀ n, Coding (β n)]

def functionList : Uniform (fun n (f : Fin n → α n) => List.ofFn f) :=
  reinterpret _ (fun _ _ => rfl)

def functionGetOption : Uniform (fun n (x : (Fin n → α n) × Fin n) => Option.some (x.1 x.2)) :=
  (((fst.comp functionList).pair (snd.comp finVal)).comp getElem?).congr (fun _ x => by
    simp only [Function.comp_apply,List.getElem?_ofFn,dite_eq_left x.2.isLt])

def functionGet : Uniform (fun n (x : (Fin n → α n) × Fin n) => x.1 x.2) where
  transform := Data.head ∘ (functionGetOption (α := α)).transform
  charge := _
  routine := (functionGetOption (α := α)).routine.comp (Routine.select true)
  correct n x := by
    simp only [Function.comp_apply,(functionGetOption (α := α)).correct,enc_some,Data.head]

def vectorMap {f : ∀ n, Fin n × α n → β n} (R : Uniform f) :
    Uniform (fun n (x : Universe n × α n) => fun v => f n (v,x.2)) where
  transform := (universeList.onFst.comp R.map).transform
  charge := (universeList.onFst.comp R.map).charge
  routine := (universeList.onFst.comp R.map).routine
  correct n x := by
    rw [(universeList.onFst.comp R.map).correct]
    simp only [Function.comp_apply,enc_function,List.ofFn_eq_map]

end Uniform
end ThreeMachine.StackCompiler

end

end OAI
end


section
-- module ListRoutines
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18

section

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i × γ i → β i}

theorem time_mapBody (R : Uniform f) (i : I) (a : α i) (e : γ i) (ys : List (β i)) :
    (mapBody R).time i (a,(e,ys)) ≤ R.time i (a,e)+
      1000*(volume a+volume e+volume ys+volume (f i (a,e))+1) := by
  simp only [mapBody,time_pair,time_comp,time_fst,time_snd,time_cons,volume_pair,volume_cons,Function.comp_apply]
  omega

theorem foldTime_mapBody (R : Uniform f) (i : I) (e : γ i) (T : ℕ)
    (xs : List (α i)) (ys : List (β i))
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T) :
    Realizer.foldTime ((mapBody R).specialize i) (e,ys) xs ≤
      xs.length*(T+4000*(volume xs+volume e+volume (xs.map (fun a => f i (a,e)))+volume ys+1))+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have hta := hT a (by simp)
    have ht := ih (f i (a,e) :: ys) (fun a ha => hT a (by simp [ha]))
    have hb := time_mapBody R i a e ys
    simp only [Realizer.foldTime]
    change (mapBody R).time i (a,(e,ys))+
      Realizer.foldTime ((mapBody R).specialize i) (e,f i (a,e) :: ys) xs+
      20*(volume (a :: xs)+volume (e,ys)+volume (e,f i (a,e) :: ys)+1) ≤ _
    simp only [volume_pair,volume_cons,List.length_cons,List.map_cons] at ht hb ⊢
    nlinarith [volume_pos a,volume_pos e,volume_pos ys,volume_pos xs,volume_pos (f i (a,e))]

theorem time_map (R : Uniform f) (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T) :
    R.map.time i (xs,e) ≤
      30000*(xs.length+1)*(T+volume xs+volume e+volume (xs.map (fun a => f i (a,e)))+1) := by
  have hf := foldTime_mapBody R i e T xs [] hT
  have hr := time_reverse i ((xs.map (fun a => f i (a,e))).reverse)
  simp only [volume_nil] at hf
  simp only [List.length_reverse,List.length_map,volume_reverse] at hr
  simp only [map,time_congr,time_comp,time_pair,time_fst,time_snd,time_nil,time_fold,
    Function.comp_apply,Realizer.map_fold_eq,List.append_nil,volume_pair,volume_nil,volume_reverse]
  nlinarith [volume_pos xs,volume_pos e,volume_pos (xs.map (fun a => f i (a,e)))]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

def lookupList {K : Type u5} {V : Type u6} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (a,b) :: xs, k => if a = k then some b else lookupList xs k

namespace Uniform
variable {I : Type u7} {α : I → Type u8} {β : I → Type u9} {γ : I → Type u10}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def mapList {f : ∀ i, α i → β i} (R : Uniform f) :
    Uniform (fun i (xs : List (α i)) => xs.map (f i)) :=
  ((id.pair unit).comp (fst.comp R).map).congr (fun _ _ => rfl)

def mapOption {f : ∀ i, α i → β i} (R : Uniform f) :
    Uniform (fun i (x : Option (α i)) => x.map (f i)) :=
  ((id.pair unit).comp (fst.comp R).optionMap).congr (fun _ _ => rfl)

def optionOrElse : Uniform (fun (i : I) (x : Option (α i) × Option (α i)) => x.1.or x.2) :=
  (fst.comp optionIsSome).ite fst snd |>.congr (fun _ x => by
    rcases x with ⟨o,e⟩; cases o <;> rfl)

def lookup [∀ i, DecidableEq (α i)]
    (E : Uniform (fun i (x : α i × α i) => decide (x.1 = x.2))) :
    Uniform (fun i (x : List (α i × β i) × α i) => lookupList x.1 x.2) :=
  ((((fst.comp fst).pair snd).comp E).find?.comp snd.mapOption).congr (fun i x => by
    dsimp only [Function.comp_apply]
    induction x.1 with
    | nil => rfl
    | cons a xs ih =>
      by_cases ha : a.1 = x.2 <;> simp [lookupList,ha,ih])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u11} {J : Type u12} {α : I → Type u13} {β : I → Type u14} {γ : I → Type u15}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i}

def reindex (R : Uniform f) (φ : J → I) : Uniform (fun j => f (φ j)) where
  transform := R.transform
  charge := R.charge
  routine := R.routine
  correct j x := R.correct (φ j) x

def finValue (d : I → ℕ) : Uniform (fun i (x : Fin (d i)) => x.val) :=
  reinterpret _ (fun _ _ => rfl)

def cardinalValue (d : I → ℕ) : Uniform (fun i (_ : Cardinal (d i)) => d i) :=
  reinterpret _ (fun _ _ => rfl)

def universeListAny (d : I → ℕ) : Uniform (fun i (_ : Universe (d i)) => List.finRange (d i)) :=
  reinterpret _ (fun _ _ => rfl)

def makeUniverseAny (d : I → ℕ) : Uniform (fun i (_ : Cardinal (d i)) => (Universe.mk () : Universe (d i))) :=
  makeUniverse.reindex d

def functionListAny (d : I → ℕ) : Uniform (fun i (f : Fin (d i) → α i) => List.ofFn f) :=
  reinterpret _ (fun _ _ => rfl)

def functionGetOptionAny (d : I → ℕ) :
    Uniform (fun i (x : (Fin (d i) → α i) × Fin (d i)) => Option.some (x.1 x.2)) :=
  (((fst.comp (functionListAny d)).pair (snd.comp (finValue d))).comp getElem?).congr (fun _ x => by
    simp only [Function.comp_apply,List.getElem?_ofFn,dite_eq_left x.2.isLt])

def functionGetAny (d : I → ℕ) : Uniform (fun i (x : (Fin (d i) → α i) × Fin (d i)) => x.1 x.2) where
  transform := Data.head ∘ (functionGetOptionAny (α := α) d).transform
  charge := _
  routine := (functionGetOptionAny (α := α) d).routine.comp (Routine.select true)
  correct i x := by
    simp only [Function.comp_apply,(functionGetOptionAny (α := α) d).correct,enc_some,Data.head]

def vectorMapAny (d : I → ℕ) {f : ∀ i, Fin (d i) × α i → β i} (R : Uniform f) :
    Uniform (fun i (x : Universe (d i) × α i) => fun v => f i (v,x.2)) where
  transform := ((universeListAny d).onFst.comp R.map).transform
  charge := ((universeListAny d).onFst.comp R.map).charge
  routine := ((universeListAny d).onFst.comp R.map).routine
  correct i x := by
    rw [((universeListAny d).onFst.comp R.map).correct]
    simp only [Function.comp_apply,enc_function,List.ofFn_eq_map]

def recode {H : Type u16} {δ : H → Type u17} {ε : H → Type u18} [∀ h, Coding (δ h)] [∀ h, Coding (ε h)]
    {g : ∀ h, δ h → ε h} (R : Uniform g) (f : ∀ i, α i → β i)
    (h : ∀ i x, ∃ j y, enc y = enc x ∧ enc (g j y) = enc (f i x)) : Uniform f where
  transform := R.transform
  charge := R.charge
  routine := R.routine
  correct i x := by
    obtain ⟨j,y,hin,hout⟩ := h i x
    rw [← hin,R.correct,hout]

def cardinalMap (d : I → ℕ) {g : ℕ → ℕ} (R : Realizer g) :
    Uniform (fun i (_ : Cardinal (d i)) => (Cardinal.mk () : Cardinal (g (d i)))) where
  transform := R.transform
  charge := R.charge
  routine := R.routine
  correct i _ := R.correct (d i)

end ThreeMachine.StackCompiler.Uniform

end

end OAI
end


section
-- module ProgramRoutines
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

instance (n : ℕ) : Coding (Algorithm.State (Fin n)) :=
  ⟨fun s => enc (s.left,(s.middle,s.right))⟩
instance (n : ℕ) : Coding (Algorithm.Block (Fin n)) :=
  ⟨fun s => enc (s.length,s.time)⟩

abbrev Matrix (n : ℕ) := Fin n → Fin n → Bool

def matrixRel {n : ℕ} (M : Matrix n) (x y : Fin n) : Prop := M x y = true

instance {n : ℕ} (M : Matrix n) : DecidableRel (matrixRel M) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

namespace Uniform

def universeNumber : Uniform (fun n (_ : Universe n) => n) :=
  (universeList.comp length).congr (fun _ _ => List.length_finRange)

def stateParts : Uniform (fun n (s : Algorithm.State (Fin n)) => (s.left,(s.middle,s.right))) :=
  reinterpret _ (fun _ _ => rfl)

def stateMake : Uniform (fun n (x : Finset (Fin n) × (Finset (Fin n) × Finset (Fin n))) =>
    (⟨x.1,x.2.1,x.2.2⟩ : Algorithm.State (Fin n))) :=
  reinterpret _ (fun _ _ => rfl)

def stateLeft : Uniform (fun n (s : Algorithm.State (Fin n)) => s.left) := stateParts.comp fst

def stateMiddle : Uniform (fun n (s : Algorithm.State (Fin n)) => s.middle) := stateParts.comp (snd.comp fst)

def stateRight : Uniform (fun n (s : Algorithm.State (Fin n)) => s.right) := stateParts.comp (snd.comp snd)

def stateEq : Uniform (fun n (x : Algorithm.State (Fin n) × Algorithm.State (Fin n)) =>
    decide (x.1 = x.2)) :=
  (((((fst.comp stateLeft).pair (snd.comp stateLeft)).comp setEq).pair
    (((((fst.comp stateMiddle).pair (snd.comp stateMiddle)).comp setEq).pair
      (((fst.comp stateRight).pair (snd.comp stateRight)).comp setEq)).comp (Realizer.and.uniform ℕ))).comp
    (Realizer.and.uniform ℕ)).congr (fun _ x => by
      rcases x with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
      apply Bool.eq_iff_iff.mpr
      simp)

def blockParts : Uniform (fun n (s : Algorithm.Block (Fin n)) => (s.length,s.time)) :=
  reinterpret _ (fun _ _ => rfl)

def blockMake : Uniform (fun n (x : ℕ × (Fin n → ℕ)) => (⟨x.1,x.2⟩ : Algorithm.Block (Fin n))) :=
  reinterpret _ (fun _ _ => rfl)

def blockLength : Uniform (fun n (s : Algorithm.Block (Fin n)) => s.length) := blockParts.comp fst

def blockTime : Uniform (fun n (s : Algorithm.Block (Fin n)) => s.time) := blockParts.comp snd

def matrixGet : Uniform (fun n (x : Matrix n × (Fin n × Fin n)) => x.1 x.2.1 x.2.2) :=
  ((((fst.pair (snd.comp fst)).comp functionGet).pair (snd.comp snd)).comp functionGet)

def setAll {γ : ℕ → Type u1} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) :
    Uniform (fun n (x : Finset (Fin n) × γ n) => decide (∀ a ∈ x.1, p n (a,x.2) = true)) :=
  (setList.onFst.comp P.all).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_eq_true,Finset.mem_sort,decide_eq_true_eq])

def setAny {γ : ℕ → Type u2} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) :
    Uniform (fun n (x : Finset (Fin n) × γ n) => decide (∃ a ∈ x.1, p n (a,x.2) = true)) :=
  (setList.onFst.comp P.any).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_eq_true,Finset.mem_sort,decide_eq_true_eq])

variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

def andD {p q : ∀ i, α i → Prop} [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x))) :
    Uniform (fun i x => decide (p i x ∧ q i x)) :=
  ((P.pair Q).comp (Realizer.and.uniform I)).congr (fun _ _ => by simp)

def orD {p q : ∀ i, α i → Prop} [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x))) :
    Uniform (fun i x => decide (p i x ∨ q i x)) :=
  ((P.pair Q).comp (Realizer.or.uniform I)).congr (fun _ _ => by simp)

def noEdges : Uniform (fun n (x : Matrix n × (Finset (Fin n) × Finset (Fin n))) =>
    decide (∀ a ∈ x.2.1, ∀ b ∈ x.2.2, ¬matrixRel x.1 a b)) := by
  let E : Uniform (fun n (x : Fin n × (Matrix n × Fin n)) => !x.2.1 x.2.2 x.1) :=
    (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp matrixGet).comp (Realizer.not.uniform ℕ)
  let F : Uniform (fun n (x : Fin n × (Matrix n × Finset (Fin n))) =>
      decide (∀ b ∈ x.2.2, ¬matrixRel x.2.1 x.1 b)) :=
    (((snd.comp snd).pair ((snd.comp fst).pair fst)).comp E.setAll).congr (fun _ _ => by
      simp only [Function.comp_apply,Bool.not_eq_true,matrixRel,Bool.not_eq_true'])
  exact (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp F.setAll).congr (fun _ _ => by
    simp only [Function.comp_apply,decide_eq_true_eq])

def stateCandidate : Uniform (fun n (x : Universe n ×
    (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)))) =>
      Algorithm.State.candidate x.2.1 x.2.2.1 x.2.2.2) := by
  let L := (((snd.comp fst).pair (snd.comp (snd.comp fst))).comp setInter :
    Uniform (fun n (x : Universe n × (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)))) => x.2.1 ∩ x.2.2.1))
  let Z := (snd.comp (snd.comp snd) :
    Uniform (fun n (x : Universe n × (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)))) => x.2.2.2))
  exact (L.pair (Z.pair (((snd.comp fst).pair ((fst.pair (L.pair Z)).comp setUnion)).comp setDiff))).comp stateMake

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm
namespace Uniform

def stateUpto : Uniform (fun n (x : Universe n × Algorithm.State (Fin n)) => x.2.upto) :=
  (fst.pair ((snd.comp stateLeft).pair (snd.comp stateMiddle))).comp setUnion

abbrev CompatInput (n : ℕ) := Universe n × (Matrix n × (Finset (Fin n) × Algorithm.State (Fin n)))
def scU : Uniform (fun n (x : CompatInput n) => x.1) := fst
def scM : Uniform (fun n (x : CompatInput n) => x.2.1) := snd.comp fst
def scW : Uniform (fun n (x : CompatInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def scS : Uniform (fun n (x : CompatInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def scL := scS.comp stateLeft
def scZ := scS.comp stateMiddle
def scR := scS.comp stateRight
def scLZ := (scU.pair (scL.pair scZ)).comp setUnion
def scLZR := (scU.pair (scLZ.pair scR)).comp setUnion
def scA := (scLZR.pair scW).comp setEq
def scB := (scL.pair scZ).comp setDisjoint
def scC := (scL.pair scR).comp setDisjoint
def scD := (scZ.pair scR).comp setDisjoint
def scE := ((scZ.comp setCard).pair (constant 3)).comp (Realizer.eqNat.uniform ℕ)
def scF := (scM.pair (scZ.pair scZ)).comp noEdges
def scH := (scM.pair (scZ.pair scL)).comp noEdges
def scI := (scM.pair (scR.pair scL)).comp noEdges
def scJ := (scM.pair (scR.pair scZ)).comp noEdges
def scIJ := scI.andD scJ
def scHIJ := scH.andD scIJ
def scFHIJ := scF.andD scHIJ
def scEFHIJ := scE.andD scFHIJ
def scDEFHIJ := scD.andD scEFHIJ
def scCDEFHIJ := scC.andD scDEFHIJ
def scBCDEFHIJ := scB.andD scCDEFHIJ
def scAll := scA.andD scBCDEFHIJ
def stateCompatible : Uniform (fun n (x : Universe n ×
     (Matrix n × (Finset (Fin n) × Algorithm.State (Fin n)))) =>
      decide (x.2.2.2.Compatible (matrixRel x.2.1) x.2.2.1)) :=
  scAll.congr (fun _ _ => by apply decide_eq_decide.mpr; rfl)

def blockEmpty : Uniform (fun n (_ : Universe n) => (Algorithm.Block.empty : Algorithm.Block (Fin n))) :=
  (zero.pair ((id.pair unit).comp zero.vectorMap)).comp blockMake

def blockTriple : Uniform (fun n (_ : Universe n) => (Algorithm.Block.triple : Algorithm.Block (Fin n))) :=
  ((constant 1).pair ((id.pair unit).comp (constant 1).vectorMap)).comp blockMake

def blockAppend : Uniform (fun n (x : Universe n ×
    (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) =>
      Algorithm.Block.append x.2.1 x.2.2.1 x.2.2.2) := by
  let F : Uniform (fun n (x : Fin n ×
      (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) =>
      if x.1 ∈ x.2.1 then x.2.2.1.time x.1 else x.2.2.1.length+x.2.2.2.time x.1) := by
    let S := (snd.comp (snd.comp fst) : Uniform (fun n (x : Fin n ×
      (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.1))
    let T := (snd.comp (snd.comp snd) : Uniform (fun n (x : Fin n ×
      (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.2))
    exact (((fst.pair (snd.comp fst)).comp setMem).ite
      (((S.comp blockTime).pair fst).comp functionGet)
      (((S.comp blockLength).pair (((T.comp blockTime).pair fst).comp functionGet)).comp
        (Realizer.add.uniform ℕ))).congr (fun _ _ => by simp)
  exact ((((snd.comp (snd.comp fst)).comp blockLength).pair
      ((snd.comp (snd.comp snd)).comp blockLength)).comp (Realizer.add.uniform ℕ)).pair
      F.vectorMap |>.comp blockMake

def stateAdvance : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) =>
      x.2.1.advance x.2.2.1 x.2.2.2) := by
  let U := (fst : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.1))
  let V := (snd.comp fst : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.1))
  let S := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.1))
  let T := (snd.comp (snd.comp snd) : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.2))
  let B := (U.pair ((V.comp stateLeft).pair (S.pair (U.comp blockTriple)))).comp blockAppend
  exact (U.pair (((U.pair V).comp stateUpto).pair (B.pair T))).comp blockAppend

variable {I : Type u5} {α β γ : I → Type}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def lookupA [∀ i, DecidableEq (α i)]
    (E : Uniform (fun i (x : α i × α i) => decide (x.1 = x.2))) :
    Uniform (fun i (x : List (α i × β i) × α i) => Algorithm.lookup x.1 x.2) :=
  (lookup E).congr (fun _ x => by
    induction x.1 with
    | nil => rfl
    | cons a xs ih => simp only [lookupList,Algorithm.lookup]; split <;> simp_all)

def firstResultA {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => Algorithm.firstResult (fun a => f i (a,x.2)) x.1) :=
  R.firstResult.congr (fun _ x => by
    induction x.1 with
    | nil => rfl
    | cons a xs ih => simp only [List.filterMap_cons,Algorithm.firstResult]; cases f _ (a,x.2) <;> simp_all)

def tableOfA {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => Algorithm.tableOf x.1 (fun a => f i (a,x.2))) :=
  R.tableOf

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm
abbrev Table (n : ℕ) := List (Finset (Fin n) × Algorithm.Block (Fin n))
abbrev Marks (n : ℕ) := List (Algorithm.State (Fin n) × Algorithm.Block (Fin n))
namespace Uniform

variable {I : Type u6} {α : I → Type u7} {β : I → Type u8}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)]

def singleton : Uniform (fun i (a : α i) => [a]) := (id.pair nil).comp cons

def product : Uniform (fun i (x : List (α i) × List (β i)) => x.1.product x.2) :=
  ((snd.pair fst).comp swap.map).flatMap.congr (fun _ _ => rfl)

def states : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) =>
      Algorithm.states (matrixRel x.2.1) x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let C : Uniform (fun n (x : (Finset (Fin n) × Finset (Fin n)) ×
      (Universe n × Finset (Fin n))) => Algorithm.State.candidate x.2.2 x.1.1 x.1.2) :=
    ((snd.comp fst).pair ((snd.comp snd).pair ((fst.comp fst).pair (fst.comp snd)))).comp stateCandidate
  let F := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) => x.2.2.1))
  let Z := (snd.comp (snd.comp (snd.comp fst)) : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) => x.2.2.2.1))
  let W := (snd.comp (snd.comp (snd.comp snd)) : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) => x.2.2.2.2))
  let S := (((F.pair Z).comp product).pair (fst.pair W)).comp C.map
  let P : Uniform (fun n (x : Algorithm.State (Fin n) ×
      (Universe n × (Matrix n × Finset (Fin n)))) =>
      decide (x.1.Compatible (matrixRel x.2.2.1) x.2.2.2)) :=
    ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair ((snd.comp (snd.comp snd)).pair fst))).comp stateCompatible
  exact ((S.pair (fst.pair ((snd.comp fst).pair W))).comp P.filter).congr (fun _ x => by
    simp only [Function.comp_apply,Algorithm.states,List.product,List.map_flatMap,List.map_map]
    rfl)

def advanceLast : Uniform (fun n (x : Algorithm.Block (Fin n) ×
    (Universe n × (Algorithm.State (Fin n) × Algorithm.Block (Fin n)))) =>
      x.2.2.1.advance x.2.2.2 x.1) :=
  ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair ((snd.comp (snd.comp snd)).pair fst))).comp stateAdvance

def tryAdvance : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) =>
      Algorithm.tryAdvance x.2.1 x.2.2.1 x.2.2.2) := by
  let U := (fst : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.1))
  let T := (snd.comp fst : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.2.1))
  let A := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.2.2.1))
  let V := (snd.comp (snd.comp snd) : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.2.2.2))
  let W := (U.pair (A.comp fst)).comp stateUpto
  let L := V.comp stateLeft
  let P := (W.pair L).comp setSubset
  let O := (T.pair ((L.pair W).comp setDiff)).comp (lookupA setEq)
  exact (P.ite ((O.pair (U.pair A)).comp advanceLast.optionMap) none).congr (fun _ _ => by
    simp only [Function.comp_apply,Algorithm.tryAdvance,decide_eq_true_eq])

def expandBody : Uniform (fun n (x : Algorithm.State (Fin n) ×
    (Universe n × (Table n × Marks n))) =>
      match Algorithm.lookup x.2.2.2 x.1 with
      | Option.some s => Option.some s
      | Option.none => Algorithm.firstResult (fun u => Algorithm.tryAdvance x.2.2.1 u x.1) x.2.2.2) := by
  let A : Uniform (fun n (x : (Algorithm.State (Fin n) × Algorithm.Block (Fin n)) ×
      (Universe n × (Table n × Algorithm.State (Fin n)))) =>
      Algorithm.tryAdvance x.2.2.1 x.1 x.2.2.2) :=
    ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair (fst.pair (snd.comp (snd.comp snd))))).comp tryAdvance
  let O := (((snd.comp (snd.comp snd)).pair fst).comp (lookupA stateEq) :
    Uniform (fun n (x : Algorithm.State (Fin n) × (Universe n × (Table n × Marks n))) =>
      Algorithm.lookup x.2.2.2 x.1))
  let B := ((snd.comp (snd.comp snd)).pair
      ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair fst))).comp A.firstResultA
  exact ((O.pair B).comp optionOrElse).congr (fun _ x => by
    simp only [Function.comp_apply]; cases Algorithm.lookup x.2.2.2 x.1 <;> rfl)

def expand : Uniform (fun n (x : Universe n ×
    (Table n × (List (Algorithm.State (Fin n)) × Marks n))) =>
      Algorithm.expand x.2.1 x.2.2.1 x.2.2.2) :=
  ((snd.comp (snd.comp fst)).pair
    (fst.pair ((snd.comp fst).pair (snd.comp (snd.comp snd))))).comp expandBody.tableOfA |>.congr
      (fun _ x => by
        simp only [Function.comp_apply,Algorithm.expand]
        congr 1
        funext v
        cases Algorithm.lookup x.2.2.2 v <;> rfl)

def initialMarks : Uniform (fun n (x : Table n × List (Algorithm.State (Fin n))) =>
    Algorithm.tableOf x.2 (fun v => Algorithm.lookup x.1 v.left)) :=
  (swap.comp ((snd.pair (fst.comp stateLeft)).comp (lookupA setEq)).tableOfA)

def markings : Uniform (fun n (x : ℕ ×
    (Universe n × (Table n × List (Algorithm.State (Fin n))))) =>
      Algorithm.markings x.2.2.1 x.2.2.2 x.1) := by
  let F : Uniform (fun n (x : (Universe n × (Table n × List (Algorithm.State (Fin n)))) × Marks n) =>
      (x.1,Algorithm.expand x.1.2.1 x.1.2.2 x.2)) :=
    fst.pair ((((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
      ((fst.comp (snd.comp snd)).pair snd)))).comp expand)
  exact (((fst.pair (snd.pair (snd.comp (snd.comp initialMarks)))).comp F.iterate).comp snd).congr
    (fun n x => by
      dsimp only [Function.comp_apply]
      have h : ∀ k, (fun p => (p.1,Algorithm.expand p.1.2.1 p.1.2.2 p.2))^[k]
          (x.2,Algorithm.tableOf x.2.2.2 (fun v => Algorithm.lookup x.2.2.1 v.left)) =
          (x.2,Algorithm.markings x.2.2.1 x.2.2.2 k) := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
      rw [h])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm
namespace Uniform

def finishing : Uniform (fun n (x : (Algorithm.State (Fin n) × Algorithm.Block (Fin n)) ×
    (Universe n × Table n)) =>
      (Algorithm.lookup x.2.2 x.1.1.right).map (x.1.1.finish x.1.2)) :=
  ((((snd.comp snd).pair ((fst.comp fst).comp stateRight)).comp (lookupA setEq)).pair
    ((snd.comp fst).pair fst)).comp advanceLast.optionMap

def solve : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) =>
      Algorithm.solve (matrixRel x.2.1) x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  let U := (fst : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.1))
  let M := (snd.comp fst : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.1))
  let T := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.1))
  let F := (snd.comp (snd.comp (snd.comp fst)) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.2.1))
  let Z := (snd.comp (snd.comp (snd.comp (snd.comp fst))) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.2.2.1))
  let W := (snd.comp (snd.comp (snd.comp (snd.comp snd))) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.2.2.2))
  let S := (U.pair (M.pair (F.pair (Z.pair W)))).comp states
  let Marks := ((U.comp universeNumber).pair (U.pair (T.pair S))).comp markings
  let Out := (Marks.pair (U.pair T)).comp finishing.firstResultA
  exact ((W.comp setIsEmpty).ite (U.comp (blockEmpty.comp some)) Out).congr (fun _ _ => by
    simp only [Function.comp_apply,Algorithm.solve,decide_eq_true_eq,Fintype.card_fin])

def initialTable : Uniform (fun n (_ : Universe n) => ([(∅,Algorithm.Block.empty)] : Table n)) :=
  (setEmpty.pair blockEmpty).comp singleton

def layerStep : Uniform (fun n (x : (Universe n × (Matrix n ×
    (List (Finset (Fin n)) × List (Finset (Fin n))))) × Table n) =>
      (x.1,Algorithm.tableOf x.1.2.2.1
        (Algorithm.solve (matrixRel x.1.2.1) x.2 x.1.2.2.1 x.1.2.2.2))) := by
  let B : Uniform (fun n (x : Finset (Fin n) ×
      ((Universe n × (Matrix n × (List (Finset (Fin n)) × List (Finset (Fin n))))) × Table n)) =>
      Algorithm.solve (matrixRel x.2.1.2.1) x.2.2 x.2.1.2.2.1 x.2.1.2.2.2 x.1) :=
    ((snd.comp (fst.comp fst)).pair ((snd.comp (fst.comp (snd.comp fst))).pair
      ((snd.comp snd).pair ((snd.comp (fst.comp (snd.comp (snd.comp fst)))).pair
        ((snd.comp (fst.comp (snd.comp (snd.comp snd)))).pair fst))))).comp solve
  exact fst.pair (((fst.comp (snd.comp (snd.comp fst))).pair id).comp B.tableOfA)

def layers : Uniform (fun n (x : ℕ × (Universe n × (Matrix n ×
    (List (Finset (Fin n)) × List (Finset (Fin n)))))) =>
      Algorithm.layers (matrixRel x.2.2.1) x.2.2.2.1 x.2.2.2.2 x.1) :=
  (((fst.pair (snd.pair ((snd.comp fst).comp initialTable))).comp layerStep.iterate).comp snd).congr
    (fun n x => by
      dsimp only [Function.comp_apply]
      have h : ∀ k, (fun p => (p.1,Algorithm.tableOf p.1.2.2.1
          (Algorithm.solve (matrixRel p.1.2.1) p.2 p.1.2.2.1 p.1.2.2.2)))^[k]
          (x.2,[(∅,Algorithm.Block.empty)]) =
          (x.2,Algorithm.layers (matrixRel x.2.2.1) x.2.2.2.1 x.2.2.2.2 k) := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
      rw [h])

end Uniform
end ThreeMachine.StackCompiler

end

end OAI
end


section
-- module FamilyRoutines
namespace OAI

universe u1 u2

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Structure ThreeMachine.Algorithm
namespace Uniform

variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]

def natLT : Uniform (fun (_ : I) (x : ℕ × ℕ) => decide (x.1 < x.2)) :=
  (swap.comp ((Realizer.le.uniform I).comp (Realizer.not.uniform I))).congr (fun _ x => by
    by_cases h : x.1 < x.2
    · have hn : ¬ x.2 ≤ x.1 := by omega
      simp [Function.comp_apply,h,hn]
    · have hn : x.2 ≤ x.1 := by omega
      simp [Function.comp_apply,h,hn])

def finCons (k : ℕ) : Uniform (fun i (x : α i × (Fin k → α i)) => (Fin.cons x.1 x.2 : Fin (k+1) → α i)) :=
  reinterpret _ (fun _ _ => by simp only [enc_function,List.ofFn_cons]; rfl)

def finEmpty : Uniform (fun i (_ : List (α i)) => (Fin.elim0 : Fin 0 → α i)) where
  transform := fun _ => .nil
  charge := _
  routine := Routine.nil
  correct _ _ := by simp only [enc_function,List.ofFn_zero]; rfl

def assignments : (k : ℕ) → Uniform (fun i (xs : List (α i)) => Structure.assignments xs k)
  | 0 => finEmpty.comp singleton
  | k+1 =>
    ((id.pair (assignments k)).comp ((snd.pair fst).comp (swap.comp (finCons k)).map).flatMap).congr
      (fun _ _ => rfl)

def tripleSet : Uniform (fun n (x : Universe n × (Fin n × (Fin n × Fin n))) =>
    ({x.2.1,x.2.2.1,x.2.2.2} : Finset (Fin n))) := by
  let P : Uniform (fun n (x : Fin n × (Fin n × (Fin n × Fin n))) =>
      decide (x.1 = x.2.1 ∨ x.1 = x.2.2.1 ∨ x.1 = x.2.2.2)) :=
    ((fst.pair (snd.comp fst)).comp finEq).orD
      (((fst.pair (snd.comp (snd.comp fst))).comp finEq).orD
        ((fst.pair (snd.comp (snd.comp snd))).comp finEq))
  exact (((fst.comp universeSet).pair snd).comp P.setFilter).congr (fun _ x => by
    ext a; simp only [Function.comp_apply,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,
      Finset.mem_insert,Finset.mem_singleton])

def triples : Uniform (fun n (_ : Universe n) =>
    (Structure.tripleList (List.finRange n)).map Subtype.val) := by
  let E := (universeList.pair (universeList.pair universeList |>.comp product)).comp product
  let A := (E.pair id).comp (swap.comp tripleSet).map
  let P : Uniform (fun n (x : Finset (Fin n) × Unit) => decide (x.1.card = 3)) :=
    (((fst.comp setCard).pair (constant 3)).comp (Realizer.eqNat.uniform ℕ))
  exact ((A.pair unit).comp P.filter).congr (fun n _ => by
    dsimp only [Function.comp_apply]
    simp only [Structure.tripleList,List.product,List.map_flatMap,List.map_map,List.map_filterMap]
    rw [← List.filterMap_eq_filter]
    congr 1
    funext Z
    by_cases h : Z.card = 3 <;> simp [Option.guard,h])

def predecessorCount : Uniform (fun n (x : Universe n × (Matrix n × Fin n)) =>
    Structure.predecessorCount (matrixRel x.2.1) x.2.2) :=
  ((((fst.comp universeSet).pair snd).comp
    (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp matrixGet).setFilter).comp setCard).congr
      (fun _ _ => rfl)

def predecessors : Uniform (fun n (x : Universe n × Matrix n) =>
    Structure.predecessorCount (matrixRel x.2)) :=
  ((fst.pair id).comp (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp predecessorCount).vectorMap)

def rankFromCounts : Uniform (fun n (x : Universe n × ((Fin n → ℕ) × Fin n)) =>
    (Finset.univ.filter (fun y => x.2.1 y < x.2.1 x.2.2 ∨
      x.2.1 y = x.2.1 x.2.2 ∧ y < x.2.2)).card+1) := by
  let A := (((snd.comp fst).pair fst).comp functionGet :
    Uniform (fun n (x : Fin n × ((Fin n → ℕ) × Fin n)) => x.2.1 x.1))
  let B := (((snd.comp fst).pair (snd.comp snd)).comp functionGet :
    Uniform (fun n (x : Fin n × ((Fin n → ℕ) × Fin n)) => x.2.1 x.2.2))
  let C := ((A.pair B).comp natLT)
  let D := ((A.pair B).comp (Realizer.eqNat.uniform ℕ))
  let E := (((fst.comp finVal).pair ((snd.comp snd).comp finVal)).comp natLT :
    Uniform (fun n (x : Fin n × ((Fin n → ℕ) × Fin n)) => decide (x.1 < x.2.2)))
  exact ((((fst.comp universeSet).pair snd).comp (C.orD (D.andD E)).setFilter).comp setCard).comp
    (Realizer.succ.uniform ℕ) |>.congr (fun _ _ => by
      simp only [Function.comp_apply,decide_eq_true_eq,Fin.lt_def])

def rank : Uniform (fun n (x : Universe n × Matrix n) => Structure.jobRank (matrixRel x.2)) :=
  ((fst.pair (fst.pair predecessors)).comp
    (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp rankFromCounts).vectorMap).congr (fun _ _ => by
      funext y
      simp only [Function.comp_apply,Structure.jobRank,Structure.rankOfKey,Structure.jobKey,
        Prod.Lex.toLex_lt_toLex])

def reverseRank : Uniform (fun n (x : Universe n × (Fin n → ℕ)) => fun v => n+1-x.2 v) :=
  ((fst.pair (((fst.comp universeNumber).comp (Realizer.succ.uniform ℕ)).pair snd)).comp
    (((snd.comp fst).pair (((snd.comp snd).pair fst).comp functionGet)).comp
      (Realizer.sub.uniform ℕ)).vectorMap)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Structure ThreeMachine.Algorithm

def coneSet {n : ℕ} (M : Matrix n) (frame : Bool) (kind : Fin 5) (Z : Finset (Fin n)) : Finset (Fin n) :=
  let R := fun x y => if frame then matrixRel M y x else matrixRel M x y
  match kind.val with
  | 0 => Z
  | 1 => Finset.univ.filter (fun x => ∃ y ∈ Z, R x y)
  | 2 => Finset.univ.filter (fun x => ∃ y ∈ Z, R y x)
  | 3 => (Finset.univ.filter (fun x => ∃ y ∈ Z, R x y)) ∪ Z
  | _ => (Finset.univ.filter (fun x => ∃ y ∈ Z, R y x)) ∪ Z

theorem atomicCone (n : ℕ) (M : Matrix n) (frame : Bool) (kind : Fin 5)
    (Z : {s : Finset (Fin n) // s.card = 3}) :
    Atomic.finsetEval (matrixRel M) (Structure.jobRank (matrixRel M))
      (Structure.reverseJobRank (matrixRel M)) (.cone frame kind Z) = coneSet M frame kind Z.val := by
  fin_cases kind <;> ext x <;> simp [Atomic.finsetEval,coneSet]

theorem map_finRange_nat {β : Type u2} (f : ℕ → β) (k : ℕ) :
    (List.finRange k).map (fun i => f i.val) = (List.range k).map f := by
  rw [← finRange_val k,List.map_map]
  rfl

theorem atomicThreshold {n : ℕ} (M : Matrix n) (frame upper : Bool) :
    (List.finRange (Fintype.card (Fin n)+2)).map (fun k =>
      Atomic.finsetEval (matrixRel M) (Structure.jobRank (matrixRel M))
        (Structure.reverseJobRank (matrixRel M)) (.threshold frame upper k)) =
    (List.range (n+2)).map (fun k => Finset.univ.filter (fun v => if upper then
      (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v ≤ k
      else k ≤ (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v)) := by
  let f : ℕ → Finset (Fin n) := fun k => Finset.univ.filter (fun v => if upper then
      (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v ≤ k
      else k ≤ (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v)
  change (List.finRange (Fintype.card (Fin n)+2)).map (fun k => f k.val) = (List.range (n+2)).map f
  rw [map_finRange_nat,Fintype.card_fin]

namespace Uniform

def thresholdSets (upper : Bool) : Uniform (fun n (x : Universe n × (Fin n → ℕ)) =>
    (List.range (n+2)).map (fun k => Finset.univ.filter
      (fun v => if upper then x.2 v ≤ k else k ≤ x.2 v))) := by
  let N : Uniform (fun n (_ : Universe n × (Fin n → ℕ)) => List.range (n+2)) := (((fst.comp universeNumber).pair (constant 2)).comp (Realizer.add.uniform ℕ)).comp
    (Realizer.range.uniform ℕ)
  let A := (((snd.comp snd).pair fst).comp functionGet :
    Uniform (fun n (x : Fin n × (ℕ × (Fin n → ℕ))) => x.2.2 x.1))
  let B := (snd.comp fst : Uniform (fun n (x : Fin n × (ℕ × (Fin n → ℕ))) => x.2.1))
  let P : Uniform (fun n (x : Fin n × (ℕ × (Fin n → ℕ))) =>
      decide (if upper then x.2.2 x.1 ≤ x.2.1 else x.2.1 ≤ x.2.2 x.1)) := by
    cases upper
    · exact (B.pair A).comp (Realizer.le.uniform ℕ)
    · exact (A.pair B).comp (Realizer.le.uniform ℕ)
  let F := ((((snd.comp fst).comp universeSet).pair (fst.pair (snd.comp snd))).comp P.setFilter :
    Uniform (fun n (x : ℕ × (Universe n × (Fin n → ℕ))) => Finset.univ.filter
      (fun v => decide (if upper then x.2.2 v ≤ x.1 else x.1 ≤ x.2.2 v) = true)))
  exact ((N.pair id).comp F.map).congr (fun _ _ => by
    simp only [Function.comp_apply,decide_eq_true_eq])

def matrixGetFrame (frame : Bool) : Uniform (fun n (x : Matrix n × (Fin n × Fin n)) =>
    decide (if frame then matrixRel x.1 x.2.2 x.2.1 else matrixRel x.1 x.2.1 x.2.2)) := by
  cases frame
  · exact matrixGet.congr (fun _ x => by simp [matrixRel])
  · exact ((fst.pair (snd.comp swap)).comp matrixGet).congr (fun _ x => by
      simp [Function.comp_apply,matrixRel])

def conePred (frame : Bool) : Uniform (fun n (x : Universe n × (Matrix n × Finset (Fin n))) =>
    Finset.univ.filter (fun v => ∃ y ∈ x.2.2,
      if frame then matrixRel x.2.1 y v else matrixRel x.2.1 v y)) := by
  let A := (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp (matrixGetFrame frame) :
    Uniform (fun n (x : Fin n × (Matrix n × Fin n)) =>
      decide (if frame then matrixRel x.2.1 x.1 x.2.2 else matrixRel x.2.1 x.2.2 x.1)))
  let P := (((snd.comp snd).pair ((snd.comp fst).pair fst)).comp A.setAny)
  exact (((fst.comp universeSet).pair snd).comp P.setFilter).congr (fun _ _ => by
    simp only [Function.comp_apply,decide_eq_true_eq])

def cone (frame : Bool) (kind : Fin 5) : Uniform (fun n (x : Universe n × (Matrix n × Finset (Fin n))) =>
    coneSet x.2.1 frame kind x.2.2) := by
  let D : Uniform (fun n (x : Universe n × (Matrix n × Finset (Fin n))) =>
      Finset.univ.filter (fun v => ∃ y ∈ x.2.2,
        if frame then matrixRel x.2.1 v y else matrixRel x.2.1 y v)) :=
    (conePred (!frame)).congr (fun _ x => by cases frame <;> rfl)
  match hk : kind.val with
  | 0 => exact (snd.comp snd).congr (fun _ _ => by simp only [Function.comp_apply,coneSet,hk])
  | 1 => exact (conePred frame).congr (fun _ _ => by simp only [coneSet,hk])
  | 2 => exact D.congr (fun _ _ => by simp only [coneSet,hk])
  | 3 =>
    exact (fst.pair ((conePred frame).pair (snd.comp snd)) |>.comp setUnion).congr
      (fun _ _ => by simp only [Function.comp_apply,coneSet,hk])
  | k+4 =>
    exact (fst.pair (D.pair (snd.comp snd)) |>.comp setUnion).congr
      (fun _ _ => by simp only [Function.comp_apply,coneSet,hk])

def cones (frame : Bool) : (ks : List (Fin 5)) →
    Uniform (fun n (x : Universe n × Matrix n) => ks.flatMap (fun k =>
      ((Structure.tripleList (List.finRange n)).map Subtype.val).map (coneSet x.2 frame k)))
  | [] => nil
  | k :: ks =>
    let F := ((((snd.comp fst).pair ((snd.comp snd).pair fst))).comp (cone frame k))
    (((((fst.comp triples).pair id).comp F.map).pair (cones frame ks)).comp append).congr
      (fun _ _ => rfl)

def ranks (frame : Bool) : Uniform (fun n (x : Universe n × Matrix n) =>
    if frame then Structure.reverseJobRank (matrixRel x.2) else Structure.jobRank (matrixRel x.2)) := by
  cases frame
  · exact rank
  · exact (fst.pair rank).comp reverseRank

def thresholds (frame : Bool) : Uniform (fun n (x : Universe n × Matrix n) =>
    [Bool.false,true].flatMap (fun upper => (List.range (n+2)).map
      (fun k => Finset.univ.filter (fun v => if upper then
        (if frame then Structure.reverseJobRank (matrixRel x.2) else Structure.jobRank (matrixRel x.2)) v ≤ k
        else k ≤ (if frame then Structure.reverseJobRank (matrixRel x.2) else Structure.jobRank (matrixRel x.2)) v)))) :=
  ((fst.pair (ranks frame)).comp ((thresholdSets Bool.false).pair (thresholdSets true) |>.comp append)).congr
    (fun _ _ => by simp only [Function.comp_apply,List.flatMap_cons,List.flatMap_nil,List.append_nil])

def atomSets : Uniform (fun n (x : Universe n × Matrix n) =>
    (Atomic.alphabet (List.finRange n)).map
      (Atomic.finsetEval (matrixRel x.2) (Structure.jobRank (matrixRel x.2)) (Structure.reverseJobRank (matrixRel x.2)))) := by
  let C : Uniform (fun n (_ : Universe n × Matrix n) => [∅, (Finset.univ : Finset (Fin n))]) := (((fst.comp setEmpty).pair (((fst.comp universeSet).pair nil).comp cons)).comp cons)
  let T := ((thresholds Bool.false).pair (thresholds true)).comp append
  let D := ((cones Bool.false (List.finRange 5)).pair (cones true (List.finRange 5))).comp append
  exact ((C.pair T).comp append |>.pair D |>.comp append).congr (fun n x => by
    simp only [Function.comp_apply,Atomic.alphabet,List.map_append,List.map_cons,List.map_nil,
      List.map_flatMap,List.map_map,List.flatMap_cons,List.flatMap_nil,List.append_nil,Function.comp_def]
    simp only [atomicCone,atomicThreshold]
    rfl)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.Structure

theorem assignments_map {A B : Type} (g : A → B) (xs : List A) (k : ℕ) :
    assignments (xs.map g) k = (assignments xs k).map (fun f => g ∘ f) := by
  induction k with
  | zero => simp only [assignments,List.map_singleton]; congr 1; funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [assignments,ih,List.flatMap_map,List.map_flatMap,List.map_map]
    apply List.flatMap_congr
    intro a ha
    apply List.map_congr_left
    intro f hf
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem Formula.map_evalFinset {J A B : Type} [Fintype J] [DecidableEq J]
    (g : A → B) (atoms : B → Finset J) (p : Formula A) :
    (p.map g).evalFinset atoms = p.evalFinset (atoms ∘ g) := by
  induction p with
  | leaf a b => rfl
  | conj p q ihp ihq | disj p q ihp ihq => simp only [map,evalFinset,ihp,ihq]

theorem Atomic.filter_eval {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (rank reverseRank : J → ℕ) (a : Atomic J) :
    Finset.univ.filter (eval r rank reverseRank a) = finsetEval r rank reverseRank a := by
  apply Finset.coe_injective
  rw [coe_finsetEval]
  ext x
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))

theorem effectiveFamily_eq_finset {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (rank reverseRank : J → ℕ) (jobs : List J) (K : ℕ) :
    effectiveFamily r rank reverseRank jobs K =
      (assignments ((Atomic.alphabet jobs).map (Atomic.finsetEval r rank reverseRank)) K).flatMap
        (fun f => (Formula.templates K).map (Formula.evalFinset f)) := by
  simp only [effectiveFamily,Atomic.filter_eval,assignments_map,List.flatMap_map]
  apply List.flatMap_congr
  intro f hf
  apply List.map_congr_left
  intro s hs
  exact Formula.map_evalFinset f _ s

end ThreeMachine.Structure

namespace ThreeMachine.StackCompiler
open ThreeMachine.Structure ThreeMachine.Algorithm
namespace Uniform

def evalTemplate {K : ℕ} : (p : Formula (Fin K)) →
    Uniform (fun n (x : Universe n × (Fin K → Finset (Fin n))) => p.evalFinset x.2)
  | .leaf a b =>
    let A := (snd.pair (constant a)).comp (functionGetAny (fun _ : ℕ => K))
    if hb : b then
      ((fst.pair A).comp setCompl).congr (fun _ _ => by simp [Formula.evalFinset,hb,Function.comp_apply])
    else A.congr (fun _ _ => by simp [Formula.evalFinset,hb,Function.comp_apply])
  | .conj p q => ((evalTemplate p).pair (evalTemplate q)).comp setInter
  | .disj p q => (fst.pair ((evalTemplate p).pair (evalTemplate q))).comp setUnion

def evalTemplates {K : ℕ} : (ps : List (Formula (Fin K))) →
    Uniform (fun n (x : Universe n × (Fin K → Finset (Fin n))) => ps.map (Formula.evalFinset x.2))
  | [] => nil
  | p :: ps => ((evalTemplate p).pair (evalTemplates ps)).comp cons

def family (K : ℕ) : Uniform (fun n (x : Universe n × Matrix n) =>
    effectiveFamily (matrixRel x.2) (Structure.jobRank (matrixRel x.2))
      (Structure.reverseJobRank (matrixRel x.2)) (List.finRange n) K) :=
  ((((atomSets.comp (assignments K)).pair fst).comp (swap.comp (evalTemplates (Formula.templates K))).flatMap)).congr
    (fun _ _ => (effectiveFamily_eq_finset _ _ _ _ _).symm)

def fullSolveK (K : ℕ) : Uniform (fun n (x : Universe n × Matrix n) =>
    Algorithm.lookup (Algorithm.layers (matrixRel x.2)
      (effectiveFamily (matrixRel x.2) (Structure.jobRank (matrixRel x.2))
        (Structure.reverseJobRank (matrixRel x.2)) (List.finRange n) K)
      ((Structure.tripleList (List.finRange n)).map Subtype.val) n) Finset.univ) := by
  let A : Uniform (fun n (x : Universe n × Matrix n) =>
      Algorithm.layers (matrixRel x.2) (effectiveFamily (matrixRel x.2) (Structure.jobRank (matrixRel x.2))
        (Structure.reverseJobRank (matrixRel x.2)) (List.finRange n) K)
        ((Structure.tripleList (List.finRange n)).map Subtype.val) n) :=
    (((fst.comp universeNumber).pair (fst.pair (snd.pair ((family K).pair (fst.comp triples))))).comp layers)
  exact ((A.pair (fst.comp universeSet)).comp (lookupA setEq)).congr (fun _ _ => rfl)

def fullSolve : Uniform (fun n (x : Universe n × Matrix n) => Algorithm.fullSolve (matrixRel x.2)) :=
  fullSolveK 10000

end Uniform
end ThreeMachine.StackCompiler

end

end OAI
end


section
-- module ScheduleRoutines
namespace OAI

universe u1 u2 u3 u4

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

instance {n : ℕ} (G : Instance n) : DecidableRel G.edge := fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ G.edges))

instance (n : ℕ) : Coding (Instance n) := ⟨fun G => enc G.edges⟩

@[simp] theorem enc_instance {n : ℕ} (G : Instance n) : enc G = enc G.edges := rfl

theorem enc_map_eq {α : Type u1} {β : Type u2} [Coding α] [Coding β] (f : α → β)
    (h : ∀ a, enc (f a) = enc a) (xs : List α) : enc (xs.map f) = enc xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,enc_cons,h,ih]

namespace Uniform

variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

def matrixMapAny (d : I → ℕ) {p : ∀ i, (Fin (d i) × Fin (d i)) × α i → Bool}
    (P : Uniform p) : Uniform (fun i (x : Universe (d i) × α i) =>
      (fun a b => p i ((a,b),x.2) : Matrix (d i))) := by
  let A : Uniform (fun i (x : Fin (d i) × (Fin (d i) × α i)) => p i ((x.2.1,x.1),x.2.2)) :=
    (((snd.comp fst).pair fst).pair (snd.comp snd)).comp P
  let B : Uniform (fun i (x : Fin (d i) × (Universe (d i) × α i)) =>
      fun b => p i ((x.1,b),x.2.2)) :=
    (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp (A.vectorMapAny d))
  exact ((fst.pair id).comp (B.vectorMapAny d)).congr (fun _ _ => rfl)

def instanceEdges : Uniform (fun n (G : Instance n) => G.edges) :=
  reinterpret _ (fun _ _ => rfl)

def edgePairEq : Uniform (fun n (x : (Fin n × Fin n) × (Fin n × Fin n)) => decide (x.1 = x.2)) :=
  (((fst.comp fst).pair (snd.comp fst)).comp finEq).andD
    (((fst.comp snd).pair (snd.comp snd)).comp finEq) |>.congr (fun _ x => by
      apply decide_eq_decide.mpr
      change (x.1.1 = x.2.1 ∧ x.1.2 = x.2.2) ↔ x.1 = x.2
      exact Prod.ext_iff.symm)

def edgeAt : Uniform (fun n (x : (Fin n × Fin n) × Instance n) => decide (x.2.edge x.1.1 x.1.2)) :=
  ((((snd.comp instanceEdges).pair fst).comp edgePairEq.any)).congr (fun _ x => by
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simp only [List.any_eq_true,decide_eq_true_eq]
    change (∃ y ∈ x.2.edges, y = x.1) ↔ x.1 ∈ x.2.edges
    exact exists_eq_right)

def edgeMatrix : Uniform (fun n (x : Universe n × Instance n) =>
    (fun a b => decide (x.2.edge a b) : Matrix n)) := matrixMapAny (fun n : ℕ => n) edgeAt

def matrixRows : Uniform (fun n (M : Matrix n) => (List.ofFn M).map List.ofFn) :=
  reinterpret _ (fun _ M => by
    rw [enc_map_eq List.ofFn (fun _ => rfl)]
    rfl)

def readMatrix {n : ℕ} (M : Matrix n) (a b : ℕ) : Bool :=
  (((List.ofFn M).map List.ofFn).getD a []).getD b Bool.false

def matrixReadNat : Uniform (fun n (x : Matrix n × (ℕ × ℕ)) => readMatrix x.1 x.2.1 x.2.2) := by
  let A := ((((fst.comp matrixRows).pair (snd.comp fst)).pair nil).comp getElemD :
    Uniform (fun n (x : Matrix n × (ℕ × ℕ)) => ((List.ofFn x.1).map List.ofFn).getD x.2.1 []))
  exact (((A.pair (snd.comp snd)).pair false).comp getElemD)

theorem readMatrix_eq {n : ℕ} (M : Matrix n) (a b : ℕ) :
    readMatrix M a b = if ha : a < n then if hb : b < n then M ⟨a,ha⟩ ⟨b,hb⟩ else Bool.false else Bool.false := by
  simp only [readMatrix,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_ofFn]
  split_ifs <;> simp_all

def paddedMatrix : Uniform (fun (i : ℕ × ℕ) (x : Universe i.2 × Matrix i.1) =>
    (fun a b => decide (paddedOrder (matrixRel x.2) i.2 a b) : Matrix i.2)) := by
  let P : Uniform (fun (i : ℕ × ℕ) (x : (Fin i.2 × Fin i.2) × Matrix i.1) =>
      readMatrix x.2 x.1.1.val x.1.2.val) :=
    (snd.pair (((fst.comp fst).comp (finValue Prod.snd)).pair
      ((fst.comp snd).comp (finValue Prod.snd)))).comp (matrixReadNat.reindex Prod.fst)
  exact (matrixMapAny Prod.snd P).congr (fun i x => by
    funext a b
    rw [readMatrix_eq]
    by_cases ha : a.val < i.1 <;> by_cases hb : b.val < i.1
    · simp only [dite_eq_left ha,dite_eq_left hb]
      apply Bool.eq_iff_iff.mpr
      change (x.2 ⟨a.val,ha⟩ ⟨b.val,hb⟩ = true) ↔
        (decide (paddedOrder (matrixRel x.2) i.2 a b) = true)
      rw [decide_eq_true_eq]
      change (matrixRel x.2 ⟨a.val,ha⟩ ⟨b.val,hb⟩) ↔ paddedOrder (matrixRel x.2) i.2 a b
      constructor
      · intro h; exact ⟨⟨a.val,ha⟩,⟨b.val,hb⟩,rfl,rfl,h⟩
      · rintro ⟨u,v,hu,hv,h⟩
        have eu : u = ⟨a.val,ha⟩ := Fin.ext hu.symm
        have ev : v = ⟨b.val,hb⟩ := Fin.ext hv.symm
        simpa only [eu,ev] using h
    · simp only [dite_eq_left ha,dite_eq_right hb]
      have h : ¬paddedOrder (matrixRel x.2) i.2 a b := by
        rintro ⟨u,v,hu,hv,hr⟩; exact hb (hv.symm ▸ v.isLt)
      simp only [h,decide_false]
    · simp only [dite_eq_right ha]
      have h : ¬paddedOrder (matrixRel x.2) i.2 a b := by
        rintro ⟨u,v,hu,hv,hr⟩; exact ha (hu.symm ▸ u.isLt)
      simp only [h,decide_false]
    · simp only [dite_eq_right ha]
      have h : ¬paddedOrder (matrixRel x.2) i.2 a b := by
        rintro ⟨u,v,hu,hv,hr⟩; exact ha (hu.symm ▸ u.isLt)
      simp only [h,decide_false])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

def nextMatrix {n : ℕ} (E M : Matrix n) : Matrix n :=
  fun a b => M a b || (List.finRange n).any (fun z => M a z && E z b)

def closureMatrix {n : ℕ} (G : Instance n) (k : ℕ) : Matrix n :=
  fun a b => decide ((a,b) ∈ Algorithm.closureTable G k)

theorem closureMatrix_zero {n : ℕ} (G : Instance n) :
    closureMatrix G 0 = fun a b => decide (G.edge a b) := by
  funext a b
  simp only [closureMatrix,Algorithm.closureTable_zero,List.mem_toFinset,Instance.edge]
  rfl

theorem nextMatrix_closure {n : ℕ} (G : Instance n) (k : ℕ) :
    nextMatrix (closureMatrix G 0) (closureMatrix G k) = closureMatrix G (k+1) := by
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp only [nextMatrix,closureMatrix,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true,
    decide_eq_true_eq,List.mem_finRange]
  simp only [Algorithm.closureTable_succ,Algorithm.closureTable_zero,
    Algorithm.closureStep,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]

namespace Uniform

def nextMatrixCell : Uniform (fun n (x : (Fin n × Fin n) × (Universe n × (Matrix n × Matrix n))) =>
    ThreeMachine.StackCompiler.nextMatrix x.2.2.1 x.2.2.2 x.1.1 x.1.2) := by
  let P : Uniform (fun n (x : Fin n × ((Fin n × Fin n) × (Matrix n × Matrix n))) =>
      x.2.2.2 x.2.1.1 x.1 && x.2.2.1 x.1 x.2.1.2) :=
    (((((snd.comp (snd.comp snd)).pair (((snd.comp (fst.comp fst)).pair fst))).comp matrixGet).pair
      (((snd.comp (snd.comp fst)).pair (fst.pair (snd.comp (fst.comp snd)))).comp matrixGet)).comp
      (Realizer.and.uniform ℕ))
  let A := (((snd.comp (snd.comp snd)).pair fst).comp matrixGet :
    Uniform (fun n (x : (Fin n × Fin n) × (Universe n × (Matrix n × Matrix n))) =>
      x.2.2.2 x.1.1 x.1.2))
  let B := ((((snd.comp fst).comp universeList).pair (fst.pair (snd.comp snd))).comp P.any)
  exact ((A.pair B).comp (Realizer.or.uniform ℕ)).congr (fun _ _ => rfl)

def nextMatrix : Uniform (fun n (x : Universe n × (Matrix n × Matrix n)) =>
    ThreeMachine.StackCompiler.nextMatrix x.2.1 x.2.2) :=
  (fst.pair id).comp (matrixMapAny (fun n => n) nextMatrixCell)

def closureMatrixStep : Uniform (fun n (x : (Universe n × Matrix n) × Matrix n) =>
    (x.1,ThreeMachine.StackCompiler.nextMatrix x.1.2 x.2)) :=
  fst.pair ((((fst.comp fst).pair ((fst.comp snd).pair snd))).comp nextMatrix)

def reachMatrix : Uniform (fun n (x : Universe n × Instance n) => closureMatrix x.2 n) := by
  let A := fst.pair edgeMatrix
  let B := ((fst.comp universeNumber).pair (A.pair edgeMatrix)).comp closureMatrixStep.iterate |>.comp snd
  exact B.congr (fun n x => by
    dsimp only [Function.comp_apply]
    have h : ∀ k, (fun p : (Universe n × Matrix n) × Matrix n =>
        (p.1,ThreeMachine.StackCompiler.nextMatrix p.1.2 p.2))^[k]
        ((x.1,fun a b => decide (x.2.edge a b)),fun a b => decide (x.2.edge a b)) =
        ((x.1,fun a b => decide (x.2.edge a b)),closureMatrix x.2 k) := by
      intro k
      induction k with
      | zero => rw [Function.iterate_zero_apply,closureMatrix_zero]
      | succ k ih =>
        rw [Function.iterate_succ_apply',ih]
        simp only [← closureMatrix_zero,nextMatrix_closure]
    rw [h])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Realizer

def triple : Realizer (fun n : ℕ => 3*n) :=
  (((id.pair id).comp add).pair id |>.comp add).congr (fun n => by
    simp only [Function.comp_apply,id_eq]
    omega)

end Realizer

def scheduleMatrix {n : ℕ} (M : Matrix n) (T : ℕ) : Option (Fin n → ℕ) :=
  if hn : n ≤ 3*T then
    (Algorithm.fullSolve (paddedOrder (matrixRel M) (3*T))).map
      (fun s x => s.time (Fin.castLE hn x))
  else none

theorem scheduleMatrix_closure {n : ℕ} (G : Instance n) (T : ℕ) :
    scheduleMatrix (closureMatrix G n) T = Algorithm.scheduleAt G T := by
  have h : matrixRel (closureMatrix G n) = Algorithm.reachable G := by
    funext a b
    simp only [matrixRel,closureMatrix,decide_eq_true_eq,Algorithm.reachable]
  simp only [scheduleMatrix,Algorithm.scheduleAt,h]

namespace Uniform

def restrictTime : Uniform (fun (i : ℕ × ℕ) (x : Universe i.1 × (Fin i.2 → ℕ)) =>
    (fun v : Fin i.1 => (List.ofFn x.2).getD v.val 0)) := by
  let A : Uniform (fun (i : ℕ × ℕ) (x : Fin i.1 × (Fin i.2 → ℕ)) =>
      (List.ofFn x.2).getD x.1.val 0) :=
    ((((snd.comp (functionListAny Prod.snd)).pair (fst.comp (finValue Prod.fst))).pair zero).comp getElemD)
  exact A.vectorMapAny Prod.fst

def paddedSolve : Uniform (fun (i : ℕ × ℕ) (x : Cardinal i.2 × Matrix i.1) =>
    Algorithm.fullSolve (paddedOrder (matrixRel x.2) (3*i.2))) := by
  let U : Uniform (fun (i : ℕ × ℕ) (_ : Cardinal i.2 × Matrix i.1) =>
      (Universe.mk () : Universe (3*i.2))) := (fst.comp (cardinalMap Prod.snd Realizer.triple)).comp
    (makeUniverseAny (fun i : ℕ × ℕ => 3*i.2))
  let A := (U.pair snd).comp (paddedMatrix.reindex (fun i : ℕ × ℕ => (i.1,3*i.2)))
  exact ((U.pair A).comp (fullSolve.reindex (fun i : ℕ × ℕ => 3*i.2))).congr (fun i x => by
    have h : matrixRel (fun a b : Fin (3*i.2) => decide (paddedOrder (matrixRel x.2) (3*i.2) a b)) =
        paddedOrder (matrixRel x.2) (3*i.2) := by
      funext a b
      exact propext (by simp only [matrixRel,decide_eq_true_eq])
    simp only [Function.comp_apply,h])

def scheduleMatrixFixed : Uniform (fun (i : ℕ × ℕ)
    (x : Universe i.1 × (Cardinal i.2 × Matrix i.1)) =>
      ThreeMachine.StackCompiler.scheduleMatrix x.2.2 i.2) := by
  let P : Uniform (fun (i : ℕ × ℕ) (_ : Universe i.1 × (Cardinal i.2 × Matrix i.1)) =>
      decide (i.1 ≤ 3*i.2)) :=
    (((fst.comp (universeNumber.reindex Prod.fst)).pair
      ((snd.comp fst).comp (cardinalValue Prod.snd) |>.comp (Realizer.triple.uniform (ℕ × ℕ)))).comp
      (Realizer.le.uniform (ℕ × ℕ)))
  let R : Uniform (fun (i : ℕ × ℕ) (x : Algorithm.Block (Fin (3*i.2)) × Universe i.1) =>
      (fun v : Fin i.1 => (List.ofFn x.1.time).getD v.val 0)) :=
    (snd.pair (fst.comp (blockTime.reindex (fun i : ℕ × ℕ => 3*i.2)))).comp
      (restrictTime.reindex (fun i : ℕ × ℕ => (i.1,3*i.2)))
  let A := (((snd.comp paddedSolve).pair fst).comp R.optionMap)
  exact ((P.pair id).comp (A.choose none)).congr (fun i x => by
    simp only [Function.comp_apply,ThreeMachine.StackCompiler.scheduleMatrix]
    by_cases h : i.1 ≤ 3*i.2
    · simp only [decide_eq_true_eq,ite_eq_left h,dite_eq_left h]
      apply congrArg (fun f => Option.map f _)
      funext b
      funext v
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left (lt_of_lt_of_le v.isLt h),
        Option.getD_some]
      rfl
    · simp only [decide_eq_true_eq,ite_eq_right h,dite_eq_right h])

def scheduleMatrix : Uniform (fun n (x : Universe n × (ℕ × Matrix n)) =>
    ThreeMachine.StackCompiler.scheduleMatrix x.2.2 x.2.1) :=
  scheduleMatrixFixed.recode _ (fun n x =>
    ⟨(n,x.2.1),(x.1,(Cardinal.mk (),x.2.2)),rfl,rfl⟩)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

def bestMatrix {n : ℕ} (M : Matrix n) : ℕ → Option (ℕ × (Fin n → ℕ))
  | 0 => none
  | k+1 => match bestMatrix M k with
    | some a => some a
    | none => (scheduleMatrix M (k+1)).map (fun t => (k+1,t))

theorem bestMatrix_closure {n : ℕ} (G : Instance n) (k : ℕ) :
    bestMatrix (closureMatrix G n) k = Algorithm.best G k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [bestMatrix,Algorithm.best,ih,scheduleMatrix_closure]
      try cases Algorithm.best G k <;> rfl

def bestMatrixStep {n : ℕ}
    (x : (Universe n × Matrix n) × (ℕ × Option (ℕ × (Fin n → ℕ)))) :=
  (x.1,(x.2.1+1,match x.2.2 with
    | some a => some a
    | none => (scheduleMatrix x.1.2 (x.2.1+1)).map (fun t => (x.2.1+1,t))))

theorem bestMatrix_iterate {n : ℕ} (U : Universe n) (M : Matrix n) (k : ℕ) :
    bestMatrixStep^[k] ((U,M),(0,none)) = ((U,M),(k,bestMatrix M k)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

def answerMatrix {n : ℕ} (M : Matrix n) : Option ℕ → Option (List ℕ)
  | some T => (scheduleMatrix M T).map List.ofFn
  | none => (bestMatrix M n).map (fun a => List.ofFn a.2)

theorem answerMatrix_closure {n : ℕ} (G : Instance n) (d : Option ℕ) :
    encodeAnswer (answerMatrix (closureMatrix G n) d) = Algorithm.output G d := by
  cases d <;> simp only [answerMatrix,Algorithm.output,scheduleMatrix_closure,bestMatrix_closure,slots]
  all_goals rfl

namespace Uniform

def bestMatrixStep : Uniform (fun n => @ThreeMachine.StackCompiler.bestMatrixStep n) := by
  let K := ((snd.comp fst).comp (Realizer.succ.uniform ℕ) :
    Uniform (fun n (x : (Universe n × Matrix n) × (ℕ × Option (ℕ × (Fin n → ℕ)))) => x.2.1+1))
  let A := ((((fst.comp fst).pair (K.pair (fst.comp snd))).comp scheduleMatrix).pair K).comp
    swap.optionMap
  let R := ((((snd.comp snd).comp optionIsSome).pair id).comp ((snd.comp snd).choose A))
  exact (fst.pair (K.pair R)).congr (fun n x => by
    simp only [Function.comp_apply,ThreeMachine.StackCompiler.bestMatrixStep]
    cases x.2.2 <;> rfl)

def bestMatrix : Uniform (fun n (x : Universe n × Matrix n) =>
    ThreeMachine.StackCompiler.bestMatrix x.2 n) :=
  ((((fst.comp universeNumber).pair (id.pair (zero.pair none))).comp bestMatrixStep.iterate).comp
    (snd.comp snd)).congr (fun n x => by
      rcases x with ⟨U,M⟩
      simp only [Function.comp_apply,bestMatrix_iterate])

def answerMatrix : Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) =>
    ThreeMachine.StackCompiler.answerMatrix x.2.1 x.2.2) := by
  let T := ((((snd.comp snd).pair zero).comp getD) :
    Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) => x.2.2.getD 0))
  let A : Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) =>
      (ThreeMachine.StackCompiler.scheduleMatrix x.2.1 (x.2.2.getD 0)).map List.ofFn) :=
    ((fst.pair (T.pair (snd.comp fst))).comp scheduleMatrix).comp functionList.mapOption
  let B : Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) =>
      (ThreeMachine.StackCompiler.bestMatrix x.2.1 n).map (fun a => List.ofFn a.2)) :=
    ((fst.pair (snd.comp fst)).comp bestMatrix).comp (snd.comp functionList).mapOption
  exact ((((snd.comp snd).comp optionIsSome).pair id).comp (A.choose B)).congr (fun n x => by
    dsimp only [Function.comp_apply]
    cases x.2.2 <;> rfl)

def unaryAnswer : Uniform (fun n (x : Universe n × (Instance n × Option ℕ)) =>
    ThreeMachine.StackCompiler.answerMatrix (closureMatrix x.2.1 n) x.2.2) :=
  (fst.pair ((((fst.pair (snd.comp fst)).comp reachMatrix).pair (snd.comp snd)))).comp answerMatrix

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.Algorithm
open Structure

namespace Block

def Bounded {J : Type} (s : Block J) : Prop := ∀ x, s.time x ≤ s.length

end Block

namespace State
variable {J : Type} [DecidableEq J]

end State

section Bounded
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

def TableBounded (tab : List (Finset J × Block J)) : Prop :=
  ∀ W s, (W,s) ∈ tab → s.Bounded

def MarksBounded (marks : List (State J × Block J)) : Prop :=
  ∀ u s, (u,s) ∈ marks → s.Bounded

end Bounded

end ThreeMachine.Algorithm

end

end OAI
end


section
-- module CostBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38 u39 u40

section

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_unit : volume () = 1 := rfl
@[simp] theorem volume_bool_false : volume Bool.false = 1 := rfl
@[simp] theorem volume_bool_true : volume Bool.true = 3 := rfl
@[simp] theorem volume_none {α : Type u1} [Coding α] : volume (none : Option α) = 1 := rfl
@[simp] theorem volume_some {α : Type u2} [Coding α] (a : α) : volume (some a) = volume a+2 := by
  simp only [volume,enc_some,Data.size_pair,Data.size_nil]

theorem volume_bool (b : Bool) : volume b ≤ 3 := by cases b <;> decide

theorem volume_mem_le {α : Type u4} [Coding α] {xs : List α} {a : α}
    (ha : a ∈ xs) : volume a ≤ volume xs := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [volume_cons]; omega
    · have := ih ha; simp only [volume_cons]; omega

theorem volume_option_le {α : Type u7} [Coding α] (o : Option α) (V : ℕ)
    (hV : ∀ a ∈ o, volume a ≤ V) : volume o ≤ V+2 := by
  cases o with
  | none => simp only [volume_none]; omega
  | some a => simpa only [volume_some,Nat.add_le_add_iff_right] using hV a rfl

theorem volume_optionToList {α : Type u8} [Coding α] (o : Option α) :
    volume o.toList = volume o := by cases o <;> rfl

theorem volume_finset_le {n : ℕ} (s : Finset (Fin n)) : volume s ≤ 3*(n+1)^2 := by
  change volume (s.sort (· ≤ ·)) ≤ _
  have h := volume_list_le (s.sort (· ≤ ·)) (2*n+1) (fun a _ => by
    rw [volume_fin]; have := a.isLt; omega)
  have hh := Finset.card_le_univ s
  rw [Finset.length_sort] at h
  simp only [Fintype.card_fin] at hh
  nlinarith

namespace Realizer
variable {α : Type u10} {β : Type u11} [Coding α] [Coding β] {f : α × β → β}

theorem foldTime_le (R : Realizer f) (xs : List α) (P : β → Prop) (T V : ℕ)
    (hvol : ∀ b, P b → volume b ≤ V)
    (hstep : ∀ a ∈ xs, ∀ b, P b → P (f (a,b)))
    (htime : ∀ a ∈ xs, ∀ b, P b → R.time (a,b) ≤ T)
    (b : β) (hb : P b) :
    foldTime R b xs ≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
  induction xs generalizing b with
  | nil => simp only [foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have ha : a ∈ a :: xs := by simp
    have hs := hstep a ha b hb
    have hi := ih (fun a ha => hstep a (by simp [ha]))
      (fun a ha => htime a (by simp [ha])) (f (a,b)) hs
    have ht := htime a ha b hb
    have hv := hvol b hb
    have hw := hvol _ hs
    simp only [foldTime,volume_cons,List.length_cons] at hi ⊢
    nlinarith [volume_pos a,volume_pos xs]

end Realizer

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
variable {f : ∀ i, α i × β i → β i}

theorem time_fold_le (R : Uniform f) (i : I) (xs : List (α i))
    (P : β i → Prop) (T V : ℕ) (hvol : ∀ b, P b → volume b ≤ V)
    (hstep : ∀ a ∈ xs, ∀ b, P b → P (f i (a,b)))
    (htime : ∀ a ∈ xs, ∀ b, P b → R.time i (a,b) ≤ T)
    (b : β i) (hb : P b) :
    R.fold.time i (xs,b) ≤ 50*(xs.length+1)*(T+volume xs+V+1) := by
  have h := Realizer.foldTime_le (R.specialize i) xs P T V hvol hstep htime b hb
  rw [time_fold]
  simp only [volume_pair]
  have hv := hvol b hb
  nlinarith [volume_pos xs]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer

theorem time_not_le (b : Bool) : not.time b ≤ 10000 := by cases b <;> decide

theorem time_and_le (x : Bool × Bool) : and.time x ≤ 10000 := by
  rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem time_or_le (x : Bool × Bool) : or.time x ≤ 10000 := by
  rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem time_succ_le (n : ℕ) : succ.time n ≤ 200*(n+1) := by
  have hu : (unit : Realizer (fun (_ : ℕ) => ())).time n = 2 := rfl
  simp only [succ,time_congr,time_comp,time_pair,time_id,hu,id_eq]
  simp only [volume_pair,volume_unit,volume_nat]
  change 2+(2*n+1+2)+20*((2*n+1)+1+(2*n+1)+1)+(volume ((),n)+2)+10*(1+(2*n+1)+1+1) ≤ _
  simp only [volume_pair,volume_unit,volume_nat]
  omega

theorem time_test_le {α : Type u15} [Coding α] (p : α → Bool)
    (h : ∀ x, (enc x).nonempty = p x) (x : α) :
    (test p h).time x ≤ 10000*(volume x+1) := by
  simp only [time,test,Routine.comp,Routine.pair,Routine.identity,Routine.nil,
    Routine.choose,Routine.constant,Data.size_pair,Data.size_nil]
  change (enc x).size+2+2+20*((enc x).size+(enc x).size+1+1)+
    (7*(20*((enc x).size+1+1)+50*3+50)+2+30*((enc x).size+1+1+3+1+1))+
    10*((enc x).size+1+1+1) ≤ _
  change _ ≤ 10000*((enc x).size+1)
  omega

end Realizer

namespace Uniform
variable {I : Type u16} {α : I → Type u17} {β : I → Type u18}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)]

@[simp] theorem time_uniform {δ : Type u19} {ε : Type u20} [Coding δ] [Coding ε]
    {f : δ → ε} (R : Realizer f) (i : I) (x : δ) : (R.uniform I).time i x = R.time x := rfl

theorem time_head?_le (i : I) (xs : List (α i)) : head?.time i xs ≤ 10000*(volume xs+1) := by
  cases xs with
  | nil =>
    simp only [time,head?,Routine.comp,Routine.pair,Routine.identity,Routine.nil,
      Routine.choose,Routine.select,enc_nil,id_eq,Function.comp_apply,
      ite_true,Data.head,Data.size_pair,Data.size_nil,volume,enc_nil]
    omega
  | cons a xs =>
    dsimp only [time,head?,Routine.comp,Routine.pair,Routine.identity,Routine.nil,
      Routine.choose,Routine.select,Function.comp_apply,enc_cons,Data.head,Data.tail,
      Data.size_pair,Data.size_nil,Data.nonempty,id_eq,ite_true]
    simp only [ite_true,Data.size_pair,Data.size_nil,volume,enc_cons,Data.size_pair]
    omega

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

def Majorized {I : Type u21} (f g : I → ℕ) : Prop := ∃ C : ℕ, ∀ i, f i ≤ C*g i

namespace Majorized
variable {I : Type u22} {J : Type u23} {f g h s t : I → ℕ}

theorem refl (f : I → ℕ) : Majorized f f := ⟨1,fun _ => by omega⟩
theorem of_le (h : ∀ i, f i ≤ g i) : Majorized f g := ⟨1,fun i => by simpa using h i⟩
theorem trans (hf : Majorized f g) (hg : Majorized g h) : Majorized f h := by
  obtain ⟨C,hC⟩ := hf; obtain ⟨D,hD⟩ := hg
  exact ⟨C*D,fun i => (hC i).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (hD i))⟩

theorem precomp (hf : Majorized f g) (a : J → I) : Majorized (f ∘ a) (g ∘ a) := by
  obtain ⟨C,hC⟩ := hf; exact ⟨C,fun i => hC (a i)⟩
theorem add (hf : Majorized f s) (hg : Majorized g s) : Majorized (fun i => f i+g i) s := by
  obtain ⟨C,hC⟩ := hf; obtain ⟨D,hD⟩ := hg
  refine ⟨C+D,fun i => ?_⟩
  simpa only [Nat.add_mul] using Nat.add_le_add (hC i) (hD i)
theorem mul (hf : Majorized f s) (hg : Majorized g t) :
    Majorized (fun i => f i*g i) (fun i => s i*t i) := by
  obtain ⟨C,hC⟩ := hf; obtain ⟨D,hD⟩ := hg
  refine ⟨C*D,fun i => ?_⟩
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul (hC i) (hD i)
theorem const (C : ℕ) (hs : ∀ i, 1 ≤ s i) : Majorized (fun _ => C) s := by
  exact ⟨C,fun i => by simpa using Nat.mul_le_mul_left C (hs i)⟩

theorem pow (hf : Majorized f s) (d : ℕ) : Majorized (fun i => (f i)^d) (fun i => (s i)^d) := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨C^d,fun i => ?_⟩
  simpa only [Nat.mul_pow] using Nat.pow_le_pow_left (hC i) d

theorem pow_mono (hs : ∀ i, 1 ≤ s i) {d e : ℕ} (hde : d ≤ e) :
    Majorized (fun i => (s i)^d) (fun i => (s i)^e) :=
  of_le (fun i => Nat.pow_le_pow_right (hs i) hde)

end Majorized
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_flatten {α : Type u24} [Coding α] (xs : List (List α)) :
    volume xs = volume xs.flatten+2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have h := volume_append a xs.flatten
    simp only [volume_cons,List.flatten_cons,List.length_cons] at ih ⊢
    omega

namespace Uniform
variable {I : Type u25} {α : I → Type u26} {β : I → Type u27} {γ : I → Type u28}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

@[simp] theorem time_tail (i : I) (xs : List (α i)) : tail.time i xs = volume xs+2 := rfl
@[simp] theorem time_none (i : I) (x : α i) : (none : Uniform (fun i (_ : α i) => (Option.none : Option (β i)))).time i x = 2 := rfl

theorem time_ite_le {p : ∀ i, α i → Bool} {f g : ∀ i, α i → β i}
    (P : Uniform p) (R : Uniform f) (S : Uniform g) (i : I) (x : α i) :
    (P.ite R S).time i x ≤ P.time i x+R.time i x+S.time i x+
      1000*(volume x+volume (f i x)+volume (g i x)+1) := by
  have hp := volume_bool (p i x)
  simp only [ite,time_congr,time_comp,time_pair,time_id,time_choose,time_snd,volume_pair]
  omega

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u29} {α : I → Type u30} {β : I → Type u31} {γ : I → Type u32}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_optionMap {f : ∀ i, α i × γ i → β i} (R : Uniform f)
    (i : I) (o : Option (α i)) (e : γ i) (T V : ℕ)
    (hT : ∀ a ∈ o, R.time i (a,e) ≤ T) (hV : ∀ a ∈ o, volume (f i (a,e)) ≤ V) :
    R.optionMap.time i (o,e) ≤ 1000000*(T+volume o+volume e+V+1) := by
  have hl : o.toList.length ≤ 1 := by cases o <;> simp
  have hv : volume (o.toList.map (fun a => f i (a,e))) ≤ V+3 := by
    cases o with
    | none => simp only [Option.toList_none,List.map_nil,volume_nil]; omega
    | some a =>
      have hv := hV a rfl
      simp only [Option.toList_some,List.map_cons,List.map_nil,volume_cons,volume_nil]
      omega
  have hm := time_map R i o.toList e T (fun a ha => hT a (by simpa using ha))
  have hh := time_head?_le i (o.toList.map (fun a => f i (a,e)))
  simp only [optionMap,time_congr,time_comp,onFst,time_pair,optionToList,time_reinterpret,
    time_fst,time_snd,Function.comp_apply,volume_pair,volume_optionToList] at hm ⊢
  nlinarith [volume_pos o,volume_pos e]

theorem time_getD_le (i : I) (o : Option (α i)) (a : α i) :
    getD.time i (o,a) ≤ 10000*(volume o+volume a+1) := by
  cases o with
  | none =>
    simp only [getD,time_congr,time_comp,time_pair,time_fst,time_snd,optionToList,time_reinterpret,
      time_fold,Function.comp_apply,Realizer.foldTime,Option.toList_none,volume_pair,volume_none,volume_nil]
    omega
  | some b =>
    simp only [getD,time_congr,time_comp,time_pair,time_fst,time_snd,optionToList,time_reinterpret,
      time_fold,Function.comp_apply,Realizer.foldTime,Option.toList_some,volume_pair,volume_some,volume_cons,volume_nil]
    simp only [Realizer.time,Uniform.specialize,Uniform.fst,Routine.select,volume,enc_pair,Data.size_pair]
    omega

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u33} {α : I → Type u34} {β : I → Type u35} {γ : I → Type u36}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_anyBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (a : α i) (e : γ i) (b : Bool) :
    (anyBody P).time i (a,(e,b)) ≤ P.time i (a,e)+100000*(volume a+volume e+1) := by
  have hp := volume_bool (p i (a,e))
  have hb := volume_bool b
  have ho := volume_bool (b || p i (a,e))
  have ht := Realizer.time_or_le (b,p i (a,e))
  simp only [anyBody,time_pair,time_comp,time_fst,time_snd,time_uniform,volume_pair,Function.comp_apply]
  omega

theorem time_any {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.any.time i (xs,e) ≤ 10000000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := time_fold_le (anyBody P) i xs (fun b => b.1 = e)
    (T+100000*(volume xs+volume e+1)) (volume e+4)
    (by rintro ⟨e',b⟩ hb; dsimp only at hb; subst e'; rw [volume_pair]; have := volume_bool b; omega)
    (by intro a ha b hb; exact hb)
    (by intro a ha b hb
        have h := time_anyBody P i a e b.2
        have ht := hT a ha
        have hv := volume_mem_le ha
        subst e
        exact h.trans (by omega)) (e,Bool.false) rfl
  have hv := volume_bool (xs.any (fun a => p i (a,e)))
  simp only [any,time_congr,time_comp,time_pair,time_fst,time_snd,time_false,
    Function.comp_apply,any_fold_eq,Bool.false_or,volume_pair,volume_bool_false]
  nlinarith [volume_pos xs,volume_pos e]

theorem time_all {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.all.time i (xs,e) ≤ 1000000000000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := time_any (P.comp (Realizer.not.uniform I)) i xs e (T+10040) (by
    intro a ha
    have ht := hT a ha
    have hn := Realizer.time_not_le (p i (a,e))
    have hv := volume_bool (p i (a,e))
    simp only [time_comp,time_uniform]
    omega)
  have hn := Realizer.time_not_le (xs.any (fun a => !(p i (a,e))))
  have hv := volume_bool (xs.any (fun a => !(p i (a,e))))
  simp only [all,time_congr,time_comp,time_uniform,Function.comp_apply]
  nlinarith [volume_pos xs,volume_pos e]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_replicate_unit (m : ℕ) : volume (List.replicate m ()) = 2*m+1 := by
  change (enc (List.replicate m ())).size = _
  rw [Realizer.encode_replicate_unit]
  exact volume_nat m

namespace Uniform
variable {I : Type u37} {α : I → Type u38} {β : I → Type u39} {γ : I → Type u40}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

omit [∀ i, Coding (β i)] [∀ i, Coding (γ i)] in
theorem foldTime_iterate_le {f : ∀ i, α i → α i} (R : Uniform f)
    (i : I) (m : ℕ) (a : α i) (T V : ℕ)
    (hT : ∀ j < m, R.time i ((f i)^[j] a) ≤ T)
    (hV : ∀ j ≤ m, volume ((f i)^[j] a) ≤ V) :
    Realizer.foldTime ((snd.comp R : Uniform (fun i (x : Unit × α i) => f i x.2)).specialize i)
      a (List.replicate m ()) ≤ m*(T+100*(V+m+1))+1 := by
  induction m generalizing a with
  | zero => simp only [List.replicate_zero,Realizer.foldTime,Nat.zero_mul,Nat.zero_add]; rfl
  | succ m ih =>
    have hv := hV 0 (by omega)
    have hw := hV 1 (by omega)
    have ht := hT 0 (by omega)
    have hi := ih (f i a)
      (fun j hj => by simpa only [Function.iterate_succ_apply] using hT (j+1) (by omega))
      (fun j hj => by simpa only [Function.iterate_succ_apply] using hV (j+1) (by omega))
    simp only [Function.iterate_zero_apply,Function.iterate_one] at hv hw ht
    rw [List.replicate_succ,Realizer.foldTime]
    change (snd.comp R).time i ((),a)+_+20*(volume (() :: List.replicate m ())+volume a+volume (f i a)+1) ≤ _
    simp only [time_comp,time_snd,volume_pair,volume_unit,volume_cons,volume_replicate_unit,Function.comp_apply]
    nlinarith

omit [∀ i, Coding (β i)] [∀ i, Coding (γ i)] in
theorem time_iterate_le {f : ∀ i, α i → α i} (R : Uniform f)
    (i : I) (m : ℕ) (a : α i) (T V : ℕ)
    (hT : ∀ j < m, R.time i ((f i)^[j] a) ≤ T)
    (hV : ∀ j ≤ m, volume ((f i)^[j] a) ≤ V) :
    R.iterate.time i (m,a) ≤ 10000*(m+1)*(T+V+m+1) := by
  have hf := foldTime_iterate_le R i m a T V hT hV
  have hv := hV 0 (Nat.zero_le _)
  simp only [Function.iterate_zero_apply] at hv
  simp only [iterate,time_congr,time_comp,onFst,time_pair,time_fst,time_snd,time_uniform,
    Realizer.unroll,Realizer.time_reinterpret,Function.comp_apply,time_fold,volume_pair,
    volume_nat,volume_replicate_unit]
  nlinarith

end Uniform
end ThreeMachine.StackCompiler
end

end OAI
end


section
-- module Polynomial
namespace OAI

universe u1 u2

section

namespace ThreeMachine.StackCompiler

def Poly {I : Type u1} (size f : I → ℕ) (d : ℕ) : Prop :=
  Majorized f (fun i => (size i+2)^d)

namespace Poly
variable {I : Type u2} {s f g : I → ℕ} {d e : ℕ}

theorem lift (h : Poly s f d) (hde : d ≤ e) : Poly s f e :=
  h.trans (Majorized.pow_mono (fun _ => by omega) hde)

theorem of_le (h : ∀ i, f i ≤ g i) (hg : Poly s g d) : Poly s f d :=
  (Majorized.of_le h).trans hg

theorem const (s : I → ℕ) (C : ℕ) : Poly s (fun _ => C) 0 :=
  Majorized.const C (fun _ => by simp)

theorem base (s : I → ℕ) : Poly s (fun i => s i+2) 1 := by
  simpa only [Poly,Nat.pow_one] using Majorized.refl (fun i => s i+2)

theorem size (s : I → ℕ) : Poly s s 1 :=
  of_le (fun _ => by omega) (base s)

theorem add (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun i => f i+g i) (max d e) :=
  Majorized.add (hf.lift (le_max_left _ _)) (hg.lift (le_max_right _ _))

theorem mul (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun i => f i*g i) (d+e) := by
  simpa only [Poly,Nat.pow_add] using Majorized.mul hf hg

theorem pow (hf : Poly s f d) (k : ℕ) : Poly s (fun i => (f i)^k) (d*k) := by
  simpa only [Poly,Nat.pow_mul] using Majorized.pow hf k

theorem max (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun i => max (f i) (g i)) (max d e) :=
  of_le (fun _ => by omega) (add hf hg)

end Poly
end ThreeMachine.StackCompiler

end

end OAI
end


section
-- module VolumeBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16

section
namespace ThreeMachine.StackCompiler
namespace Realizer
variable {α : Type u1} [Coding α]

theorem time_iterate_le {f : α → α} (R : Realizer f) (m : ℕ) (a : α) (T V : ℕ)
    (hT : ∀ j < m, R.time (f^[j] a) ≤ T)
    (hV : ∀ j ≤ m, volume (f^[j] a) ≤ V) :
    R.iterate.time (m,a) ≤ 10000*(m+1)*(T+V+m+1) := by
  exact Uniform.time_iterate_le (R.uniform Unit) () m a T V hT hV

theorem time_add_le (a b : ℕ) : add.time (a,b) ≤ 10000000*(a+b+1)^2 := by
  have h := time_iterate_le succ a b (200*(a+b+1)) (2*(a+b)+1)
    (fun j hj => by rw [iterate_succ]; exact (time_succ_le _).trans (by omega))
    (fun j hj => by rw [iterate_succ,volume_nat]; omega)
  change succ.iterate.time (a,b) ≤ _
  nlinarith

theorem time_sub_le (a b : ℕ) : sub.time (a,b) ≤ 10000000*(a+b+1)^2 := by
  have h := time_iterate_le pred b a (2*a+3) (2*a+1)
    (fun j _ => by rw [iterate_pred]; change volume (a-j)+2 ≤ _; rw [volume_nat]; omega)
    (fun j _ => by rw [iterate_pred,volume_nat]; omega)
  simp only [sub,time_congr,time_comp,swap,time_pair,time_fst,time_snd,volume_pair,volume_nat]
  nlinarith

theorem time_le_le (a b : ℕ) : le.time (a,b) ≤ 1000000000*(a+b+1)^2 := by
  have hs := time_sub_le a b
  have hp := time_test_le (fun n : ℕ => decide (0 < n)) (by intro n; cases n <;> rfl) (a-b)
  change positive.time (a-b) ≤ 10000*(volume (a-b)+1) at hp
  simp only [volume_nat] at hp
  have hn := time_not_le (decide (0 < a-b))
  have hv := volume_bool (decide (0 < a-b))
  simp only [le,time_congr,time_comp,isZero,volume_nat]
  have hsq : a+b+1 ≤ (a+b+1)^2 := le_self_pow (by omega) (by decide)
  omega

theorem time_eqNat_le (a b : ℕ) : eqNat.time (a,b) ≤ 10000000000*(a+b+1)^2 := by
  have hl := time_le_le a b
  have hr := time_le_le b a
  have ha := time_and_le (decide (a ≤ b),decide (b ≤ a))
  have hv := volume_bool (decide (a ≤ b))
  have hw := volume_bool (decide (b ≤ a))
  simp only [eqNat,time_congr,time_comp,time_pair,swap,time_fst,time_snd,volume_pair,volume_nat,
    Function.comp_apply]
  nlinarith

end Realizer
namespace Uniform
variable {I : Type u2} {α : I → Type u3} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_prod {α : Type u4} {β : Type u5} [Coding α] [Coding β] (x : α × β) :
    volume x = volume x.1+volume x.2+1 := by cases x; exact volume_pair _ _

@[simp] theorem volume_state {n : ℕ} (x : Algorithm.State (Fin n)) :
    volume x = volume x.left+volume x.middle+volume x.right+2 := by
  change volume (x.left,(x.middle,x.right)) = _
  simp only [volume_pair]; omega

@[simp] theorem volume_cardinal {n : ℕ} (x : Cardinal n) : volume x = 2*n+1 := volume_nat n

theorem volume_state_le {n : ℕ} (x : Algorithm.State (Fin n)) : volume x ≤ 12*(n+1)^2 := by
  have h₁ := volume_finset_le x.left
  have h₂ := volume_finset_le x.middle
  have h₃ := volume_finset_le x.right
  rw [volume_state]
  have hpos : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  omega

namespace Poly
variable {I : Type u6} {s n f : I → ℕ} {d : ℕ}

theorem precomp (h : Poly s f d) {J : Type u7} (g : J → I) : Poly (s ∘ g) (f ∘ g) d := Majorized.precomp h g

theorem volumeNat (h : Poly s f d) : Poly s (fun i => volume (f i)) d := by
  simp only [volume_nat]
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (h); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega))

theorem volumeBool (s : I → ℕ) (b : I → Bool) : Poly s (fun i => volume (b i)) 0 :=
  of_le (fun i => volume_bool (b i)) (const s 3)

theorem volumeFin (hn : Poly s n d) (v : ∀ i, Fin (n i)) : Poly s (fun i => volume (v i)) d := by
  apply of_le (g := fun i => 2*n i+1) (by intro i; rw [volume_fin]; have := (v i).isLt; omega)
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hn); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega))

theorem volumeFinset (hn : Poly s n d) (v : ∀ i, Finset (Fin (n i))) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_finset_le (v i))
  (have polyH0 := Poly.const (s) (3); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem volumeState (hn : Poly s n d) (v : ∀ i, Algorithm.State (Fin (n i))) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_state_le (v i))
  (have polyH0 := Poly.const (s) (12); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

variable {α : I → Type u8} {β : I → Type u9} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem volumeProd (f : ∀ i, α i × β i) {d e : ℕ}
    (h₁ : Poly s (fun i => volume (f i).1) d) (h₂ : Poly s (fun i => volume (f i).2) e) :
    Poly s (fun i => volume (f i)) (Max.max d e) := by
  simp only [volume_prod]
  (have polyH0 := Poly.add (h₁) (h₂); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add polyH0 polyH1; exact Poly.lift polyH2 (by first | decide +kernel | omega))

omit [∀ i, Coding (β i)] in
theorem volumeList {xs : ∀ i, List (α i)} {V : I → ℕ} {d e : ℕ}
    (hl : Poly s (fun i => (xs i).length) d) (hV : Poly s V e)
    (hv : ∀ i, ∀ a ∈ xs i, volume a ≤ V i) :
    Poly s (fun i => volume (xs i)) (d+e) := by
  apply of_le (fun i => volume_list_le (xs i) (V i) (hv i))
  (have polyH0 := Poly.const (s) (1); have polyH1 := Poly.add (hV) polyH0; have polyH2 := Poly.mul (hl) polyH1; have polyH3 := Poly.add polyH2 polyH0; exact Poly.lift polyH3 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_ofFn {α : Type u10} [Coding α] {n : ℕ} (f : Fin n → α) :
    volume (List.ofFn f) = volume f := rfl

@[simp] theorem volume_sort {n : ℕ} (s : Finset (Fin n)) : volume (s.sort (· ≤ ·)) = volume s := rfl

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

@[simp] theorem time_functionListAny (d : I → ℕ) (i : I) (f : Fin (d i) → α i) :
    (functionListAny d).time i f = volume f+2 := rfl

@[simp] theorem time_finValue (d : I → ℕ) (i : I) (v : Fin (d i)) :
    (finValue d).time i v = volume v+2 := rfl

@[simp] theorem time_reindex {f : ∀ i, α i → β i} (R : Uniform f) {J : Type u16}
    (φ : J → I) (j : J) (x : α (φ j)) : (R.reindex φ).time j x = R.time (φ j) x := rfl

end Uniform
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

end ThreeMachine.StackCompiler
end

end OAI
end


section
-- module PolynomialLoops
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

section
namespace ThreeMachine.StackCompiler
namespace Poly
variable {I : Type u1} {J : Type u2} {s : J → ℕ}
variable {α : I → Type u3} {β : I → Type u4} {γ : I → Type u5} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

abbrev Pool := Σ j, {a : α (idx j) // a ∈ xs j}

theorem reparam {K : Type u6} {u f : K → ℕ} {d r : ℕ}
    (h : Poly u f d) (g : J → K) (hs : Poly s (fun j => u (g j)) r) :
    Poly s (fun j => f (g j)) (d*r) := by
  obtain ⟨C,hC⟩ := h
  apply of_le (fun j => hC (g j))
  have hN : Poly s (fun j => u (g j)+2) r := by
    simpa only [Nat.max_zero] using hs.add (const s 2)
  simpa only [Nat.zero_add,Nat.mul_comm] using (const s C).mul (hN.pow d)

theorem powerBase (s : J → ℕ) (C d : ℕ) : Poly s (fun j => C*(s j+2)^d) d := by
  (have polyH0 := Poly.const (s) (C); have polyH1 := Poly.base (s); have polyH2 := Poly.pow polyH1 (d); have polyH3 := Poly.mul polyH0 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega))

theorem anyTime {p : ∀ i, α i × γ i → Bool} (P : Uniform p) {l t vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun q : Pool idx xs => s q.1)
      (fun q => P.time (idx q.1) (q.2.1,e q.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => P.any.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx ve)) := by
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_any P (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  (have polyH0 := Poly.const (s) (10000000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hx); have polyH5 := Poly.add polyH4 (he); have polyH6 := Poly.add polyH5 polyH1; have polyH7 := Poly.mul polyH3 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))

theorem allTime {p : ∀ i, α i × γ i → Bool} (P : Uniform p) {l t vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun q : Pool idx xs => s q.1)
      (fun q => P.time (idx q.1) (q.2.1,e q.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => P.all.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx ve)) := by
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_all P (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  (have polyH0 := Poly.const (s) (1000000000000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hx); have polyH5 := Poly.add polyH4 (he); have polyH6 := Poly.add polyH5 polyH1; have polyH7 := Poly.mul polyH3 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler
namespace Poly
variable {J : Type u7} {s : J → ℕ} {d : ℕ}

theorem finsetCard {n : J → ℕ} (hn : Poly s n d) (a : ∀ j, Finset (Fin (n j))) :
    Poly s (fun j => (a j).card) d :=
  of_le (fun j => by simpa only [Fintype.card_fin] using Finset.card_le_univ (a j)) hn

variable {α : J → Type u8} {β : J → Type u9} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem volumePool (xs : ∀ j, List (α j)) (h : Poly s (fun j => volume (xs j)) d) :
    Poly (fun q : Pool _root_.id xs => s q.1) (fun q => volume q.2.1) d :=
  of_le (fun q => volume_mem_le q.2.2) (h.precomp Sigma.fst)

end Poly
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u10} {s n : J → ℕ} {d : ℕ}

theorem lengthSort (a : ∀ j, Finset (Fin (n j)))
    (h : Poly s (fun j => (a j).card) d) :
    Poly s (fun j => ((a j).sort (· ≤ ·)).length) d := by simpa only [Finset.length_sort] using h

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u12} {J : Type u13} {α : I → Type u14} {β : I → Type u15} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u16} {s n : J → ℕ} {d v : ℕ}

def FinPool (n : J → ℕ) := Σ j, Fin (n j)

theorem iteNat (p : J → Prop) [∀ j, Decidable (p j)] {f g : J → ℕ} {d e : ℕ}
    (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun j => if p j then f j else g j) (Max.max d e) :=
  of_le (g := fun j => Max.max (f j) (g j)) (fun j => by split <;> omega) (hf.max hg)

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u18} {J : Type u19} {s : J → ℕ}
variable {α : I → Type u20} {β : I → Type u21} {γ : I → Type u22} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u23} {s : J → ℕ} {d e : ℕ} {α : J → Type u24} {β : J → Type u25}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u26} {s : J → ℕ} {α : J → Type u27} [∀ j, Coding (α j)]
abbrev ListPool (xs : ∀ j, List (α j)) := Σ j, {a : α j // a ∈ xs j}
theorem listVolume (xs : ∀ j, List (α j)) {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun q : ListPool xs => s q.1) (fun q => volume q.2.1) v) :
    Poly s (fun j => volume (xs j)) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  exact volumeList hl (powerBase s C v) (fun j a ha => hC ⟨j,⟨a,ha⟩⟩)
end ThreeMachine.StackCompiler.Poly
end

end OAI
end


section
-- module PolynomialLists
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16

section
namespace ThreeMachine.StackCompiler

@[simp] theorem volume_block {n : ℕ} (b : Algorithm.Block (Fin n)) :
    volume b = volume b.length+volume b.time+1 := by
  change volume (b.length,b.time) = _
  rw [volume_pair]

namespace Poly
variable {J : Type u1} {s n : J → ℕ} {d e : ℕ}

variable {α : J → Type u2} {β : J → Type u3} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem volumeOption (o : ∀ j, Option (α j)) {v : J → ℕ}
    (h : Poly s v d) (hv : ∀ j, ∀ a ∈ o j, volume a ≤ v j) : Poly s (fun j => volume (o j)) d := by
  apply of_le (fun j => volume_option_le (o j) (v j) (hv j))
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (h) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u4} {J : Type u5} {s : J → ℕ}
variable {α : I → Type u6} {β : I → Type u7} {γ : I → Type u8} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

variable (o : ∀ j, Option (α (idx j)))

theorem optionMapTime {f : ∀ i, α i × γ i → β i} (R : Uniform f) {t vo ve v : ℕ}
    (ht : Poly (fun p : Pool idx (fun j => (o j).toList) => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (ho : Poly s (fun j => volume (o j)) vo)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx (fun j => (o j).toList) => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.optionMap.time (idx j) (o j,e j)) (Max.max t (Max.max vo (Max.max ve v))) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_optionMap R (idx j) (o j) (e j)
    (C*(s j+2)^t) (D*(s j+2)^v) (fun a ha => hC ⟨j,⟨a,by simpa using ha⟩⟩)
      (fun a ha => hD ⟨j,⟨a,by simpa using ha⟩⟩))
  (have polyH0 := Poly.const (s) (1000000); have polyH1 := Poly.add (hT) (ho); have polyH2 := Poly.add polyH1 (he); have polyH3 := Poly.add polyH2 (hV); have polyH4 := Poly.const (s) (1); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.mul polyH0 polyH5; exact Poly.lift polyH6 (by first | decide +kernel | omega))

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u9} {s : J → ℕ} {d e : ℕ} {α : J → Type u10} {β : J → Type u11}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem volumeIte (p : J → Prop) [∀ j, Decidable (p j)] (a b : ∀ j, α j)
    (ha : Poly s (fun j => volume (a j)) d) (hb : Poly s (fun j => volume (b j)) e) :
    Poly s (fun j => volume (if p j then a j else b j)) (Max.max d e) := by
  convert iteNat p ha hb using 1
  funext j; split <;> rfl

omit [∀ j, Coding (α j)] in
theorem volumeOptionMap (f : ∀ j, α j → β j) (o : ∀ j, Option (α j))
    (h : Poly (fun p : ListPool (fun j => (o j).toList) => s p.1)
      (fun p => volume (f p.1 p.2.1)) d) : Poly s (fun j => volume ((o j).map (f j))) d := by
  obtain ⟨C,hC⟩ := h
  apply volumeOption _ (powerBase s C d)
  intro j b hb
  cases ho : o j with
  | none => simp [ho] at hb
  | some a =>
    have he : f j a = b := by simpa [ho] using hb
    subst b
    exact hC ⟨j,⟨a,by simp [ho]⟩⟩

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u12} {s : J → ℕ} {d : ℕ} {K V : J → Type}
variable [∀ j, Coding (K j)] [∀ j, Coding (V j)] [∀ j, DecidableEq (K j)]

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u13} {s : J → ℕ} {d : ℕ} {α : J → Type u14} [∀ j, Coding (α j)]
theorem volumeOptionToList (o : ∀ j, Option (α j))
    (h : Poly s (fun j => volume (o j)) d) :
    Poly s (fun j => volume (o j).toList) d := by
  simpa only [volume_optionToList] using h
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u15} {s : J → ℕ} {d e : ℕ} {α : J → Type u16}
theorem lengthCons (a : ∀ j, α j) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => (a j :: xs j).length) d := by
  simp only [List.length_cons]; (have polyH0 := Poly.const (s) (1); have polyH1 := Poly.add (h) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | omega))

end ThreeMachine.StackCompiler.Poly
end

end OAI
end


