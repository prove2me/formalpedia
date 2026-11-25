-- Prove2me | Definitions.Def_SinkReset_Plan
-- name    : SinkReset_Plan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:41:50.022647+00:00
-- url     : https://prove2.me/theorems/fbcf533d-0c94-5fd1-a22f-436cd1e2fa00
-- title:
--   Plan
-- statement:
--   Definitions and structural lemmas for Plan, from Ben Keene (benkeene/sink-reset-thresholds; see pinned Apache-2.0 LICENSE and source headers)'s pinned Sharp reset thresholds for bounded-response synchronization games with a sink development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean

module
public import Definitions.Def_SinkReset_Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SinkReset
namespace Plan
def active {n : ℕ} [NeZero n] (S : Finset (Fin n)) : Finset (Fin n) := S.erase 0
def ResetOn {n : ℕ} [NeZero n] (A : Automaton n)
    (S : Finset (Fin n)) (w : List (Letter n)) : Prop :=
  A.IsWord w ∧ ∀ q ∈ S, act w q = 0
def Within {n : ℕ} [NeZero n] (A : Automaton n)
    (S : Finset (Fin n)) (b : ℕ) : Prop :=
  ∃ w, ResetOn A S w ∧ w.length ≤ b
def SC {n : ℕ} [NeZero n] (A : Automaton n) : Prop :=
  ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q
noncomputable def Z {n : ℕ} [NeZero n] (A : Automaton n) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun q => q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0)
noncomputable def Y {n : ℕ} [NeZero n] (A : Automaton n) : Finset (Fin n) :=
  active Finset.univ \ Z A
def Distances {n : ℕ} [NeZero n] (A : Automaton n) (d : Fin n → ℕ) : Prop :=
  ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
    ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
def potential {n : ℕ} (weight : Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  ∑ q ∈ S, weight q
def kill {n : ℕ} [NeZero n] (i : Fin n) : Letter n :=
  fun q => if q = i then 0 else q
def transposition (n : ℕ) [NeZero n] : Automaton n :=
  { letters := {kill (1 : Fin n)} ∪ {a | ∃ i j : Fin n,
      1 ≤ i.val ∧ j.val = i.val + 1 ∧ a = (Equiv.swap i j : Fin n → Fin n)}
    sink_fixed := by
      rintro a (h | ⟨i, j, hi, hj, rfl⟩)
      · rw [Set.mem_singleton_iff] at h
        subst h
        simp [kill]
      · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · intro h; rw [← h] at hi; simp at hi
        · intro h; rw [← h] at hj; simp at hj }
def predecessor (n : ℕ) : Letter n :=
  fun q => ⟨q.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) q.isLt⟩
def path (n : ℕ) [NeZero n] : Automaton n :=
  { letters := {predecessor n}
    sink_fixed := by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact Fin.ext (by simp [predecessor]) }
def shift (k m : ℕ) : Letter (k + m + 1) :=
  fun q => if hq : q = 0 then 0 else
    ⟨q.val % (k + m) + 1, by
      have h1 : q.val ≠ 0 := fun h => hq (Fin.ext (by simp [h]))
      have h2 := q.isLt
      have h3 := Nat.mod_lt q.val (show 0 < k + m by omega)
      omega⟩
def cycle (k m : ℕ) : Automaton (k + m + 1) :=
  { letters := {shift k m} ∪ {a | ∃ i : Fin (k + m + 1),
      2 ≤ i.val ∧ i.val ≤ k + 1 ∧ a = kill i}
    sink_fixed := by
      rintro a (h | ⟨i, _, _, rfl⟩)
      · rw [Set.mem_singleton_iff] at h
        subst h
        simp [shift]
      · simp [kill] }
def cycleWeight (k m : ℕ) (q : Fin (k + m + 1)) : ℕ :=
  if q = 0 then 0 else if 2 ≤ q.val ∧ q.val ≤ k + 1 then 1 else 2
def cycleDelta (k m : ℕ) (q : Fin (k + m + 1)) : ℕ :=
  if q.val = 1 then 1 else if k + 1 < q.val then k + m + 2 - q.val else 0
noncomputable def delay (k m : ℕ) (S : Finset (Fin (k + m + 1))) : ℕ :=
  sInf {r : ℕ | ∃ q ∈ active S, cycleDelta k m q = r}
noncomputable def cycleRank (k m : ℕ) (S : Finset (Fin (k + m + 1))) : ℕ :=
  (m + 1) * (active S).card + delay k m S
end Plan
end SinkReset


