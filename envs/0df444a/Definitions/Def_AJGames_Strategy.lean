-- Prove2me | Definitions.Def_AJGames_Strategy
-- name    : AJGames_Strategy
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:26:58.068625+00:00
-- url     : https://prove2.me/theorems/576242b9-a1ba-4cb4-b907-a77c5be0080a
-- title:
--   Strategies in AJ games and the tensor of strategies
-- statement:
--   A **strategy** $\sigma$ for Player in $A$ is a set of positions of $A$ satisfying five conditions:
--
--   1. it contains the empty sequence;
--   2. it is prefix-closed;
--   3. Opponent opens: every nonempty element starts with an Opponent move;
--   4. it is deterministic: if $sa$ and $sb$ are in $\sigma$ with $a,b$ Player moves, then $a=b$;
--   5. it is receptive: if $s\in\sigma$, $a$ is an Opponent move and $sa$ is a position, then $sa\in\sigma$.
--
--   For strategies $\sigma$ on $A$ and $\tau$ on $B$, the **tensor** $\sigma\otimes\tau$ is the set of positions $s$ of $A\otimes B$ with $s{\restriction}A\in\sigma$ and $s{\restriction}B\in\tau$; the file proves that it is again a strategy.
--
--   The tensor of strategies runs two strategies side by side; the online-algorithm milestones about the tensor are stated for it.
--
--   **Formalization Note** That $\sigma\otimes\tau$ is deterministic uses the tensor's switching rule: a Player move stays in the component of the move before it.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §3.1 Definition 3 (strategies) and §3.3 (tensor of strategies)

import Mathlib
import Definitions.Def_AJGames_Game
import Definitions.Def_AJGames_Tensor

/-!
# Strategies in Abramsky–Jagadeesan games, and their tensor

Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*,
J. Symbolic Logic 59(2) (1994), 543–574: Definition 3 (strategies) and §3.3 (tensor of strategies,
`σ ⊗ τ = {s ∈ P_{A⊗B} | s↾A ∈ σ, s↾B ∈ τ}`).

**Formalization Note.** Finite-play (safety) fragment: winning conditions on infinite plays are
omitted. That `σ ⊗ τ` is again a strategy uses that in a tensor only Opponent switches component,
so a Player move stays in the component of the move before it.
-/

namespace AJGames

universe u

open Game

/-- A strategy for Player in `A` (Definition 3): non-empty, prefix-closed, a subset of the
positions, with Opponent opening, determinism on Player moves, and receptiveness to Opponent moves. -/
structure Strategy (A : Game.{u}) where
  carrier : Set (List A.M)
  nil_mem : [] ∈ carrier
  subset_pos : carrier ⊆ A.pos
  prefix_closed : ∀ s t : List A.M, s <+: t → t ∈ carrier → s ∈ carrier
  first_O : ∀ a s, a :: s ∈ carrier → A.lab a = Pl.O
  deterministic : ∀ s a b, s ++ [a] ∈ carrier → s ++ [b] ∈ carrier →
    A.lab a = Pl.P → A.lab b = Pl.P → a = b
  receptive : ∀ s a, s ∈ carrier → A.lab a = Pl.O → s ++ [a] ∈ A.pos → s ++ [a] ∈ carrier

section Proj

variable {α β : Type u}

theorem projL_append (s t : List (α ⊕ β)) : projL (s ++ t) = projL s ++ projL t := by
  simp [projL, List.filterMap_append]
theorem projR_append (s t : List (α ⊕ β)) : projR (s ++ t) = projR s ++ projR t := by
  simp [projR, List.filterMap_append]
@[simp] theorem projL_nil' : projL ([] : List (α ⊕ β)) = [] := rfl
@[simp] theorem projR_nil' : projR ([] : List (α ⊕ β)) = [] := rfl
@[simp] theorem projL_cons_inl (a : α) (s : List (α ⊕ β)) : projL (Sum.inl a :: s) = a :: projL s := by
  simp [projL]
@[simp] theorem projL_cons_inr (b : β) (s : List (α ⊕ β)) : projL (Sum.inr b :: s) = projL s := by
  simp [projL, List.filterMap_cons, Sum.getLeft?]
@[simp] theorem projR_cons_inl (a : α) (s : List (α ⊕ β)) : projR (Sum.inl a :: s) = projR s := by
  simp [projR, List.filterMap_cons, Sum.getRight?]
@[simp] theorem projR_cons_inr (b : β) (s : List (α ⊕ β)) : projR (Sum.inr b :: s) = b :: projR s := by
  simp [projR]
theorem projL_snoc_inl (s : List (α ⊕ β)) (x : α) : projL (s ++ [Sum.inl x]) = projL s ++ [x] := by
  simp [projL_append]
theorem projL_snoc_inr (s : List (α ⊕ β)) (y : β) : projL (s ++ [Sum.inr y]) = projL s := by
  simp [projL_append]
theorem projR_snoc_inl (s : List (α ⊕ β)) (x : α) : projR (s ++ [Sum.inl x]) = projR s := by
  simp [projR_append]
theorem projR_snoc_inr (s : List (α ⊕ β)) (y : β) : projR (s ++ [Sum.inr y]) = projR s ++ [y] := by
  simp [projR_append]

end Proj

variable {A B : Game.{u}}

/-- In a tensor sequence, a Player move continues in the component of the move before it. -/
theorem tensor_P_same_component {s : List (A.M ⊕ B.M)} {m a : A.M ⊕ B.M}
    (h : (Game.tensor A B).pos (s ++ [a])) (hm : s.getLast? = some m)
    (ha : Sum.elim A.lab B.lab a = Pl.P) : m.isLeft = a.isLeft := by
  have hch : List.IsChain (TR A.lab B.lab) (s ++ [a]) := h.1
  have hTR : TR A.lab B.lab m a := (List.isChain_append.1 hch).2.2 m hm a (by simp)
  rcases hTR.2 with h' | h'
  · exact h'
  · rw [ha] at h'; cases h'

/-- The tensor of strategies `σ ⊗ τ` (§3.3). -/
def tensorS (σ : Strategy A) (τ : Strategy B) : Strategy (Game.tensor A B) where
  carrier := {s | s ∈ (Game.tensor A B).pos ∧ projL s ∈ σ.carrier ∧ projR s ∈ τ.carrier}
  nil_mem := ⟨(Game.tensor A B).nil_mem, by simpa using σ.nil_mem, by simpa using τ.nil_mem⟩
  subset_pos := fun _ h => h.1
  prefix_closed := by
    intro s t hst ht
    exact ⟨(Game.tensor A B).prefix_closed s t hst ht.1,
      σ.prefix_closed _ _ (hst.filterMap Sum.getLeft?) ht.2.1,
      τ.prefix_closed _ _ (hst.filterMap Sum.getRight?) ht.2.2⟩
  first_O := by
    intro a s h
    cases a with
    | inl x => have := σ.first_O x (projL s) (by simpa using h.2.1); simpa using this
    | inr y => have := τ.first_O y (projR s) (by simpa using h.2.2); simpa using this
  deterministic := by
    intro s a b ha hb hPa hPb
    have hPa' : Sum.elim A.lab B.lab a = Pl.P := hPa
    have hPb' : Sum.elim A.lab B.lab b = Pl.P := hPb
    cases hl : s.getLast? with
    | none =>
      have : s = [] := List.getLast?_eq_none_iff.1 hl
      subst this
      cases a with
      | inl x =>
        have h2 : projL ([] ++ [Sum.inl x]) ∈ σ.carrier := ha.2.1
        have := σ.first_O x [] (by simpa using h2)
        exact absurd (this.symm.trans (show A.lab x = Pl.P from hPa')) (by decide)
      | inr y =>
        have h2 : projR ([] ++ [Sum.inr y]) ∈ τ.carrier := ha.2.2
        have := τ.first_O y [] (by simpa using h2)
        exact absurd (this.symm.trans (show B.lab y = Pl.P from hPa')) (by decide)
    | some m =>
      have e1 := tensor_P_same_component ha.1 hl hPa'
      have e2 := tensor_P_same_component hb.1 hl hPb'
      cases a with
      | inl x =>
        cases b with
        | inl y =>
          have ha2 : projL (s ++ [Sum.inl x]) ∈ σ.carrier := ha.2.1
          have hb2 : projL (s ++ [Sum.inl y]) ∈ σ.carrier := hb.2.1
          rw [projL_snoc_inl] at ha2 hb2
          have := σ.deterministic (projL s) x y ha2 hb2 hPa hPb
          rw [this]
        | inr y => cases m <;> simp_all
      | inr x =>
        cases b with
        | inl y => cases m <;> simp_all
        | inr y =>
          have ha2 : projR (s ++ [Sum.inr x]) ∈ τ.carrier := ha.2.2
          have hb2 : projR (s ++ [Sum.inr y]) ∈ τ.carrier := hb.2.2
          rw [projR_snoc_inr] at ha2 hb2
          have := τ.deterministic (projR s) x y ha2 hb2 hPa hPb
          rw [this]
  receptive := by
    intro s a hs hO hpos
    refine ⟨hpos, ?_, ?_⟩
    · cases a with
      | inl x =>
        have hpos' : projL (s ++ [Sum.inl x]) ∈ A.pos := hpos.2.1
        rw [projL_snoc_inl] at hpos' ⊢
        exact σ.receptive _ x hs.2.1 hO hpos'
      | inr y => rw [projL_snoc_inr]; exact hs.2.1
    · cases a with
      | inl x => rw [projR_snoc_inl]; exact hs.2.2
      | inr y =>
        have hpos' : projR (s ++ [Sum.inr y]) ∈ B.pos := hpos.2.2
        rw [projR_snoc_inr] at hpos' ⊢
        exact τ.receptive _ y hs.2.2 hO hpos'

end AJGames


