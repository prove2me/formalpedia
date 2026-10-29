-- Prove2me | Definitions.Def_PutermanMDP_FiniteHorizon_Model
-- name    : PutermanMDP_FiniteHorizon_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:16.362368+00:00
-- url     : https://prove2.me/theorems/baf96154-57a4-4b6a-b2fa-1e5265616793
-- title:
--   Discrete finite-horizon MDP, histories and admissible policies
-- statement:
--   Let $S$ be a nonempty finite or countable state space and $A_s$ a nonempty set of admissible actions at state $s$. A finite-horizon model has decision epochs $0,\ldots,H-1$, a terminal epoch $H$, transition probabilities $p_t(j\mid s,a)$, decision rewards $r_t(s,a)$, and a terminal reward $g(s)$. Each transition row is a probability distribution. For some real $C\ge0$,
--   $$
--   |r_t(s,a)|\le C\quad(t<H),\qquad |g(s)|\le C.
--   $$
--   A history $h_t=(s_0,a_0,\ldots,s_{t-1},a_{t-1},s_t)$ contains the complete observed past. A history-dependent randomized policy assigns a probability mass function on $A_{s_t}$ to every history. Deterministic history policies choose a single admissible action from each history; deterministic Markov policies choose one using only $t$ and $s_t$.
--
--   This interface supplies the data and policy classes for the expected total reward criterion. It imposes no Bellman equation, optimality condition, or existence of maximizing actions.
--
--   **Formalization Note** $H=N-1$ and Lean epoch $t$ corresponds to book epoch $t+1$. Past pairs are stored chronologically. Action sets need not be finite; randomized actions are discrete probability mass functions. State nonemptiness is imposed by the theorem binders. Policies and data are extended beyond $H$, where they are unused.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, pp. 74, 78–80 (PDF 90, 94–96), §§4.1–4.2, Eq. (4.1.3); https://doi.org/10.1002/9780470316887.ch4

import Mathlib

namespace PutermanMDP.FiniteHorizon

/-- A history consists of past state-action pairs in chronological order and the current state.
Its list length is the zero-based current epoch. No positive-probability restriction is imposed. -/
structure History (S A : Type) where
  past : List (S × A)
  state : S

def History.time {S A : Type} (h : History S A) : ℕ := h.past.length

def History.initial {S A : Type} (s : S) : History S A := ⟨[], s⟩

def History.extend {S A : Type} (h : History S A) (a : A) (j : S) : History S A :=
  ⟨h.past ++ [(h.state, a)], j⟩

/-- `horizon` counts decisions. The terminal epoch is `horizon`, corresponding to epoch
`N = horizon + 1` under one-based indexing. Rewards may have either sign. -/
structure Model (S A : Type) [Countable S] where
  horizon : ℕ
  available : S → Set A
  available_nonempty : ∀ s, (available s).Nonempty
  transition : ℕ → (s : S) → {a // a ∈ available s} → PMF S
  reward : ℕ → (s : S) → {a // a ∈ available s} → ℝ
  terminal : S → ℝ
  bounded : ∃ C : ℝ, 0 ≤ C ∧
    (∀ t, t < horizon → ∀ s a, |reward t s a| ≤ C) ∧
    (∀ s, |terminal s| ≤ C)

/-- All history-dependent randomized decision rules, extended harmlessly beyond the horizon. -/
def Policy {S A : Type} [Countable S] (M : Model S A) : Type :=
  (h : History S A) → PMF {a // a ∈ M.available h.state}

def HistoryPolicy {S A : Type} [Countable S] (M : Model S A) : Type :=
  (h : History S A) → {a // a ∈ M.available h.state}

def MarkovPolicy {S A : Type} [Countable S] (M : Model S A) : Type :=
  ℕ → (s : S) → {a // a ∈ M.available s}

noncomputable def HistoryPolicy.randomized {S A : Type} [Countable S] {M : Model S A}
    (d : HistoryPolicy M) : Policy M := fun h => PMF.pure (d h)

noncomputable def MarkovPolicy.randomized {S A : Type} [Countable S] {M : Model S A}
    (d : MarkovPolicy M) : Policy M := fun h => PMF.pure (d h.time h.state)

end PutermanMDP.FiniteHorizon


