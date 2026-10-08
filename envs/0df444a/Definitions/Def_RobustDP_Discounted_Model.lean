-- Prove2me | Definitions.Def_RobustDP_Discounted_Model
-- name    : RobustDP_Discounted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:29.171955+00:00
-- url     : https://prove2.me/theorems/e9aed462-557d-4c77-991f-bb50a57191cd
-- title:
--   Discounted ambiguous MDP: countable S, A(s), ambiguity sets P(s, a), bounded reward r(s, a, s′), λ ∈ (0, 1)
-- statement:
--   A **discounted ambiguous Markov decision process** in the sense of Iyengar, Section 3, consists of
--
--   1. a countable state set $\mathcal S$ and a countable action set $\mathcal A$; decisions are made at the epochs $t\in\{0,1,2,\dots\}$;
--   2. for every state $s$, a nonempty set $\mathcal A(s)\subseteq\mathcal A$ of admissible actions;
--   3. for every state $s$ and admissible action $a\in\mathcal A(s)$, a nonempty set $\mathcal P(s,a)\subseteq\mathcal M(\mathcal S)$ of probability measures on the next state (the *ambiguity set*; it need not be convex or closed);
--   4. a reward $r(s,a,s')$, received when $a$ is chosen in $s$ and the next state is $s'$, with a bound $R$ such that $|r(s,a,s')|\le R$ for all $s,s'\in\mathcal S$ and $a\in\mathcal A(s)$;
--   5. a discount factor $\lambda\in(0,1)$.
--
--   None of $\mathcal A(s)$, $\mathcal P(s,a)$, $r$ depends on the epoch. A **history** at epoch $n$ is $h_n=(s_0,a_0,\dots,s_{n-1},a_{n-1},s_n)$ with current state $s_n$; appending the action $a$ and the next state $s$ gives $(h_n,a,s)$. A **deterministic Markov decision rule** is a map $d:\mathcal S\to\mathcal A$ with $d(s)\in\mathcal A(s)$ for all $s$; a **randomized Markov decision rule** assigns to every state $s$ a probability measure $q_s\in\mathcal M(\mathcal A(s))$. For a probability measure $p$ on a discrete set, $\mathbf E^p[f]=\sum_x p(x)f(x)$.
--
--   This is the model of Section 3 on which every statement of the mission is built.
--
--   **Formalization Note** Nonemptiness of $\mathcal A(s)$ and $\mathcal P(s,a)$ is implicit on the page and stated here (otherwise the suprema and infima of (19)–(22) range over empty sets). The page assumes "the reward is bounded, i.e. $\sup_{s,s'\in\mathcal S,a\in\mathcal A(s)} r(s,a,s')=R<\infty$"; it is read as a bound on $|r|$, which the page's own bounds $\pm R/(1-\lambda)$ and its use of $V^\pi\in\mathbf V$ require. A history is stored as the $n$ past state–action pairs together with the current state. $\mathbf E^p[f]$ is the series $\sum_x p(x)f(x)$; it is only applied to bounded $f$, where it converges absolutely.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), pp. 8–9, Section 3 (T = Z₊, S, A(s), P(s, a), bounded reward r(s, a, s′), λ ∈ (0, 1)); histories and decision rules from Section 2, p. 4

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value

namespace RobustDP.Discounted

/-- A discounted ambiguous Markov decision process, Iyengar (TR-2002-07), Section 3, pp. 8–9.
States and actions live in countable types `S` and `A` (the page: `S` and `A(s)` discrete).
In state `s` the admissible actions are `Aset s` (nonempty), and for an admissible action `a`
the set of conditional measures for the next state is `P s a ⊆ M(S)` (nonempty, otherwise
arbitrary: neither convex nor closed). Neither depends on the epoch. The reward `r s a s'` does
not depend on the epoch and is bounded in absolute value on admissible actions, and
`lam ∈ (0, 1)` is the discount factor `λ`. -/
structure Model (S A : Type*) [Countable S] [Countable A] where
  /-- Admissible actions `A(s)`. -/
  Aset : S → Set A
  Aset_nonempty : ∀ s, (Aset s).Nonempty
  /-- The ambiguity sets `P(s, a) ⊆ M(S)`. -/
  P : S → A → Set (PMF S)
  P_nonempty : ∀ s, ∀ a ∈ Aset s, (P s a).Nonempty
  /-- Rewards `r(s, a, s')`. -/
  r : S → A → S → ℝ
  bounded : ∃ R : ℝ, ∀ s, ∀ a ∈ Aset s, ∀ s', |r s a s'| ≤ R
  /-- The discount factor `λ`. -/
  lam : ℝ
  lam_pos : 0 < lam
  lam_lt_one : lam < 1

/-- A history at epoch `n`: `h_n = (s₀, a₀, …, s_{n-1}, a_{n-1}, s_n)`, stored as the `n` past
state–action pairs together with the current state `s_n`. -/
abbrev History (S A : Type*) (n : ℕ) := (Fin n → S × A) × S

/-- The current state `s_n` of a history `h_n`. -/
abbrev History.cur {S A : Type*} {n : ℕ} (h : History S A n) : S := h.2

/-- The history `(h_n, a, s) ∈ H_{n+1}`: append the action `a` taken at epoch `n` and the next
state `s`. -/
def History.extend {S A : Type*} {n : ℕ} (h : History S A n) (a : A) (s : S) :
    History S A (n + 1) :=
  (Fin.snoc h.1 (h.2, a), s)

/-- The history `h_0 = (s₀)` of length zero starting in `s₀`. -/
def History.init {S A : Type*} (s : S) : History S A 0 :=
  (fun i => i.elim0, s)

/-- A deterministic Markov decision rule: a map `d : S → A` with `d(s) ∈ A(s)` for all `s`. -/
def DecisionRule {S A : Type*} [Countable S] [Countable A] (M : Model S A) :=
  {d : S → A // ∀ s, d s ∈ M.Aset s}

/-- A randomized Markov decision rule: for every state `s` a probability measure
`q_s ∈ M(A(s))`, i.e. a law on `A` putting all its mass on `A(s)`. -/
def RandRule {S A : Type*} [Countable S] [Countable A] (M : Model S A) :=
  {q : S → PMF A // ∀ s, ∀ a ∈ (q s).support, a ∈ M.Aset s}

end RobustDP.Discounted


