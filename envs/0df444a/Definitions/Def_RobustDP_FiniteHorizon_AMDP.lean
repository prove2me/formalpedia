-- Prove2me | Definitions.Def_RobustDP_FiniteHorizon_AMDP
-- name    : RobustDP_FiniteHorizon_AMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:14.814994+00:00
-- url     : https://prove2.me/theorems/9220d93b-1e5d-47b9-bf75-0016ed4227cd
-- title:
--   Finite horizon ambiguous Markov decision process (AMDP) and its histories
-- statement:
--   A **finite horizon ambiguous Markov decision process** (AMDP) in the sense of Iyengar consists of
--
--   1. a horizon $N\ge 1$: decisions are made at the epochs $t\in T=\{0,\dots,N-1\}$, and $N$ is the terminal epoch;
--   2. a countable state set $\mathcal S$ and a countable action set $\mathcal A$;
--   3. for every epoch $t$ and state $s$, a nonempty set $\mathcal A_t(s)\subseteq\mathcal A$ of admissible actions;
--   4. for every epoch $t$, state $s$ and admissible action $a\in\mathcal A_t(s)$, a nonempty set $\mathcal P_t(s,a)\subseteq\mathcal M(\mathcal S)$ of probability measures on the next state (the *ambiguity set*; it need not be convex or closed);
--   5. rewards $r_t(s,a,s')$, received when $a$ is chosen in $s$ at epoch $t$ and the next state is $s'$, and a terminal reward $r_N(s)$;
--   6. a bound $R$ with $|r_t(s,a,s')|\le R$ and $|r_N(s)|\le R$ for all arguments.
--
--   If at epoch $t$ action $a$ is taken in state $s$, the next state is drawn from some measure $p\in\mathcal P_t(s,a)$ that the decision maker does not know.
--
--   A **history** at epoch $n$ is $h_n=(s_0,a_0,\dots,s_{n-1},a_{n-1},s_n)$; its current state is $s_n$. Appending the action $a$ chosen at epoch $n$ and the next state $s$ gives the history $(h_n,a,s)$ at epoch $n+1$.
--
--   This is the model of Section 2 on which every statement of the mission is built.
--
--   **Formalization Note** One state type and one action type serve all epochs: the page's epoch-dependent discrete sets $\mathcal S_t$ embed into their disjoint union, and states that cannot occur at epoch $t$ do not affect any value. Nonemptiness of $\mathcal A_t(s)$ and $\mathcal P_t(s,a)$ is implicit on the page and stated here (otherwise the suprema and infima below range over empty sets). The bound $R$ is an added hypothesis: Section 2 states no bound, but with countably many states the expectations in (4) and (8) and the suprema in (5) and (10) need it to be finite. The bound is imposed on every argument, including inadmissible actions, whose rewards play no role. A history is stored as the $n$ past state–action pairs together with the current state.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), pp. 3–4, Section 2 (decision epochs, M(B), P_t(s, a), rewards, AMDP, histories h_t)

import Mathlib

namespace RobustDP.FiniteHorizon

/-- A finite horizon ambiguous Markov decision process (AMDP), Iyengar (TR-2002-07), Section 2,
pp. 3–4. Decision epochs are `0, …, N - 1` with `N ≥ 1`, and `N` is the terminal epoch. States
and actions live in countable types `S` and `A`. At epoch `t` in state `s` the admissible actions
are `Aset t s` (nonempty), and for each admissible action `a` the set of conditional measures on
the next state is `P t s a ⊆ M(S)` (nonempty, otherwise arbitrary). The decision maker receives
`r t s a s'` at epoch `t`, and `rN s` at the terminal epoch. Rewards are bounded (an added
hypothesis: the page states none, but the expectations and suprema of (4)–(10) need it). -/
structure AMDP (S A : Type*) [Countable S] [Countable A] where
  /-- The horizon: decision epochs are `0, …, N - 1`. -/
  N : ℕ
  one_le_N : 1 ≤ N
  /-- Admissible actions `A_t(s)`. -/
  Aset : ℕ → S → Set A
  Aset_nonempty : ∀ t < N, ∀ s, (Aset t s).Nonempty
  /-- The ambiguity sets `P_t(s, a) ⊆ M(S)`. -/
  P : ℕ → S → A → Set (PMF S)
  P_nonempty : ∀ t < N, ∀ s, ∀ a ∈ Aset t s, (P t s a).Nonempty
  /-- Rewards `r_t(s, a, s')`. -/
  r : ℕ → S → A → S → ℝ
  /-- Terminal reward `r_N(s)`. -/
  rN : S → ℝ
  bounded : ∃ R : ℝ, (∀ t s a s', |r t s a s'| ≤ R) ∧ ∀ s, |rN s| ≤ R

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

end RobustDP.FiniteHorizon


