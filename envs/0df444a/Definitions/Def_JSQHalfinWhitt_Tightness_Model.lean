-- Prove2me | Definitions.Def_JSQHalfinWhitt_Tightness_Model
-- name    : JSQHalfinWhitt_Tightness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:14.06557+00:00
-- url     : https://prove2.me/theorems/eab83c86-ed58-48a1-9d94-c6f6b245299d
-- title:
--   The join-the-shortest-queue chain: state space $S$, generator $G_Q$, Halfin–Whitt rate $\lambda = 1-\beta/\sqrt n$, fluid coordinates
-- statement:
--   The **join-the-shortest-queue (JSQ) system** has $n$ identical servers, each with its own infinite buffer. Customers arrive as a Poisson process of rate $n\lambda$ and service times are i.i.d. exponential with mean $1$. An arriving customer joins a server with the fewest customers (ties broken arbitrarily). For $i \ge 1$ let $Q_i$ be the number of servers with at least $i$ customers.
--
--   **State space.** The chain $Q = (Q_1, Q_2, \dots)$ lives on
--   $$S = \Big\{ q \in \{0, 1, \dots, n\}^{\infty} \ \Big|\ q_i \ge q_{i+1} \text{ for } i \ge 1,\ \sum_{i \ge 1} q_i < \infty \Big\}.$$
--   For a nonincreasing sequence of natural numbers, $\sum_i q_i < \infty$ means that $q_i = 0$ for all large $i$.
--
--   **Transitions.** Write $e^{(i)}$ for the $i$-th unit vector. An arrival joins a server with exactly $i-1$ customers, moving $q$ to $q + e^{(i)}$, exactly when $q_1 = \dots = q_{i-1} = n$ and $q_i < n$ (for $i = 1$: when $q_1 < n$). A departure from a server with exactly $i$ customers moves $q$ to $q - e^{(i)}$ at rate $q_i - q_{i+1}$. The generator acts on $f : S \to \mathbb R$ by
--   $$G_Q f(q) = \sum_{i \ge 1} n\lambda\, 1(q_1 = \dots = q_{i-1} = n,\ q_i < n)\big(f(q + e^{(i)}) - f(q)\big) + \sum_{i \ge 1} (q_i - q_{i+1})\big(f(q - e^{(i)}) - f(q)\big).$$
--   For $q \in S$ each sum has finitely many nonzero terms, and every state reached with positive rate is again in $S$.
--
--   **Halfin–Whitt regime.** The arrival rate per server is $\lambda = 1 - \beta/\sqrt n$ with $\beta > 0$ (1.1).
--
--   **Fluid coordinates.** A state $q$ has fluid-scaled coordinates $x = (x_1, x_2) = \big((q_1 - n)/n,\ q_2/n\big)$.
--
--   **Formalization Note** States are functions `ℕ → ℕ` with 0-based indices: the Lean value `q.1 i` is the paper's $q_{i+1}$. So `q.1 0` is $Q_1$, `q.1 1` is $Q_2$, and Theorem 2's "$i \ge 3$" is Lean index $i \ge 2$. The successor states `up q i` and `down q i` are $q + e^{(i+1)}$ and $q - e^{(i+1)}$ when the corresponding transition has positive rate, and $q$ otherwise (the term then vanishes). The two small lemmas `up_mem` and `down_mem` only check that these successor states lie in $S$. The parameter $\lambda$ (`lam`) is free in `genQ`; the Halfin–Whitt value is `lamHW β n`.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 1 (model, (1.1)), p. 5 (state space S, fluid scaling X), p. 6 (generator G_Q), p. 7 (x_1 = (q_1 − n)/n, x_i = q_i/n)

import Mathlib

namespace JSQHalfinWhitt.Tightness

open scoped Classical

/-- The state space `S = {q ∈ {0, 1, …, n}^∞ | q_i ≥ q_{i+1}, ∑_i q_i < ∞}` of the
join-the-shortest-queue chain with `n` servers (Braverman, p. 5). Indices are 0-based: the Lean
value `q.1 i` is the paper's `q_{i+1}`, the number of servers with at least `i + 1` customers.
For a nonincreasing sequence of natural numbers, `∑_i q_i < ∞` is the same as `q_i = 0` for all
large `i`. -/
def State (n : ℕ) : Type :=
  {q : ℕ → ℕ // (∀ i, q i ≤ n) ∧ Antitone q ∧ ∃ N, ∀ i, N ≤ i → q i = 0}

/-- The arrival condition at (0-based) index `i`: `q_0 = … = q_{i-1} = n` and `q_i < n`
(paper: `q_1 = … = q_i = n`, `q_{i+1} < n`), i.e. an arriving customer joins a server that has
exactly `i` customers, increasing the paper's `q_{i+1}` by one. -/
def ArrivesAt {n : ℕ} (q : State n) (i : ℕ) : Prop :=
  (∀ j, j < i → q.1 j = n) ∧ q.1 i < n

theorem up_mem {n : ℕ} (q : State n) (i : ℕ) (h : ArrivesAt q i) :
    (∀ k, Function.update q.1 i (q.1 i + 1) k ≤ n) ∧ Antitone (Function.update q.1 i (q.1 i + 1)) ∧
      ∃ N, ∀ k, N ≤ k → Function.update q.1 i (q.1 i + 1) k = 0 := by
  obtain ⟨hle, hanti, N, hN⟩ := q.2
  obtain ⟨hpre, hlt⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rcases eq_or_ne k i with rfl | hk
    · simp; omega
    · simp [Function.update_of_ne hk, hle k]
  · intro a b hab
    rcases eq_or_ne a i with rfl | ha <;> rcases eq_or_ne b a with rfl | hb
    · exact le_rfl
    · have : b ≠ a := hb
      simp [Function.update_of_ne this]
      have := hanti hab; omega
    · simp
    · simp only [Function.update_of_ne ha]
      rcases eq_or_ne b i with rfl | hbi
      · simp
        have hlt' : a < b := lt_of_le_of_ne hab (Ne.symm hb)
        have := hpre a hlt'; omega
      · simp [Function.update_of_ne hbi]; exact hanti hab
  · refine ⟨max N (i + 1), fun k hk => ?_⟩
    have hki : k ≠ i := by omega
    simp [Function.update_of_ne hki, hN k (le_of_max_le_left hk)]

theorem down_mem {n : ℕ} (q : State n) (i : ℕ) (h : q.1 (i + 1) < q.1 i) :
    (∀ k, Function.update q.1 i (q.1 i - 1) k ≤ n) ∧ Antitone (Function.update q.1 i (q.1 i - 1)) ∧
      ∃ N, ∀ k, N ≤ k → Function.update q.1 i (q.1 i - 1) k = 0 := by
  obtain ⟨hle, hanti, N, hN⟩ := q.2
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rcases eq_or_ne k i with rfl | hk
    · simp; have := hle k; omega
    · simp [Function.update_of_ne hk, hle k]
  · intro a b hab
    rcases eq_or_ne a i with rfl | ha <;> rcases eq_or_ne b a with rfl | hb
    · exact le_rfl
    · have hlt' : a + 1 ≤ b := by omega
      simp [Function.update_of_ne hb]
      have := hanti hlt'; omega
    · simp
    · simp only [Function.update_of_ne ha]
      rcases eq_or_ne b i with rfl | hbi
      · simp
        have := hanti hab; omega
      · simp [Function.update_of_ne hbi]; exact hanti hab
  · refine ⟨N, fun k hk => ?_⟩
    rcases eq_or_ne k i with rfl | hki
    · simp [hN k hk]
    · simp [Function.update_of_ne hki, hN k hk]

/-- The state after an arrival that joins a server with exactly `i` customers:
`q + e^{(i+1)}` in the paper's 1-based notation, when the arrival condition holds
(otherwise `q` itself; that transition then has rate `0`). -/
noncomputable def up {n : ℕ} (q : State n) (i : ℕ) : State n :=
  if h : ArrivesAt q i then ⟨Function.update q.1 i (q.1 i + 1), up_mem q i h⟩ else q

/-- The state after a departure from a server with exactly `i + 1` customers:
`q − e^{(i+1)}` in the paper's notation, when `q_{i+1} > q_{i+2}` (paper indices; otherwise `q`
itself, and that transition has rate `0`). -/
noncomputable def down {n : ℕ} (q : State n) (i : ℕ) : State n :=
  if h : q.1 (i + 1) < q.1 i then ⟨Function.update q.1 i (q.1 i - 1), down_mem q i h⟩ else q

/-- The generator `G_Q` of the join-the-shortest-queue chain with `n` servers, arrival rate
`n λ` and unit service rates (Braverman, p. 6):
`G_Q f(q) = ∑_{i ≥ 1} nλ 1(q_1 = … = q_{i−1} = n, q_i < n)(f(q + e^{(i)}) − f(q))
          + ∑_{i ≥ 1} (q_i − q_{i+1})(f(q − e^{(i)}) − f(q))`
(paper indices; the `i = 1` arrival term is `nλ 1(q_1 < n)`). For `q ∈ S` both sums have finitely
many nonzero terms. In Lean the summation index is 0-based. -/
noncomputable def genQ (n : ℕ) (lam : ℝ) (f : State n → ℝ) (q : State n) : ℝ :=
  (∑' i : ℕ, (if ArrivesAt q i then (n : ℝ) * lam else 0) * (f (up q i) - f q)) +
    ∑' i : ℕ, ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) * (f (down q i) - f q)

/-- The Halfin–Whitt arrival rate per server (1.1): `λ = 1 − β/√n`. -/
noncomputable def lamHW (β : ℝ) (n : ℕ) : ℝ :=
  1 - β / Real.sqrt n

/-- The fluid-scaled coordinates `(x_1, x_2) = ((q_1 − n)/n, q_2/n)` of a state (paper indices;
Lean `q.1 0` and `q.1 1`). -/
noncomputable def xOf {n : ℕ} (q : State n) : ℝ × ℝ :=
  (((q.1 0 : ℝ) - n) / n, (q.1 1 : ℝ) / n)

end JSQHalfinWhitt.Tightness


