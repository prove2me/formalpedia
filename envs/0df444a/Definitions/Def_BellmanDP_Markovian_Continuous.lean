-- Prove2me | Definitions.Def_BellmanDP_Markovian_Continuous
-- name    : BellmanDP_Markovian_Continuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T21:35:30.182565+00:00
-- url     : https://prove2.me/theorems/ff4d376b-5858-46b2-9e71-88b59e969490
-- title:
--   Row-wise maximized and max-min differential equations $dx/dt=\max_q[A(q,t)x+b(q,t)]$ and their successive approximations
-- statement:
--   This file sets up the continuous-time processes of Chapter XI, §§ 4, 5 and 12. Vectors $x \in \mathbb R^N$ have components $x_1, \dots, x_N$, and row $i$ carries its own parameter set (the maximization is element by element, § 3).
--
--   1. Row $i$ of $A(q,t)x + b(q,t)$: $\sum_{j=1}^N a_{ij}(q_i, t)\, x_j + b_i(q_i, t)$.
--   2. The right-hand side $F(t,x) = \max_q [A(q,t)x + b(q,t)]$: $F$ is the row-wise maximum when, for every $t$, $x$ and $i$, the maximum over $q_i \in S_i$ of row $i$ is attained and equals $F_i(t,x)$.
--   3. The two-person right-hand side of § 12: row $i$ of $A(p,q,t)x + b(p,q,t)$, and $V(t,x)$ is the row-wise **saddle value** when for every $t$, $x$, $i$ there are admissible $\hat p, \hat q$ with
--   $$g_i(p, \hat q) \le V_i(t,x) \le g_i(\hat p, q) \quad \text{for all admissible } p, q,$$
--   $g_i$ being row $i$'s payoff; equivalently $\max_p \min_q g_i = \min_q \max_p g_i = V_i(t,x)$, both extrema attained.
--   4. A **solution on $[0,T]$** of $dx/dt = F(t,x)$, $x(0) = c$, in the sense of "satisfying the equation almost everywhere" (Eqs. (4.2), (5.10)): $x$ is continuous on $[0,T]$, $s \mapsto F(s, x(s))$ is integrable on $[0,T]$, and
--   $$x(t) = c + \int_0^t F(s, x(s))\, ds, \qquad 0 \le t \le T .$$
--   5. The **successive approximations** (5.3), (12.3): $x_0(t) = c$, $x_{n+1}(t) = c + \int_0^t F(s, x_n(s))\, ds$.
--
--   **Formalization Note** The book writes (5.3) with the maximum over the admissible functions $q(\cdot)$ outside the integral and notes (§ 4) that "since $q$ is a function of $t$, pointwise maximization yields global maximization"; the definition uses the integral of the pointwise maximum, which is the book's (4.2) and (5.10).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, § 3, Eq. (3.4), p. 320; § 4, Eqs. (4.1)-(4.3), p. 320; § 5, Theorem 1 and Eqs. (5.3), (5.10), pp. 321, 323; § 12, Theorem 4, Eqs. (12.1)-(12.3), p. 332

import Mathlib

namespace BellmanDP.Markovian

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. XI, § 5, (5.1), p. 321: row `i` of
`A(q, t) x + b(q, t)`, namely `Σ_{j=1}^N a_ij(q, t) x_j + b_i(q, t)`, where row `i` depends only
on its own parameter `q : Q i` (§ 3, (3.4), p. 320: the maximization is element by element). -/
def rowAffine {N : ℕ} {Q : Fin N → Type*} (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ)
    (b : (i : Fin N) → Q i → ℝ → ℝ) (i : Fin N) (q : Q i) (t : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ j, A i q t j * x j + b i q t

/-- Ch. XI, § 5, Theorem 1, p. 321: `F(t, x) = Max_q [A(q, t) x + b(q, t)]`, taken row by row,
with the maximum over `S i` attained ("the maximum of `A(q, t) x + b(q, t)` is attained for
`q ∈ S` for any fixed `t` and `x` values"). -/
def IsRowwiseMax {N : ℕ} {Q : Fin N → Type*} (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ)
    (b : (i : Fin N) → Q i → ℝ → ℝ) (S : (i : Fin N) → Set (Q i))
    (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ (t : ℝ) (x : Fin N → ℝ) (i : Fin N),
    IsGreatest ((fun q => rowAffine A b i q t x) '' S i) (F t x i)

/-- Ch. XI, § 12, (12.1), p. 332: row `i` of `A(p, q, t) x + b(p, q, t)` in the two-person
version, `Σ_{j=1}^N a_ij(p, q, t) x_j + b_i(p, q, t)`. -/
def rowAffine2 {N : ℕ} {P Q : Fin N → Type*} (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ)
    (b : (i : Fin N) → P i → Q i → ℝ → ℝ) (i : Fin N) (p : P i) (q : Q i) (t : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∑ j, A i p q t j * x j + b i p q t

/-- Ch. XI, § 12, Theorem 4, condition (2a), p. 332: `V(t, x)` is, row by row, the common value
`Max_p Min_q [A(p, q, t) x + b(p, q, t)] = Min_q Max_p […]`, both extrema attained: there are
`p̂ ∈ SP i`, `q̂ ∈ SQ i` with `g(p, q̂) ≤ V ≤ g(p̂, q)` for all admissible `p`, `q` (a saddle
point of row `i`'s payoff `g`). -/
def IsRowwiseSaddleValue {N : ℕ} {P Q : Fin N → Type*}
    (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → P i → Q i → ℝ → ℝ)
    (SP : (i : Fin N) → Set (P i)) (SQ : (i : Fin N) → Set (Q i))
    (V : ℝ → (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ (t : ℝ) (x : Fin N → ℝ) (i : Fin N), ∃ p₀ ∈ SP i, ∃ q₀ ∈ SQ i,
    (∀ p ∈ SP i, rowAffine2 A b i p q₀ t x ≤ V t x i) ∧
    (∀ q ∈ SQ i, V t x i ≤ rowAffine2 A b i p₀ q t x)

/-- Ch. XI, § 4, (4.2), and § 5, (5.10), pp. 320, 323: `x` is a solution of `dx/dt = F(t, x)`,
`x(0) = c`, on `[0, T]` "satisfying the equation almost everywhere": `x` is continuous on
`[0, T]`, `s ↦ F(s, x(s))` is integrable on `[0, T]`, and
`x(t) = c + ∫_0^t F(s, x(s)) ds` for `0 ≤ t ≤ T`. -/
def IsIntegralSolutionOn {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (c : Fin N → ℝ) (T : ℝ)
    (x : ℝ → Fin N → ℝ) : Prop :=
  ContinuousOn x (Set.Icc 0 T) ∧ IntegrableOn (fun s => F s (x s)) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T, x t = c + ∫ s in (0 : ℝ)..t, F s (x s)

/-- Ch. XI, § 5, (5.3), p. 321, and § 12, (12.3), p. 332: the successive approximations
`x₀ = c`, `x_{n+1}(t) = c + ∫_0^t F(s, x_n(s)) ds`. -/
noncomputable def picardIter {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (c : Fin N → ℝ) :
    ℕ → ℝ → Fin N → ℝ
  | 0 => fun _ => c
  | n + 1 => fun t => c + ∫ s in (0 : ℝ)..t, F s (picardIter F c n s)

end BellmanDP.Markovian


