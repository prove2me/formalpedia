-- Prove2me | Definitions.Def_MatrixAnalytic_BirthDeath_Passage
-- name    : MatrixAnalytic_BirthDeath_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:00.192911+00:00
-- url     : https://prove2.me/theorems/fd18bbe2-c03b-4551-a965-6a522770449a
-- title:
--   Taboo probabilities ₙP_ij(k), passage densities g_n, r_n, u_n, the quantities G_n, U_n, R_n and their generating functions
-- statement:
--   Let $P$ be a transition matrix on $\{0,1,2,\dots\}$ and $(X_k)$ the Markov chain it governs.
--
--   1. The **taboo probability** ${}_nP_{ij}(k) = \mathrm P[X_k=j,\ X_1>n,\dots,X_{k-1}>n \mid X_0=i]$ is the probability that the chain started in $i$ is in $j$ at time $k$ without visiting any state of $\{0,\dots,n\}$ at times $1,\dots,k-1$. It is the sum, over all trajectories $\omega_0=i,\omega_1,\dots,\omega_k=j$ whose intermediate states all exceed $n$, of $\prod_{m<k}P(\omega_m,\omega_{m+1})$.
--   2. For $n\ge1$ and $k\ge1$: $g_n(k)={}_{n-1}P_{n,n-1}(k)$, the probability that the chain started in $n$ makes its first visit to $n-1$ at time $k$; $r_n(k)={}_{n-1}P_{n-1,n}(k)$, the probability that the chain started in $n-1$ is in $n$ at time $k$ and has not returned to $n-1$ in between; and $u_n(k)={}_nP_{n,n}(k)$, the probability of returning to $n$ for the first time at time $k$, starting from $n$, while avoiding $n-1$.
--   3. $G_n=\sum_{k\ge1}g_n(k)$ is the probability that, starting from $n$, the chain reaches $n-1$ in a finite time; $U_n=\sum_{k\ge1}u_n(k)$ is the probability of returning to $n$, starting from $n$, before visiting $n-1$; $R_n=\sum_{k\ge1}r_n(k)$ is the expected number of visits to $n$ between two successive visits to $n-1$.
--   4. The generating functions, for complex $z$, are
--   $$G_n(z)=\sum_{k\ge1}z^kg_n(k),\qquad R_n(z)=\sum_{k\ge1}z^kr_n(k),\qquad U_n(z)=\sum_{k\ge1}z^ku_n(k),$$
--   so that $G_n=G_n(1)$, $R_n=R_n(1)$, $U_n=U_n(1)$.
--
--   **Formalization Note** All of these are defined probabilistically, as sums over finite taboo trajectories of products of one-step transition probabilities; none is defined as the solution of an equation. Infinite sums are `tsum`s. For a birth-and-death chain every one of them converges (the $g_n(k)$ and $u_n(k)$ are probabilities of disjoint events, $R_n = a_{n-1,n}(1-U_n)^{-1}$ is finite, and the power series converge for $|z|\le1$), so the `tsum` takes the true value. The indices $n-1$ use natural-number subtraction; the theorems use $g_n$, $r_n$, $G_n$, $R_n$, $G_n(z)$, $R_n(z)$ only for $n\ge1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 88 (taboo probabilities ₙP_ij(k)); pp. 89–90 (U_n, R_n, G_n); pp. 94–95 (g_n, r_n (4.16), u_n and the generating functions)

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain

namespace MatrixAnalytic.BirthDeath

open Classical in
/-- The taboo probability `ₙP_ij(k) = P[X_k = j, X_1 > n, …, X_{k-1} > n | X_0 = i]` (p. 88):
the sum, over trajectories `ω_0, …, ω_k` with `ω_0 = i`, `ω_k = j` and every intermediate state
`ω_1, …, ω_{k-1}` outside `{0, …, n}`, of the product of one-step transition probabilities. -/
noncomputable def tabooProb (P : ℕ → ℕ → ℝ) (n i j k : ℕ) : ℝ :=
  ∑' ω : Fin (k + 1) → ℕ,
    if ω 0 = i ∧ ω (Fin.last k) = j ∧
        (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → n < ω m)
    then pathWeightC P ω else 0

/-- `g_n(k) = ₙ₋₁P_{n,n-1}(k)` (p. 94): starting in `n`, the first visit to `n - 1` occurs at
time `k`. Used for `n ≥ 1` and `k ≥ 1`. -/
noncomputable def g (P : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := tabooProb P (n - 1) n (n - 1) k

/-- `r_n(k) = ₙ₋₁P_{n-1,n}(k)` (4.16): starting in `n - 1`, the chain is in `n` at time `k` and
has not returned to `n - 1` (nor gone below it) in between. Used for `n ≥ 1` and `k ≥ 1`. -/
noncomputable def r (P : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := tabooProb P (n - 1) (n - 1) n k

/-- `u_n(k) = ₙP_{n,n}(k)` (p. 94): starting in `n`, the first return to `n` occurs at time `k`,
avoiding `n - 1` (and every lower state) in between. Used for `k ≥ 1`. -/
noncomputable def u (P : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := tabooProb P n n n k

/-- `G_n = ∑_{k ≥ 1} g_n(k)`: the probability that, starting from `n`, the chain reaches `n - 1`
in a finite time (pp. 90, 95). -/
noncomputable def G (P : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∑' k : ℕ, g P n (k + 1)

/-- `U_n = ∑_{k ≥ 1} ₙP_{nn}(k)`: the probability of returning to `n`, starting from `n`, before
visiting `n - 1` (p. 89). -/
noncomputable def U (P : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∑' k : ℕ, u P n (k + 1)

/-- `R_n = ∑_{k ≥ 1} r_n(k)`: the expected number of visits to `n` between two successive visits
to `n - 1` (pp. 89, 94–95). -/
noncomputable def R (P : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∑' k : ℕ, r P n (k + 1)

/-- The generating function `G_n(z) = ∑_{k ≥ 1} z^k g_n(k)` (p. 95), for complex `z`. -/
noncomputable def Gz (P : ℕ → ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ (k + 1) * (g P n (k + 1) : ℂ)

/-- The generating function `R_n(z) = ∑_{k ≥ 1} z^k r_n(k)` (p. 95), for complex `z`. -/
noncomputable def Rz (P : ℕ → ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ (k + 1) * (r P n (k + 1) : ℂ)

/-- The generating function `U_n(z) = ∑_{k ≥ 1} z^k u_n(k)` (p. 95), for complex `z`. -/
noncomputable def Uz (P : ℕ → ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ (k + 1) * (u P n (k + 1) : ℂ)

end MatrixAnalytic.BirthDeath


