-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_TimeGrid
-- name    : BorkarMeynODE_Tapering_TimeGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:38:54.650086+00:00
-- url     : https://prove2.me/theorems/eb0f963d-88a6-45cc-a0f6-6ad65e2c8cda
-- title:
--   ODE time grid $t(n)$, blocks $m(j)$, $T(j)$, and piecewise-linear interpolation
-- statement:
--   Let $\{a(n)\}$ be positive step sizes with $\sum_n a(n)=\infty$ and fix $T>0$. The **ODE time scale** is
--   $$
--   t(0)=0, \qquad t(n) = \sum_{i=0}^{n-1} a(i), \quad n\ge1 .
--   $$
--   The **blocks** are defined inductively by $T(0)=0$ and
--   $$
--   T(j+1) = \min\{\, t(k) : t(k) > T(j) + T \,\}, \qquad j\ge0 ,
--   $$
--   so that $T(j) = t(m(j))$ with $m(0)=0$ and $m(j+1)$ the least $k$ with $t(k)>t(m(j))+T$.
--
--   For $t\ge0$ the file also names the block containing $t$ (the $j$ with $T(j)\le t<T(j+1)$), the block containing an iteration index $n$ (the $j$ with $m(j)\le n<m(j+1)$), and the grid cell containing $t$ (the $n$ with $t(n)\le t<t(n+1)$). The **piecewise-linear interpolation** of a sequence $\{y(n)\}$ on the grid is
--   $$
--   \bar y(t) = y(n) + \frac{t-t(n)}{a(n)}\big(y(n+1)-y(n)\big), \qquad t(n)\le t\le t(n+1),
--   $$
--   so that $\bar y(t(n)) = y(n)$.
--
--   These objects set up the comparison between the discrete recursion and ODE solutions that is used in the proofs of Theorems 2.1 and 2.2.
--
--   **Formalization Note** $m(j+1)$ is an `sInf` over $\mathbb N$ and the cell and block indices are `sSup`s over $\mathbb N$. They take Lean's junk value $0$ when the underlying set is empty or unbounded, which can happen only when $\sum_n a(n)<\infty$ or $T\le0$. Every statement that uses them assumes (TS) or (BS) and $T>0$, under which $t(n)$ and $T(j)$ increase strictly to $\infty$ and all indices are well defined.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 450 (proof of Theorem 2.2: t(n), T(n), m(n) and the linear interpolation psi)

import Mathlib

namespace BorkarMeynODE.Tapering

/-- The ODE time scale of the step sizes (p. 450): `t(0) = 0` and
`t(n) = ∑_{i=0}^{n-1} a(i)` for `n ≥ 1`. -/
def timeGrid (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

/-- The block indices `m(j)` (p. 450): `m(0) = 0` and `m(j+1)` is the least `k` with
`t(k) > t(m(j)) + T`, so that `T(j+1) = t(m(j+1)) = min {t(k) : t(k) > T(j) + T}`.
If no such `k` exists (possible only when `∑ a(n) < ∞`) Lean's `sInf ∅ = 0` is returned;
every statement using the blocks assumes (TS) or (BS), under which `∑ a(n) = ∞`. -/
noncomputable def blockIndex (a : ℕ → ℝ) (T : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sInf {k : ℕ | timeGrid a (blockIndex a T j) + T < timeGrid a k}

/-- The block start times `T(j) = t(m(j))` (p. 450). -/
noncomputable def blockTime (a : ℕ → ℝ) (T : ℝ) (j : ℕ) : ℝ :=
  timeGrid a (blockIndex a T j)

/-- For `t ≥ 0`, the index `j` of the block with `T(j) ≤ t < T(j+1)`: the largest `j` with
`T(j) ≤ t`. (Under (TS) or (BS) and `T > 0` the block times increase strictly to `∞`, so the
set is finite and nonempty; otherwise Lean's `sSup` returns `0`.) -/
noncomputable def blockOfTime (a : ℕ → ℝ) (T : ℝ) (t : ℝ) : ℕ :=
  sSup {j : ℕ | blockTime a T j ≤ t}

/-- For an iteration index `n`, the index `j` of the block with `m(j) ≤ n < m(j+1)`: the
largest `j` with `m(j) ≤ n` (well defined under (TS) or (BS) with `T > 0`). -/
noncomputable def blockOfIndex (a : ℕ → ℝ) (T : ℝ) (n : ℕ) : ℕ :=
  sSup {j : ℕ | blockIndex a T j ≤ n}

/-- For `t ≥ 0`, the index `n` with `t(n) ≤ t < t(n+1)`: the largest `n` with `t(n) ≤ t`
(well defined when `∑ a(n) = ∞` and `a > 0`). -/
noncomputable def gridIndex (a : ℕ → ℝ) (t : ℝ) : ℕ :=
  sSup {n : ℕ | timeGrid a n ≤ t}

/-- Piecewise-linear interpolation of a sequence `y` on the grid `t(n)`: for
`t(n) ≤ t ≤ t(n+1)`, `y(n) + ((t − t(n))/a(n)) (y(n+1) − y(n))`, so that the value at `t(n)` is
`y(n)` (p. 450, (a); p. 460, (a)). -/
noncomputable def gridInterp {d : ℕ} (a : ℕ → ℝ) (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  y (gridIndex a t) + ((t - timeGrid a (gridIndex a t)) / a (gridIndex a t)) •
    (y (gridIndex a t + 1) - y (gridIndex a t))

end BorkarMeynODE.Tapering


