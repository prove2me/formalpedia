-- Prove2me | Definitions.Def_HochbaumShmoys_Uniform_Rounding
-- name    : HochbaumShmoys_Uniform_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:39.156841+00:00
-- url     : https://prove2.me/theorems/f05adef7-ad12-4662-9b91-463ac8bd6e66
-- title:
--   Geometric intervals and the rounding $\bar p_j=\lfloor p_j/\delta^{k+2}\rfloor\,\delta^{k+2}$ (§3, p. 543)
-- statement:
--   Fix an integer $N\ge2$ and the parameter $\delta=1/N$ (the paper's $\varepsilon$ in §3, assumed there to have $1/\varepsilon$ a positive integer). Sizes are normalized to lie in $(0,1]$.
--
--   1. The **interval index** of a size $x$ is the least $q\ge0$ with $\delta^{q+1}<x$; for $0<x\le1$ it equals $k=\max\{q\ge0: x\le\delta^q\}$, and $x$ lies in **interval $k$**, namely $(\delta^{k+1},\delta^k]$.
--   2. The **rounded size** of $x$ in interval $k$ is
--   $$\bar x=\Big\lfloor \frac{x}{\delta^{k+2}}\Big\rfloor\,\delta^{k+2}.$$
--   3. The **rounding class** of $x$ is $c=\lfloor x/\delta^{k+2}\rfloor-N$, so that $\bar x=(N+c)\,\delta^{k+2}$. For $0<x\le 1$ the class is one of $0,1,\dots,N^2-N$: there are $w+1$ rounded values per interval, where $w=(1-\delta)/\delta^2=N^2-N$.
--   4. The **class size** of class $c$ in interval $k$ is $(N+c)\,\delta^{k+2}$, the lower end of the $c$-th subinterval of length $\delta^{k+2}$ of $(\delta^{k+1},\delta^k]$.
--
--   The rounding turns the piece sizes into finitely many classes per interval, which is what makes the layered graph of all-pack polynomial in size.
--
--   **Formalization Note** The paper's state vectors have $w$ entries indexed by the lower ends $l_1,\dots,l_w$ of the subintervals, but the floor in the displayed formula also produces the value $\delta^k$ itself (for instance a piece equal to the largest bin): $w+1$ values. The formalization keeps the displayed formula and uses $w+1$ classes (finding F4). The interval index is defined by the least $q$ with $\delta^{q+1}<x$, which agrees with the paper's maximum on $(0,1]$ and is total on all reals.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 543, §3 (definition of p̄_j and k), p. 544 (subintervals, w = (1 − ε)/ε²)

import Mathlib

namespace HochbaumShmoys.Uniform

/-- The interval index of a size `x` for the parameter `δ = 1/N`: the least `q` with
`δ^(q+1) < x`. For `0 < x ≤ 1` and `N ≥ 2` this is `k = max {q ≥ 0 | x ≤ δ^q}`, i.e. `x` lies in
interval `k`, which is `(δ^(k+1), δ^k]`. -/
noncomputable def intervalIndex (N : ℕ) (x : ℝ) : ℕ :=
  sInf {q : ℕ | ((N : ℝ)⁻¹) ^ (q + 1) < x}

/-- The rounded size `x̄ = ⌊x / δ^(k+2)⌋ · δ^(k+2)` where `k` is the interval index of `x` and
`δ = 1/N`. -/
noncomputable def roundDown (N : ℕ) (x : ℝ) : ℝ :=
  (⌊x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)⌋ : ℝ) * ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)

/-- The rounding class of `x`: `x̄ = (N + c) · δ^(k+2)` with `c = ⌊x / δ^(k+2)⌋ − N`. For
`0 < x ≤ 1` the class lies in `{0, 1, …, N² − N}`, so there are `w + 1` classes per interval,
`w = (1 − δ)/δ² = N² − N`. -/
noncomputable def roundClass (N : ℕ) (x : ℝ) : ℕ :=
  ⌊x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)⌋₊ - N

/-- The rounded size `(N + c) · δ^(k+2)` of class `c` in interval `k`, i.e. the lower end of the
`c`-th subinterval of length `δ^(k+2)` of `(δ^(k+1), δ^k]`. -/
noncomputable def classSize (N k c : ℕ) : ℝ :=
  ((N : ℝ) + c) * ((N : ℝ)⁻¹) ^ (k + 2)

end HochbaumShmoys.Uniform


