-- Prove2me | Definitions.Def_ServiceParts_Allocation_AllocData
-- name    : ServiceParts_Allocation_AllocData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T22:48:28.335445+00:00
-- url     : https://prove2.me/theorems/2308ba36-cf48-4822-9493-c07bc0273b81
-- title:
--   Allocation optimization data: gridpoints, convex function values, slopes (7.19) and piecewise linear interpolants (7.20)–(7.21)
-- statement:
--   This definition sets up the data of the allocation optimization of Muckstadt, Section 7.4.
--
--   There is a set $M = \{1, 2, \dots, \bar M\}$ of locations and an augmented set $M_0 = \{0\} \cup M$ with one location at a higher level. Each location $m \in M_0$ has integer **gridpoints**
--   $$0 = r^m_0 < r^m_1 < \cdots < r^m_{n(m)},$$
--   indexed by $N_m = \{0, 1, \dots, n(m)\}$. At each gridpoint $r^m_n$ of a location $m \in M$ a value $c^m_n$ of a convex function is given. A convex function $f$ on $\mathbb R_+$ is also given.
--
--   The standing assumptions (the predicate `WellFormed`) are:
--
--   1. $M$ is nonempty ($\bar M \ge 1$) and every $m \in M$ has $n(m) \ge 1$;
--   2. $r^m_0 = 0$ and $r^m_n > r^m_{n-1}$ for $0 < n \le n(m)$, for every $m \in M_0$;
--   3. for every $m \in M$ there is a function $\varphi_m$, convex on $[0, \infty)$, with $c^m_n = \varphi_m(r^m_n)$ for all $n \in N_m$;
--   4. $f$ is convex on $[0, \infty)$.
--
--   The **slopes** (7.19) are
--   $$\hat c^m_n = \begin{cases} \dfrac{c^m_{n+1} - c^m_n}{r^m_{n+1} - r^m_n}, & n < n(m),\\[2mm] \dfrac{c^m_n - c^m_{n-1}}{r^m_n - r^m_{n-1}}, & n = n(m),\end{cases}$$
--   and the **piecewise linear approximation** (7.20)–(7.21) of location $m \in M$ is
--   $$\tilde C_m(r) = c^m_0 + \sum_{n=0}^{n(m)-1} \mathbf 1_{\{r \ge r^m_n\}} \bigl(r \wedge r^m_{n+1} - r^m_n\bigr)\, \hat c^m_n + \mathbf 1_{\{r \ge r^m_{n(m)}\}} \bigl(r - r^m_{n(m)}\bigr)\, \hat c^m_{n(m)}.$$
--
--   These are the objects of the allocation problem (7.22) and of algorithm AllocOpt (Definition 4).
--
--   **Formalization Note** The locations of $M$ are indexed by `Fin Mbar` (book location $i+1$ is index $i$); location $0$ is stored separately (`n0`, `grid0`). Gridpoints are integers (`ℤ`), function values and slopes are reals. The requirement $n(m) \ge 1$ is implicit in the book: the slope (7.19) at $n = n(m)$ needs a previous gridpoint. For indices $n > n(m)$, outside the book's range, `slope` returns the last backward slope; no statement uses those indices.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 177-178, Section 7.4, Eqs. (7.19)-(7.21) and the data of (7.22)

import Mathlib

namespace ServiceParts.Allocation

/-- Data of the allocation optimization of Muckstadt (2005), Section 7.4, pp. 177–178.
The locations `M = {1, …, M̄}` are indexed by `Fin Mbar` (the book's location `i + 1` is
`i : Fin Mbar`); the higher-level location `0` is kept separately.

* `n m` is `n(m)`, and `grid m k`, `k = 0, …, n(m)`, are the integer gridpoints `r^m_k`;
* `cost m k` is the function evaluation `c^m_k` at the gridpoint `r^m_k`;
* `n0` is `n(0)` and `grid0 k`, `k = 0, …, n(0)`, are the gridpoints `r^0_k` of location `0`,
  at which the values `c^0_k` of (7.22) are to be computed;
* `f` is the convex function `f` on `ℝ⁺` added in (7.22).

Values of `grid`, `cost`, `grid0` at indices beyond `n(m)` (resp. `n(0)`) are never used. -/
structure AllocData (Mbar : ℕ) where
  /-- `n(m)`: the last gridpoint index of location `m` -/
  n : Fin Mbar → ℕ
  /-- the integer gridpoints `r^m_k` -/
  grid : Fin Mbar → ℕ → ℤ
  /-- the function evaluations `c^m_k` at the gridpoints -/
  cost : Fin Mbar → ℕ → ℝ
  /-- `n(0)`: the last gridpoint index of location `0` -/
  n0 : ℕ
  /-- the integer gridpoints `r^0_k` of location `0` -/
  grid0 : ℕ → ℤ
  /-- the convex function `f` on `ℝ⁺` -/
  f : ℝ → ℝ

namespace AllocData

variable {Mbar : ℕ} (d : AllocData Mbar)

/-- The standing assumptions of Section 7.4, pp. 177–178: `M` is nonempty; every location
`m ∈ M` has at least two gridpoints (`n(m) ≥ 1`, needed for the slopes (7.19)); gridpoints
start at `0` and are strictly increasing, at every location of `M₀ = {0} ∪ M`; each `c^m_k` is
the value at `r^m_k` of a convex function on `ℝ⁺`; `f` is convex on `ℝ⁺`. -/
structure WellFormed : Prop where
  Mbar_pos : 0 < Mbar
  n_pos : ∀ m, 1 ≤ d.n m
  grid_zero : ∀ m, d.grid m 0 = 0
  grid_strictMono : ∀ m k, k < d.n m → d.grid m k < d.grid m (k + 1)
  grid0_zero : d.grid0 0 = 0
  grid0_strictMono : ∀ k, k < d.n0 → d.grid0 k < d.grid0 (k + 1)
  cost_convex : ∀ m, ∃ φ : ℝ → ℝ, ConvexOn ℝ (Set.Ici 0) φ ∧
    ∀ k, k ≤ d.n m → d.cost m k = φ (d.grid m k)
  f_convex : ConvexOn ℝ (Set.Ici 0) d.f

/-- The slopes `ĉ^m_k` of (7.19): the forward difference quotient for `k < n(m)`, and for
`k = n(m)` the backward one, `(c^m_{n(m)} - c^m_{n(m)-1}) / (r^m_{n(m)} - r^m_{n(m)-1})`.
(For `k > n(m)`, outside the book's range, the value is also the last backward slope.) -/
noncomputable def slope (m : Fin Mbar) (k : ℕ) : ℝ :=
  if k < d.n m then
    (d.cost m (k + 1) - d.cost m k) / ((d.grid m (k + 1) : ℝ) - d.grid m k)
  else
    (d.cost m (d.n m) - d.cost m (d.n m - 1)) /
      ((d.grid m (d.n m) : ℝ) - d.grid m (d.n m - 1))

/-- The piecewise linear approximation `Ĉ_m(r)` of (7.20)–(7.21):
`Ĉ_m(r) = c^m_0 + Σ_{k=0}^{n(m)-1} 1{r ≥ r^m_k} (r ∧ r^m_{k+1} - r^m_k) ĉ^m_k
  + 1{r ≥ r^m_{n(m)}} (r - r^m_{n(m)}) ĉ^m_{n(m)}`. -/
noncomputable def pwl (m : Fin Mbar) (r : ℝ) : ℝ :=
  d.cost m 0
    + (∑ k ∈ Finset.range (d.n m),
        if (d.grid m k : ℝ) ≤ r then (min r (d.grid m (k + 1) : ℝ) - d.grid m k) * d.slope m k
        else 0)
    + (if (d.grid m (d.n m) : ℝ) ≤ r then (r - d.grid m (d.n m)) * d.slope m (d.n m) else 0)

end AllocData

end ServiceParts.Allocation


