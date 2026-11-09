-- Prove2me | Definitions.Def_WalkTreeCluster_Params
-- name    : WalkTreeCluster_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:39:20.8498+00:00
-- url     : https://prove2.me/theorems/3f3a4239-f712-44bf-b23d-4142b31761ab
-- title:
--   The parameters of Table 1: $a,q,\alpha,\delta,B,H,t,c_0$ and the coefficients $d_s$
-- statement:
--   For $\epsilon>0$ and $0<\phi\le1$ the algorithm uses (Table 1)
--   $$a=(8\epsilon/\phi^2)^{1/1000},\quad q=\lceil 2000/a\rceil,\quad \alpha=q^2/10^6,\quad \delta=a^2,$$
--   $$B=\lceil 19200\log(6400\alpha^2)\rceil,\quad H=\max\{1,\lceil\log_\alpha n\rceil\},\quad t=\lceil 4000\phi^{-2}\log(1/a)\rceil,$$
--   and the constant $c_0=\tfrac18\min\{10^{-4},(128c_{\rm loc})^{-1/60}\}^{1000}$, a function of the constant $c_{\rm loc}$ of Lemma 8.3. The high-pass series of Eq. (10) has coefficients
--   $$d_s=\frac{\binom{2s}{s}}{4^s(2s-1)}\qquad(s\ge1),$$
--   which sum to $1$.
--
--   $q$ is the number of children per node of the walk tree, $\alpha^i$ the size scale of stage $i$, $\delta$ the discount probability of a walk block, $B$ the number of collision pairs per Keep call, $H$ the terminal depth and $t$ the walk length of a block.
--
--   **Formalization Note.** Table 1 writes $q=2000/a$ and $t=4000\phi^{-2}\log(1/a)$; as numbers of calls and of walk steps they are read as integer ceilings. With this $q$, Table 1's bound $\alpha\le5a^{-2}$ holds.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Table 1, p.18; Eq. (10), p.10

import Mathlib

namespace WalkTreeCluster

/-!
# The parameters of Table 1

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Table 1, p.18; Eq. (10), p.10.

`a = (8ϵ/ϕ²)^{1/1000}`, `q = ⌈2000/a⌉`, `α = q²/10⁶`, `δ = a²`, `B = ⌈19200 log(6400α²)⌉`,
`H = max{1, ⌈log_α n⌉}`, `t = ⌈4000 ϕ⁻² log(1/a)⌉`,
`c₀ = (1/8) min{10⁻⁴, (128 c_loc)^{−1/60}}^{1000}`, and the series coefficients
`d_s = C(2s, s) / (4^s (2s − 1))` of Eq. (10).

**Formalization Note.**
* Table 1 writes `q = 2000/a` and `t = 4000ϕ⁻² log(1/a)`, but `q` is a number of calls to Child and
  `t` a number of walk steps, so both are read as the integer ceilings `⌈2000/a⌉` and
  `⌈4000ϕ⁻² log(1/a)⌉`. With this `q`, Table 1's bound `α = q²/10⁶ ≤ 5a⁻²` holds (it is `4a⁻²`
  without rounding).
* `H` uses `log_α n = log n / log α` (`Real.logb`) and its integer ceiling.
* All powers with real exponents are `Real.rpow` of positive bases on the parameter range.
* `seriesCoeff s` is `d_s`; it is only used for `s ≥ 1`.
-/

/-- `a = (8ϵ/ϕ²)^{1/1000}` (Table 1). -/
noncomputable def aParam (ϵ ϕ : ℝ) : ℝ := (8 * ϵ / ϕ ^ 2) ^ (1 / 1000 : ℝ)

/-- `q = ⌈2000/a⌉`, the number of calls to Child per node of the walk tree (Table 1). -/
noncomputable def qParam (ϵ ϕ : ℝ) : ℕ := ⌈2000 / aParam ϵ ϕ⌉₊

/-- `α = q²/10⁶`, the size scale (Table 1). -/
noncomputable def alphaParam (ϵ ϕ : ℝ) : ℝ := (qParam ϵ ϕ : ℝ) ^ 2 / 10 ^ 6

/-- `δ = a²`, the discounting probability (Table 1). -/
noncomputable def deltaParam (ϵ ϕ : ℝ) : ℝ := aParam ϵ ϕ ^ 2

/-- `B = ⌈19200 log(6400α²)⌉`, the number of independent tree pairs per Keep call (Table 1). -/
noncomputable def BParam (ϵ ϕ : ℝ) : ℕ := ⌈19200 * Real.log (6400 * alphaParam ϵ ϕ ^ 2)⌉₊

/-- `H = max{1, ⌈log_α n⌉}`, the terminal depth (Table 1). -/
noncomputable def HParam (ϵ ϕ : ℝ) (n : ℕ) : ℕ := max 1 ⌈Real.logb (alphaParam ϵ ϕ) n⌉₊

/-- `t = ⌈4000 ϕ⁻² log(1/a)⌉`, the walk length of WalkBlock (Table 1). -/
noncomputable def tParam (ϵ ϕ : ℝ) : ℕ := ⌈4000 * (ϕ ^ 2)⁻¹ * Real.log (1 / aParam ϵ ϕ)⌉₊

/-- `c₀ = (1/8) min{10⁻⁴, (128 c_loc)^{−1/60}}^{1000}` (Table 1), as a function of the constant
`c_loc` of Lemma 8.3. -/
noncomputable def c0Param (cloc : ℝ) : ℝ :=
  (1 / 8) * (min (1 / 10 ^ 4) ((128 * cloc) ^ (-(1 / 60 : ℝ)))) ^ (1000 : ℕ)

/-- `d_s = C(2s, s) / (4^s (2s − 1))`, the coefficients of the high-pass series in Eq. (10);
used for `s ≥ 1`. -/
noncomputable def seriesCoeff (s : ℕ) : ℝ :=
  (Nat.centralBinom s : ℝ) / (4 ^ s * (2 * (s : ℝ) - 1))

end WalkTreeCluster


