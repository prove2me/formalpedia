-- Prove2me | Definitions.Def_IntMul_HvdH_JApprox
-- name    : IntMul_HvdH_JApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T00:12:46.47824+00:00
-- url     : https://prove2.me/theorems/ff971ed5-0ef2-4e40-8655-2ec526418f19
-- title:
--   Truncated Neumann-series approximation of $\mathcal J'=\mathcal N^{-1}/2$ (Harvey–van der Hoeven Lemma 4.12)
-- statement:
--   Computable approximation of $\mathcal J'=\mathcal N^{-1}/2=(I+\mathcal E)^{-1}/2$ by the truncated Neumann series
--   $$\mathcal J'u=v-\mathcal Ev+\mathcal E^2v-\cdots,\qquad v=u/2.$$
--   Here $\mathcal E$ is the off-diagonal map of `IntMul_HvdH_EApprox`.
--
--   * `halfFP U` $=\tilde v^{(0)}$ halves each component of $U$, rounding towards zero.
--   * `jIter p s t α` $=n=\lceil ps/(\alpha^2(t-s))\rceil=\lceil p/(\alpha^2\theta)\rceil$ with $\theta=t/s-1$.
--   * `vIter p s t α U j` $=\tilde v^{(j)}=\tilde{\mathcal E}^j\tilde v^{(0)}$, using `Eapprox` (Lemma 4.11).
--   * `Japprox p s t α U ℓ` $=\sum_{j<n}(-1)^j\tilde v^{(j)}_\ell$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.12

import Definitions.Def_IntMul_HvdH_EApprox

/-! Fixed-point approximation of `J' = N⁻¹ / 2 = (I + E)⁻¹ / 2` by the truncated Neumann series
`v - Ev + E²v - ⋯` with `v = u / 2` (Harvey–van der Hoeven Lemma 4.12). Gaussian integers are
pairs `(re, im) : ℤ × ℤ`, and a fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing
for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- `ṽ⁽⁰⁾ = ρ(U / 2)`, halving each component with rounding towards zero. -/
def halfFP (U : ℕ → ℤ × ℤ) (i : ℕ) : ℤ × ℤ := ((U i).1.tdiv 2, (U i).2.tdiv 2)

/-- Number of Neumann terms `n = ⌈ps / (α²(t - s))⌉ = ⌈p / (α²θ)⌉`. -/
def jIter (p s t α : ℕ) : ℕ := (p * s + α ^ 2 * (t - s) - 1) / (α ^ 2 * (t - s))

/-- The iterates `ṽ⁽ʲ⁾ = Ẽ ṽ⁽ʲ⁻¹⁾` (Lemma 4.11 applied `j` times to `ṽ⁽⁰⁾`). -/
def vIter (p s t α : ℕ) (U : ℕ → ℤ × ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0 => halfFP U
  | j + 1 => Eapprox p s t α (vIter p s t α U j)

/-- Lemma 4.12: `J̃' U = ṽ⁽⁰⁾ - ṽ⁽¹⁾ + ⋯ ± ṽ⁽ⁿ⁻¹⁾`. -/
def Japprox (p s t α : ℕ) (U : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  (∑ j ∈ Finset.range (jIter p s t α), (-1) ^ j * (vIter p s t α U j l).1,
    ∑ j ∈ Finset.range (jIter p s t α), (-1) ^ j * (vIter p s t α U j l).2)

end IntMul.HvdH


