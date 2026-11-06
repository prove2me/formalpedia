-- Prove2me | Definitions.Def_QuerySampleRev_hardDist
-- name    : QuerySampleRev_hardDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:52.505136+00:00
-- url     : https://prove2.me/theorems/27b7890d-3e5f-4caa-8b53-04beffb21168
-- title:
--   Base distribution $F^{(0)}$ and hard distributions $F^{(i)}$
-- statement:
--   The **base distribution** $F^{(0)}$ is the equal-revenue distribution truncated at $e$: it has density $1/p^2$ on $(1,e)$ and an atom of mass $1/e$ at $e$, so that
--   $$
--   F^{(0)}(p)=\begin{cases}0,&p\le1,\\ 1-1/p,&1<p\le e,\\ 1,&p>e.\end{cases}
--   $$
--   The **$i$-th hard distribution** $F^{(i)}$ keeps the atom at $e$ and changes the density only on $P^{(i)}=(a_i,b_i]$: it is $(1-\rho)/p^2$ on $(a_i,m_i]$ and $(1+\rho b_i/a_i)/p^2$ on $(m_i,b_i]$, and $1/p^2$ elsewhere on $(1,e)$. Its CDF is
--   $$
--   F^{(i)}(p)=\begin{cases}1-\rho/a_i-(1-\rho)/p,&a_i<p\le m_i,\\ 1+\rho/a_i-(1+\rho b_i/a_i)/p,&m_i<p\le b_i,\\ F^{(0)}(p),&p\notin P^{(i)}.\end{cases}
--   $$
--   Under $F^{(i)}$ the revenue rises linearly from $1$ at $a_i$ to $1+\rho w/a_i$ at $m_i$ and falls back to $1$ at $b_i$.
--
--   **Formalization Note** The distributions are defined through their densities (those of the proof of Lemma 23, p.37) plus the atom; the milestone `cdf_displays` shows that their left-continuous CDFs are the printed displays. They are the paper's objects for $i\in[K]$, $c\in[0,1]$, $0<\varepsilon\le1/128$.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §5.5, proof of Theorem 21, p.36 (PDF p.38), the displays of F^(0) and F^(i); proof of Lemma 23, p.37 (PDF p.39), the densities

import Mathlib
import Definitions.Def_QuerySampleRev_priceInterval

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **The base distribution `F⁽⁰⁾`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §5.5, p.36 (PDF 38): "`F⁽⁰⁾(p) ≜ 0` for `p ≤ 1`;
`1 − 1/p` for `1 < p ≤ e`; `1` for `p > e`, which is the equal-revenue distribution truncated at `e`,
with an atom of mass `1/e` at `e`".

`baseDist` has density `1/p²` on `(1, e)` and an atom of mass `e^{−1}` at `e`; its left-continuous CDF is
the printed `F⁽⁰⁾` (milestone `cdf_displays`). -/
noncomputable def baseDist : Measure ℝ :=
  (volume.restrict (Set.Ioo 1 (Real.exp 1))).withDensity (fun p => ENNReal.ofReal (1 / p ^ 2)) +
    ENNReal.ofReal (Real.exp (-1)) • Measure.dirac (Real.exp 1)

/-- The density of the `i`-th hard distribution on `(1, e)`: `(1 − ρ)/p²` on `(a_i, m_i]`,
`(1 + ρ b_i/a_i)/p²` on `(m_i, b_i]`, and the base density `1/p²` elsewhere. Same source, proof of
Lemma 23, p.37 (PDF 39): "On the two halves of `P⁽ⁱ⁾`, the base density is `f₀(p) = 1/p²`, and
differentiating the displayed CDF gives `fᵢ(p) = (1 − ρ)/p²` and `fᵢ(p) = (1 + ρbᵢ/aᵢ)/p²`". -/
noncomputable def hardDensity (ε c : ℝ) (i : ℕ) (p : ℝ) : ℝ≥0∞ :=
  if p ∈ Set.Ioc (aPt ε c i) (mPt ε c i) then ENNReal.ofReal ((1 - rho ε c) / p ^ 2)
  else if p ∈ Set.Ioc (mPt ε c i) (bPt ε c i) then
    ENNReal.ofReal ((1 + rho ε c * bPt ε c i / aPt ε c i) / p ^ 2)
  else ENNReal.ofReal (1 / p ^ 2)

/-- **The `i`-th hard distribution `F⁽ⁱ⁾`.** Same source, §5.5, p.36 (PDF 38): "The `i`-th hard
distribution raises the revenue linearly from one at `a_i` to `1 + ρw/a_i` at `m_i` and decreases it
linearly back to one at `b_i`. The corresponding CDF is `F⁽ⁱ⁾(p) ≜ 1 − ρ/a_i − (1 − ρ)/p` for
`a_i < p ≤ m_i`; `1 + ρ/a_i − (1 + ρb_i/a_i)/p` for `m_i < p ≤ b_i`; `F⁽⁰⁾(p)` for `p ∉ P⁽ⁱ⁾`."

`hardDist ε c i` has density `hardDensity ε c i` on `(1, e)` and the same atom of mass `e^{−1}` at `e`;
its left-continuous CDF is the printed `F⁽ⁱ⁾` for `i ∈ [K]`, `c ∈ [0, 1]`, `0 < ε ≤ 1/128` (milestone
`cdf_displays`).

**Formalization Note.** Defined for every `(ε, c, i)`; it is the paper's object for `i ∈ [K]` and the
parameter range of Theorem 21, where `P⁽ⁱ⁾ ⊆ [5/4, 3/2] ⊆ (1, e)` and `ρ ≤ 1/4`. -/
noncomputable def hardDist (ε c : ℝ) (i : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Ioo 1 (Real.exp 1))).withDensity (hardDensity ε c i) +
    ENNReal.ofReal (Real.exp (-1)) • Measure.dirac (Real.exp 1)

end QuerySampleRev


