-- Prove2me | Definitions.Def_GaussPart_Supplement_L1Degree
-- name    : GaussPart_Supplement_L1Degree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:05:50.667315+00:00
-- url     : https://prove2.me/theorems/c3826beb-f310-4e9a-b33f-319fca393edb
-- title:
--   The Gaussian $L_1$ approximation degree $\deg_{1,\epsilon}(f)$
-- statement:
--   For $f:\mathbb R^K\to\{\pm1\}$ and $\epsilon\in(0,1)$,
--   $$
--   \deg_{1,\epsilon}(f)=\min\Bigl\{r:\ \exists\text{ a polynomial }p:\mathbb R^K\to\mathbb R,\ \deg p\le r,\ \mathbb E_{z\sim\mathcal N(0,I_K)}\bigl[|p(z)-f(z)|\bigr]<\epsilon\Bigr\}.
--   $$
--   It is the degree in the multiplicative-approximation SQ lower bound (Theorem E.2).
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so a non-integrable difference never counts as small; the inequality is strict, as on the page.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Appendix E, p.77 (PDF p.79)

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_Supplement_BoolFn

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **The Gaussian `L₁` approximation degree** (Appendix E, arXiv:2611.05264, sha256 7e0ca6d4…,
p.77, PDF p.79): for `f : ℝᴷ → {±1}` and `ϵ ∈ (0, 1)`,
`deg_{1,ϵ}(f) := min { r : ∃ polynomial p : ℝᴷ → ℝ, deg(p) ≤ r, E_{z∼N(0,I_K)}[|p(z) − f(z)|] < ϵ }`.

**Formalization Note.** The expectation is a lower Lebesgue integral in `[0, ∞]` (no junk value
for a non-integrable integrand); the inequality is strict, as on the page. For a measurable
`f : ℝᴷ → {±1}` the set is nonempty (polynomials are dense in `L₁(N(0, I_K))`), so `sInf` is a
minimum; `sInf ∅ = 0` occurs only outside that case. -/
noncomputable def l1Degree {K : ℕ} (f : Vec K → ℝ) (ε : ℝ) : ℕ :=
  sInf {r : ℕ | ∃ p : MvPolynomial (Fin K) ℝ, p.totalDegree ≤ r ∧
    ∫⁻ z, ENNReal.ofReal |evalPoly p z - f z| ∂(stdGaussian (Vec K)) < ENNReal.ofReal ε}

end Supplement

end GaussPart


