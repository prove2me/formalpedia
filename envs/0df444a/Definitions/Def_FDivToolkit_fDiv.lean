-- Prove2me | Definitions.Def_FDivToolkit_fDiv
-- name    : FDivToolkit_fDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:46.507166+00:00
-- url     : https://prove2.me/theorems/05527792-d3cd-4d1a-9b29-66e1ef3df1ae
-- title:
--   The $F$-divergence $D_F(\eta\,|\,\nu)$
-- statement:
--   Let $\nu$ and $\eta$ have densities $f$ and $g$, and let $F$ be a function on $[0,\infty)$. The **$F$-divergence** between $\nu$ and $\eta$ is
--   $$
--   D_F(\eta\,|\,\nu)=\int_{\mathcal S}F\!\left(\frac{g(x)}{f(x)}\right)f(x)\,dx \tag{1}
--   $$
--   with the convention $F(\tfrac00)\cdot0=0$, and $D_F(\eta\,|\,\nu)=+\infty$ if $\eta$ is not absolutely continuous with respect to $\nu$.
--
--   This is the classical divergence of Csiszár, Morimoto and Ali–Silvey, and the measure of model distance throughout the paper.
--
--   **Formalization Note** $F$ takes values in $[0,\infty]$, which is the case for the paper's $F$ by Lemma 1. The integrand is tested for $f(x)=0$ first, so Lean's $x/0=0$ is not used. The integral over $\mathbb R$ equals that over $\mathcal S$ because $f=0$ off $\mathcal S$.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (1), §2.1, p.5

import Definitions.Def_FDivToolkit_IsDensity

open MeasureTheory
open scoped ENNReal

namespace FDivToolkit

open Classical in
/-- The integrand `F(g(x)/f(x)) f(x)` of display (1), Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), §2.1, p.5, "with the convention that `F(0/0) · 0 = 0`".

**Formalization Note.** The case `f x = 0` is tested first, so Lean's `x / 0 = 0` is never used. Under
absolute continuity `g = 0` almost everywhere on `{f = 0}`, so the value there does not matter. -/
noncomputable def divIntegrand (F : ℝ → ℝ≥0∞) (f g : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  if f x = 0 then 0 else F (g x / f x) * ENNReal.ofReal (f x)

open Classical in
/-- The `F`-divergence `D_F(η|ν) = ∫_𝓢 F(g(x)/f(x)) f(x) dx` of display (1), Kruse, Schneider &
Schweizer, SSRN 3680475 (Aug 25, 2020), §2.1, p.5, where ν has density `f` and η has density `g`:
"If η is not absolutely continuous with respect to ν, then we set `D_F(η|ν) = +∞`."

**Formalization Note.** `F : ℝ → ℝ≥0∞` is any nonnegative function on `[0, ∞)`, possibly `+∞`; the
paper's `F` is of this kind by Lemma 1. The integral over `ℝ` equals the one over `𝓢` since
`f = 0` off `𝓢`. -/
noncomputable def fDiv (F : ℝ → ℝ≥0∞) (f g : ℝ → ℝ) : ℝ≥0∞ :=
  if densityMeasure g ≪ densityMeasure f then ∫⁻ x, divIntegrand F f g x else ⊤

end FDivToolkit


