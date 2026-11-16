-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Supplement_Divergences
-- name    : MatrixSenseRank_Testing_Supplement_Divergences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:06:01.062409+00:00
-- url     : https://prove2.me/theorems/ba46d78d-3441-4c54-8f43-7ea0412a79e4
-- title:
--   Extended chi-squared divergence and total variation
-- statement:
--   For probability measures $P,Q$ on a measurable space, define
--
--   $$\chi^2(P\Vert Q)=\begin{cases}\displaystyle\int\left(\frac{dP}{dQ}-1\right)^2\,dQ,&P\ll Q,\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   The nonnegative integral may be infinite; no square-integrability or absolute-continuity premise is built into a later upper bound. Total variation is the supremum of $|P(E)-Q(E)|$ over measurable events $E$. Both quantities take extended nonnegative values, retaining singular cases.
--
--   These definitions compare the actual continuous observation laws in the full-Gaussian lower bound. All uses are probability measures, so the Radon–Nikodym density is finite almost everywhere; converting this density to a real number inside the integrand loses no mass.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; §3.1 and Appendix B, printed p. 12, 46–47, PDF p. 13, 47–48 (1-based).

import Mathlib

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MatrixSenseRank.Testing.Supplement

/-- Appendix B, extended convention: singular or infinite-square-density laws give infinity. -/
noncomputable def chiSquared {α : Type} [MeasurableSpace α] (P Q : Measure α) : ℝ≥0∞ :=
  open Classical in
  if P ≪ Q then ∫⁻ x, ENNReal.ofReal (((P.rnDeriv Q x).toReal - 1) ^ 2) ∂Q else ⊤

/-- Supremum over all measurable events, with extended values retained. -/
noncomputable def totalVariation {α : Type} [MeasurableSpace α] (P Q : Measure α) : ℝ≥0∞ :=
  ⨆ (E : Set α) (_ : MeasurableSet E), max (P E - Q E) (Q E - P E)

end MatrixSenseRank.Testing.Supplement


