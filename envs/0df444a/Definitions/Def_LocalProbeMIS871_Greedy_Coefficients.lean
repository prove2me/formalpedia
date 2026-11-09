-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Coefficients
-- name    : LocalProbeMIS871_Greedy_Coefficients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T01:51:28.065124+00:00
-- url     : https://prove2.me/theorems/a367aff9-3461-41ce-b127-0f3931fe7bb5
-- title:
--   Equation (30) — The explicit real-exponent coefficient integrals
-- statement:
--   For a real exponent $s>1$, the coefficients used in the inequality for $D$ are the specific integrals
--
--   $$u_s=s\int_0^1\frac{z^{s-1}\ln(1/z)}{\ln(1+(s-1)z)}\,dz,\qquad w_s=s\int_0^1\frac{z^{s-1}\ln^2(1/z)}{\ln(1+(s-1)z)}\,dz.$$
--
--   These are computed functions of $s$, not adjustable witnesses. Lemma 3.9 asserts their positivity and integrability for every $s>1$; Lemma A.1 gives the two estimates at $s=5$.
--
--   **Formalization Note** Integration uses the open interval $(0,1)$ with Lebesgue measure, avoiding endpoint quotients. Both integrands have their real powers and logarithms as printed. The definitions are total for other exponents, but no theorem here uses those other values.
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 22, PDF p. 24, §3.3.3, Eq.(30); Appendix A (PDF p.39); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Mathlib

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Eq.(30), printed p.22 / PDF24; open-interval integrands, extended by the integral convention. -/
def uIntegrand (s z : ℝ) : ℝ :=
  z ^ (s - 1) * Real.log (1 / z) / Real.log (1 + (s - 1) * z)

def wIntegrand (s z : ℝ) : ℝ :=
  z ^ (s - 1) * (Real.log (1 / z)) ^ (2 : ℕ) / Real.log (1 + (s - 1) * z)

def coeffU (s : ℝ) : ℝ := s * ∫ z in Set.Ioo (0 : ℝ) 1, uIntegrand s z

def coeffW (s : ℝ) : ℝ := s * ∫ z in Set.Ioo (0 : ℝ) 1, wIntegrand s z

end LocalProbeMIS871.Greedy


