-- Prove2me | Definitions.Def_GrothendieckPD_Digits_ArcsineTail
-- name    : GrothendieckPD_Digits_ArcsineTail
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:21.815328+00:00
-- url     : https://prove2.me/theorems/4836d86e-c2ef-4777-9eb3-7e2bf85316e9
-- title:
--   Correlation polynomials and the finite arcsine head for Claim 5 of Lemma C.2
-- statement:
--   For each row $i$ of Table 1, this module defines the correlation polynomial
--   $$P_i(t)=\sum_{m=1}^{15}[t^m]P_i(t)\,t^m$$
--   and its coefficientwise absolute-value version $P_{i,+}$, obtained by replacing every coefficient by its absolute value.
--
--   For a real polynomial $P$ with zero constant term, `arcsinCoef P m` is the degree-$m$ coefficient of
--   $$\frac{2}{\pi}\arcsin P(t)
--    =\frac{2}{\pi}\sum_{k\ge0}\frac{\binom{2k}{k}}{4^k(2k+1)}P(t)^{2k+1}.$$
--   The coefficient is represented by the finite sum over $0\le k<m$; all omitted powers have degree greater than $m$. Finally,
--   $$\operatorname{arcsinHead}(i)=\sum_{m=1}^{681}[t^m]\left(\frac{2}{\pi}\arcsin P_{i,+}(t)\right).$$
--   This is precisely the nonnegative finite head appearing in the tail estimate (C.36).
--
--   **Formalization Note** Polynomial coefficients and finite sums are exact real expressions. The truncation to `Finset.range m` is valid because $P(0)=0$ for the polynomials to which this construction is applied.
-- source:
--   Heilman–Jones–Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820, Table 1 p. 15, Eq. (C.8) p. 24, and Eqs. (C.35)–(C.36) p. 35. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

open scoped BigOperators

namespace GrothendieckPD.Digits

/-- The correlation polynomial `P_i` from Table 1. -/
noncomputable def corrPoly (i : ℕ) : Polynomial ℝ :=
  ∑ m ∈ tableDegrees, Polynomial.C (pcoef i m) * Polynomial.X ^ m

/-- The coefficientwise absolute-value polynomial `P_{i,+}` of Eq. (C.8). -/
noncomputable def corrPolyAbs (i : ℕ) : Polynomial ℝ :=
  ∑ m ∈ tableDegrees, Polynomial.C |pcoef i m| * Polynomial.X ^ m

/-- The degree-`m` coefficient of `(2 / π) arcsin P(t)`, for a polynomial `P`
with zero constant term.  Terms with `2 * k + 1 > m` vanish, so `range m` suffices. -/
noncomputable def arcsinCoef (P : Polynomial ℝ) (m : ℕ) : ℝ :=
  (2 / Real.pi) * ∑ k ∈ Finset.range m,
    ((Nat.choose (2 * k) k : ℝ) / (4 ^ k * (2 * k + 1))) *
      (P ^ (2 * k + 1)).coeff m

/-- The finite head through degree 681 of the nonnegative arcsine majorant. -/
noncomputable def arcsinHead (i : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 681, arcsinCoef (corrPolyAbs i) m

end GrothendieckPD.Digits


