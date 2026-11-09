-- Prove2me | Definitions.Def_RecruitSmaller_I
-- name    : RecruitSmaller_I
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:48.539012+00:00
-- url     : https://prove2.me/theorems/c5aafc91-8fb4-4d05-8cf5-bf56bdb0bc1b
-- title:
--   Rank-$i$ threshold integrand $I_i(x)$
-- statement:
--   Let $m$ buyers have values i.i.d. with CDF $F_B$, let $F_S$ be the seller CDF, $n\ge1$, $i\in\{1,\dots,n\}$ and $x\in\mathbb R$ with $p:=F_S(x)$. The **rank-$i$ threshold integrand** is
--   $$
--   I_i(x) := p^i\,\mathbb E_{b^{(i)}}\Bigl[\Bigl(A_{n,i}(p)-\binom{n+2}{i}\bigl(1-F_S(b^{(i)})\bigr)^{n+2-i}\Bigr)\mathbb 1\bigl[b^{(i)}\ge x\bigr]\Bigr].
--   $$
--   It separates the recruitment gain (the $A_{n,i}$ term) from the trade-reduction loss at rank $i$ and threshold $x$; Lemma 3.1 bounds $\mathrm{STR}(m,n+2)-\mathrm{OPT}(m,n)$ below by $\sum_i\int I_i$.
--
--   **Formalization Note** The expectation over $b^{(i)}$ is an integral over the full profile law $\mu_B^{\otimes m}$; $I_i$ depends on $m$ through it.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.1, eq. (3.2), p.12

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_A

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller

/-- The **rank-`i` threshold integrand** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.1, eq. (3.2), p.12):
`Iᵢ(x) := pⁱ · E_{b⁽ⁱ⁾}[(A_{n,i}(p) − C(n+2, i)(1 − F_S(b⁽ⁱ⁾))^{n+2−i}) 𝟙[b⁽ⁱ⁾ ≥ x]]` with
`p := F_S(x)`, for `m` buyers with values i.i.d. from `μB`.

**Formalization Note** `F_S = cdf μS`. The expectation over `b⁽ⁱ⁾` is the Bochner integral over the
full profile law `μBᵐ` of a bounded measurable function of `b⁽ⁱ⁾`. `Iᵢ` depends on the number `m` of
buyers through that law. -/
noncomputable def I (m n : ℕ) (μB μS : Measure ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  (cdf μS x) ^ i *
    ∫ b, (A n i (cdf μS x) - ((n + 2).choose i : ℝ) * (1 - cdf μS (buyerOrd b i)) ^ (n + 2 - i)) *
        (if x ≤ buyerOrd b i then 1 else 0) ∂(Measure.pi fun _ : Fin m => μB)

end RecruitSmaller


