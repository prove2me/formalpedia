-- Prove2me | Definitions.Def_RecruitSmaller_STR
-- name    : RecruitSmaller_STR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:28.197034+00:00
-- url     : https://prove2.me/theorems/b50c52ad-8029-4aac-aa6c-4a4a524e34ab
-- title:
--   Expected Gains From Trade of Seller Trade Reduction $\mathrm{STR}(m,k)$
-- statement:
--   With $m$ buyers whose values are i.i.d. with CDF $F_B$ and $k$ sellers whose costs are i.i.d. with CDF $F_S$, independent, the **expected Gains From Trade of Seller Trade Reduction** is
--   $$
--   \mathrm{STR}(m,k) := \mathbb E_{b\sim F_B^m,\ s_k\sim F_S^k}\bigl[\mathrm{STR}(b,s_k)\bigr].
--   $$
--   Seller Trade Reduction is dominant-strategy incentive compatible, individually rational, weakly budget balanced and prior-independent; the paper compares $\mathrm{STR}(m,n+2)$ with $\mathrm{OPT}(m,n)$.
--
--   **Formalization Note** As for $\mathrm{OPT}$: product law $\mu_B^{\otimes m}\otimes\mu_S^{\otimes k}$, Lebesgue integral in $[0,\infty]$ of the nonnegative integrand.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.4, p.11

import Mathlib
import Definitions.Def_RecruitSmaller_strEx

open MeasureTheory

namespace RecruitSmaller

/-- The **expected Gains From Trade of Seller Trade Reduction**
`STR(m, k) := E_{b∼F_Bᵐ, sₖ∼F_Sᵏ}[STR(b, sₖ)]` (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.4, p.11), for `m` buyers with
values i.i.d. from `μB` and `k` sellers with costs i.i.d. from `μS`, independent.

**Formalization Note** As for `OPT`: product law `μBᵐ ⊗ μSᵏ`, lower Lebesgue integral in `ℝ≥0∞` of
`ofReal (STR(b, sₖ))`; `STR(b, sₖ) ≥ 0` (every traded pair has `b⁽ⁱ⁾ ≥ s⁽ⁱ⁾ₖ`), so the cast loses
nothing and the value `∞` is representable. -/
noncomputable def STR (m k : ℕ) (μB μS : Measure ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (strEx ω.1 ω.2)
    ∂((Measure.pi fun _ : Fin m => μB).prod (Measure.pi fun _ : Fin k => μS))

end RecruitSmaller


