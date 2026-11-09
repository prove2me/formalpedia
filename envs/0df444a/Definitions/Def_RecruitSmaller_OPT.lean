-- Prove2me | Definitions.Def_RecruitSmaller_OPT
-- name    : RecruitSmaller_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:19.555639+00:00
-- url     : https://prove2.me/theorems/23a4a5b3-2047-443c-89d4-e4bbc9c3667d
-- title:
--   Expected first-best Gains From Trade $\mathrm{OPT}(m,n)$
-- statement:
--   Let buyer values $b_1,\dots,b_m$ be i.i.d. with CDF $F_B$ and seller costs $s_1,\dots,s_n$ be i.i.d. with CDF $F_S$, independent of the buyers. The **expected first-best Gains From Trade** is
--   $$
--   \mathrm{OPT}(m,n) := \mathbb E_{b\sim F_B^m,\ s_n\sim F_S^n}\bigl[\mathrm{OPT}(b,s_n)\bigr].
--   $$
--   It is the benchmark of the paper: the largest expected Gains From Trade any allocation of the original $(m,n)$ market can achieve.
--
--   **Formalization Note** $F_B$, $F_S$ are the CDFs of measures $\mu_B$, $\mu_S$ on $\mathbb R$ (probability measures in every statement). The joint law is $\mu_B^{\otimes m}\otimes\mu_S^{\otimes n}$ and the expectation is a Lebesgue integral in $[0,\infty]$ of the nonnegative integrand, so the value $+\infty$ is representable; the paper's standing assumption $\mathrm{OPT}(m,n)<\infty$ is a hypothesis of each statement that needs it.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.3, p.11

import Mathlib
import Definitions.Def_RecruitSmaller_optEx

open MeasureTheory

namespace RecruitSmaller

/-- The **expected first-best Gains From Trade** `OPT(m, n) := E_{b∼F_Bᵐ, sₙ∼F_Sⁿ}[OPT(b, sₙ)]`
(Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.3, p.11), for buyer values i.i.d. from `μB` and seller costs i.i.d. from `μS`,
independent.

**Formalization Note** The distributions are measures on `ℝ` (probability measures in every use;
`F_B = cdf μB`, `F_S = cdf μS`). The joint law is the product `μBᵐ ⊗ μSⁿ` of the i.i.d. product
laws. The expectation is the lower Lebesgue integral in `ℝ≥0∞` of `ofReal (OPT(b, sₙ))`; since
`OPT(b, sₙ) ≥ 0` the cast loses nothing and `OPT(m, n) = ∞` is representable (the paper assumes
`OPT(m, n) < ∞` as a hypothesis). -/
noncomputable def OPT (m n : ℕ) (μB μS : Measure ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (optEx ω.1 ω.2)
    ∂((Measure.pi fun _ : Fin m => μB).prod (Measure.pi fun _ : Fin n => μS))

end RecruitSmaller


