-- Prove2me | Definitions.Def_RecruitSmaller_Supplement_GFT__8e3ec3
-- name    : RecruitSmaller_Supplement_GFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:56:37.525568+00:00
-- url     : https://prove2.me/theorems/8e3ec35d-d13a-4261-9f2b-c30a66707840
-- title:
--   Expected Gains From Trade $\mathrm{GFT}_M(m,k;F_B,F_S)$ of a mechanism
-- statement:
--   For buyer values i.i.d. from $F_B$ and seller costs i.i.d. from $F_S$, all independent, the **expected Gains From Trade** of a mechanism $M$ for $m$ buyers and $k$ sellers is
--   $$
--   \mathrm{GFT}_M(m,k)=\mathrm{GFT}_M(m,k;F_B,F_S):=\mathbb E_{b\sim F_B^m,\ s\sim F_S^k}\big[\mathrm{gft}_M(b,s)\big].
--   $$
--   It is the quantity compared with the first-best $\mathrm{OPT}$ in the paper's lower bounds.
--
--   **Formalization Note** The expectation is the real Bochner integral over the product law $\mu_B^m\otimes\mu_S^k$ (the same law as the published $\mathrm{OPT}$ and $\mathrm{STR}$). It equals $0$ for a non-integrable integrand, so every theorem using it also asserts integrability.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_RecruitSmaller_Supplement_gft

open MeasureTheory

namespace RecruitSmaller.Supplement

/-- The **expected Gains From Trade** of a mechanism `M` for `m` buyers and `k` sellers
(Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10): `GFT_M(m, k; F_B, F_S) := E_{b∼F_Bᵐ, s∼F_Sᵏ}[gft_M(b, s)]`, buyer values
i.i.d. from `μB`, seller costs i.i.d. from `μS`, all independent.

**Formalization Note** The joint law is `μBᵐ ⊗ μSᵏ`, the same product law as the published
`RecruitSmaller.OPT`/`RecruitSmaller.STR`. Since `gft_M` can be negative the expectation is the
real Bochner integral; it is `0` for a non-integrable integrand, so every theorem that uses
`GFT` also asserts integrability. -/
noncomputable def GFT {m k : ℕ} (M : Mechanism m k) (μB μS : Measure ℝ) : ℝ :=
  ∫ ω, gft M ω.1 ω.2
    ∂((Measure.pi fun _ : Fin m => μB).prod (Measure.pi fun _ : Fin k => μS))

end RecruitSmaller.Supplement


