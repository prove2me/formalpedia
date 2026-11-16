-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_spendT
-- name    : AutobidSPPE_Supplement_spendT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:39:00.326852+00:00
-- url     : https://prove2.me/theorems/e221f1a5-1921-4275-9ca1-0e3e6173796c
-- title:
--   Expected throttling spending $s_i(\alpha)$
-- statement:
--   The **expected spending** of bidder $i$ under throttling probabilities $\alpha$ is
--   $$
--   s_i(\alpha)=\mathbb E_{v\sim\mu,\ \xi\sim\mathrm{Ber}(\alpha)}\Big[x_i(\alpha)\max_{j\ne i:\ \xi_j=1}v_j\Big],
--   $$
--   where the participation coins are independent of each other and of the values, and $\mu$ is the law of the value profile. The budget constraint of Problem 1.2 is $g_i=s_i-\rho_i\le 0$.
--
--   **Formalization Note** The expectation over the coins is the finite sum over participation sets $P$ weighted by $\pi(\alpha,P)$; the expectation over values is the integral against $\mu$. Section 3 uses the independent uniform law $\mu=\prod_i\mathrm{Unif}[0,\bar v_i]$ (published `AutobidSPPE.valueLaw`); Theorem B.1 uses an arbitrary probability measure.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26; Theorem B.1, p.54

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_partWeight
import Definitions.Def_AutobidSPPE_Supplement_allocT
import Definitions.Def_AutobidSPPE_Supplement_highestOtherT
open MeasureTheory

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Expected throttling spending
`sᵢ(α) = E_{v∼μ, ξ∼Ber(α)}[xᵢ(α) · max_{j≠i: ξⱼ=1} vⱼ]` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.2, p.4 (`gᵢ = sᵢ − ρᵢ`); §3.2,
p.26; Theorem B.1, p.54 (SPTE mechanism)). The participation coins are independent of each other and of the
values.

**Formalization Note** The expectation over the coins is the finite sum over participation sets `P`
weighted by `partWeight α P`; the expectation over the values is the integral against an arbitrary measure
`μ` on value profiles. Section 3 uses `μ = AutobidSPPE.valueLaw v̄`; Theorem B.1 uses an arbitrary
probability measure. -/
noncomputable def spendT {n : ℕ} (μ : Measure (Fin n → ℝ)) (tie : TieRule n) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∑ P : Finset (Fin n), partWeight α P * ∫ v, allocT tie P v i * highestOtherT P v i ∂μ

end AutobidSPPE.Supplement


