-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_lossT
-- name    : AutobidSPPE_Supplement_lossT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:39:41.798298+00:00
-- url     : https://prove2.me/theorems/df3ae93a-9984-4cee-b66d-fcb276e164aa
-- title:
--   Throttling loss $l_i(\alpha)=-\mathbb E[x_i(\alpha)v_i]$
-- statement:
--   The **loss** of a value-maximizing bidder $i$ under throttling is
--   $$
--   l_i(\alpha)=-\mathbb E_{v\sim\mu,\ \xi\sim\mathrm{Ber}(\alpha)}[x_i(\alpha)\,v_i].
--   $$
--
--   **Formalization Note** As for spending, the coin expectation is the finite sum over participation sets weighted by $\pi(\alpha,P)$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_partWeight
import Definitions.Def_AutobidSPPE_Supplement_allocT
open MeasureTheory

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The throttling loss of a value-maximizing bidder
`lᵢ(α) = −E_{v∼μ, ξ∼Ber(α)}[xᵢ(α) vᵢ]` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26).

**Formalization Note** The coin expectation is the finite sum over participation sets weighted by
`partWeight`, as in `spendT`. -/
noncomputable def lossT {n : ℕ} (μ : Measure (Fin n → ℝ)) (tie : TieRule n) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  -∑ P : Finset (Fin n), partWeight α P * ∫ v, allocT tie P v i * v i ∂μ

end AutobidSPPE.Supplement


