-- Prove2me | Definitions.Def_AutobidSPPE_loss
-- name    : AutobidSPPE_loss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:57.863825+00:00
-- url     : https://prove2.me/theorems/7a6ac718-5440-4399-b931-584a60ec457f
-- title:
--   Loss $l_i(\alpha)=-\mathbb E[x_i(\alpha)v_i]$
-- statement:
--   The **loss** of the value-maximizing bidder $i$ at the multiplier profile $\alpha$ is the negative expected allocated value
--   $$
--   l_i(\alpha) = -\,\mathbb E_{v\sim\mathcal D}\big[x_i(\alpha)\,v_i\big].
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.1, p.4; §2.2, p.10

import Mathlib
import Definitions.Def_AutobidSPPE_valueLaw
import Definitions.Def_AutobidSPPE_alloc
open MeasureTheory

namespace AutobidSPPE

/-- The loss of a value-maximizing bidder `lᵢ(α) = −E_{v∼D}[xᵢ(α)vᵢ]` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.1, p.4;
§2.2, p.10). -/
noncomputable def loss {n : ℕ} (vbar : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  -∫ v, alloc tie α v i * v i ∂(valueLaw vbar)

end AutobidSPPE


