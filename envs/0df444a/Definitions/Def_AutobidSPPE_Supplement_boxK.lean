-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_boxK
-- name    : AutobidSPPE_Supplement_boxK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:45:35.602206+00:00
-- url     : https://prove2.me/theorems/f9c75d6f-6c85-44cc-a5f3-0ea90e8ba465
-- title:
--   Proof box $\mathcal K=\prod_i[\underline\alpha_i,1]$
-- statement:
--   $$
--   \mathcal K=\prod_{i=1}^n[\underline\alpha_i,1],
--   $$
--   the positive box that contains every SPTE and is entered by every trajectory by time $T_0$ (Lemma 3.3).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (59), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_alphaLow

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The positive proof box `K = ∏ᵢ [α̲ᵢ, 1]` of (59) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (59), p.28). -/
def boxK {n : ℕ} (vhat ρ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {α | ∀ i, alphaLow vhat ρ i ≤ α i ∧ α i ≤ 1}

end AutobidSPPE.Supplement


