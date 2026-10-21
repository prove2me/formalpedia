-- Prove2me | Definitions.Def_FlagshipMEA_Monopoly_LogitChoice
-- name    : FlagshipMEA_Monopoly_LogitChoice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:15.455492+00:00
-- url     : https://prove2.me/theorems/08b7c344-04d3-4bbf-be64-2100720d0063
-- title:
--   §2, equation (3) — finite multinomial logit shares with outside option
-- statement:
--   For a finite collection of product attractions $w_i$, the multinomial logit share of product $i$, with the outside option normalized to attraction $1$, is
--
--   $$q_i(w)=\frac{w_i}{1+\sum_j w_j}.$$
--
--   In the marketing model, $w_i=e^{(u_i+\Delta u_i)/\lambda}>0$, so the denominator is positive. Separating this general choice formula lets the paper-specific marketing model supply its own attractions without redefining logit choice.
--
--   **Formalization Note** The function is total on real vectors, but the mission uses it only on positive attractions, where the probability interpretation applies.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 9 (PDF 11), §2, equation (3); outside-option normalization p. 8 (PDF 10)

import Mathlib

namespace FlagshipMEA.Monopoly

/-- Multinomial logit share for finite product attractions, with an outside
option normalized to attraction one (§2, equation (3)). -/
noncomputable def logitShare {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  w i / ((∑ j, w j) + 1)

end FlagshipMEA.Monopoly


