-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_alphaLow
-- name    : AutobidSPPE_Supplement_alphaLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:45:02.305335+00:00
-- url     : https://prove2.me/theorems/2e8a4f38-2912-4d76-aa8c-da92be75299c
-- title:
--   Lower box endpoints $\underline\alpha_i=\tfrac12\min\{1,4\rho_i/\hat v_i\}$
-- statement:
--   From budgets $\rho_i$ and certified support upper bounds $\hat v_i$,
--   $$
--   \underline\alpha_i=\tfrac12\min\{1,\,4\rho_i/\hat v_i\}.
--   $$
--   Responses satisfy $r_i\ge 2\underline\alpha_i$ (Lemma 3.3).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (59), p.28

import Mathlib

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The lower box endpoints `α̲ᵢ = ½ min{1, 4ρᵢ/v̂ᵢ}` of (59) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (59), p.28), from the budgets and the
certified support upper bounds `v̂ᵢ`. -/
noncomputable def alphaLow {n : ℕ} (vhat ρ : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 / 2) * min 1 (4 * ρ i / vhat i)

end AutobidSPPE.Supplement


