-- Prove2me | Definitions.Def_AutobidSPPE_gammaLow
-- name    : AutobidSPPE_gammaLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:44.09312+00:00
-- url     : https://prove2.me/theorems/c95d2846-bb7e-41fd-8cce-dd0b53c67ee4
-- title:
--   $\underline\gamma=\varrho^{2n}/n!$ (also $a$)
-- statement:
--   The constant
--   $$
--   \underline\gamma = \frac{\varrho^{2n}}{n!},
--   $$
--   which is also the lower sector constant $a=\underline\gamma$ of (12).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (11)–(12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_varrho

namespace AutobidSPPE

/-- `γ̲ = ϱ^{2n}/n!` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (11), p.11); also `a = γ̲` ((12), p.11), the lower sector constant. -/
noncomputable def gammaLow {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  varrho vhat ρ ^ (2 * n) / (n.factorial : ℝ)

end AutobidSPPE


