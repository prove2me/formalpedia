-- Prove2me | Definitions.Def_AnalystRanking_Revelation_gl
-- name    : AnalystRanking_Revelation_gl
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:41:06.721782+00:00
-- url     : https://prove2.me/theorems/6778a917-1c48-4e4c-b8bd-1acc522878ec
-- title:
--   $g_l(\sigma^h,\sigma^l)$, (B.5a)
-- statement:
--   $$g_l(\sigma^h,\sigma^l)=\frac{\gamma}{1-\gamma}\,\Psi^l_i(\sigma^h,\sigma^l)$$ ((B.5a), p. 34). A low-signal analyst is indifferent at $(\sigma^h,\sigma^l)$ exactly when the prior odds $q/(1-q)$ equal $g_l$.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3, (B.5a), p. 34

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_psiL

namespace AnalystRanking.Revelation

/-- **`g_l(σʰ, σˡ)`, (B.5a).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3, display (B.5a), p. 34: `g_l(σʰ, σˡ) ≡ (γ/(1 − γ)) Ψˡ_i(σʰ, σˡ)`. -/
noncomputable def gl (γ ρ φ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  γ / (1 - γ) * psiL γ ρ φ σ

end AnalystRanking.Revelation


