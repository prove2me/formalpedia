-- Prove2me | Definitions.Def_AnalystRanking_Revelation_gh
-- name    : AnalystRanking_Revelation_gh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:41:35.22911+00:00
-- url     : https://prove2.me/theorems/256bdd52-40e5-4b99-a827-9065e74512f0
-- title:
--   $g_h(\sigma^h,\sigma^l)$, (B.5b)
-- statement:
--   $$g_h(\sigma^h,\sigma^l)=\frac{1-\gamma}{\gamma}\,\Psi^h_i(\sigma^h,\sigma^l)$$ ((B.5b), p. 34). A high-signal analyst is indifferent at $(\sigma^h,\sigma^l)$ exactly when the prior odds $q/(1-q)$ equal $g_h$.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3, (B.5b), p. 34

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_psiH

namespace AnalystRanking.Revelation

/-- **`g_h(σʰ, σˡ)`, (B.5b).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3, display (B.5b), p. 34: `g_h(σʰ, σˡ) ≡ ((1 − γ)/γ) Ψʰ_i(σʰ, σˡ)`. -/
noncomputable def gh (γ ρ φ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  (1 - γ) / γ * psiH γ ρ φ σ

end AnalystRanking.Revelation


