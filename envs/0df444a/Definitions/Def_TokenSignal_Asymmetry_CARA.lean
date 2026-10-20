-- Prove2me | Definitions.Def_TokenSignal_Asymmetry_CARA
-- name    : TokenSignal_Asymmetry_CARA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:28.88567+00:00
-- url     : https://prove2.me/theorems/99db7577-bc4f-49e9-8a95-89ef099a44c8
-- title:
--   CARA utility
-- statement:
--   For a risk-aversion coefficient $\gamma>0$ and terminal wealth $\omega$, the entrepreneur’s constant-absolute-risk-aversion utility is
--
--   $$u_\gamma(\omega)=\gamma^{-1}-\gamma^{-1}\exp(-\gamma\omega).$$
--
--   This utility is used to value the risk that remains after the entrepreneur sells part of the venture.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 12 (PDF 13), Assumption 1(i)

import Mathlib

namespace TokenSignal.Asymmetry

noncomputable def cara (γ ω : ℝ) : ℝ :=
  γ⁻¹ - γ⁻¹ * Real.exp (-(γ * ω))

end TokenSignal.Asymmetry


