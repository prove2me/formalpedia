-- Prove2me | Definitions.Def_UninformedMG_cDelta
-- name    : UninformedMG_cDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:22.522248+00:00
-- url     : https://prove2.me/theorems/1229c266-554e-41ab-be93-a19847540e8b
-- title:
--   The constant $C_\delta$ and the parameter $\lambda$ of Theorem 2.1
-- statement:
--   For a horizon $H$, $S$ nonterminal states, $N$ candidates, $A$ learner actions and $\delta\in(0,1)$,
--   $$C_\delta=(H+1)\log N+2S\log A+(H+1)\log(2/\delta),\qquad \lambda=\min\Big\{\big[2(A+1)S\big]^{-1},\ \sqrt{C_\delta/[2(A+1)SK]}\Big\}.$$
--
--   These are the constants of the main theorem (natural logarithm).
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Theorem 2.1, p.11 (PDF p.13)

import Mathlib

namespace UninformedMG

/-- **The confidence constant of Theorem 2.1** (p.11 = PDF p.13):
`C_δ = (H + 1) log N + 2 S log A + (H + 1) log(2/δ)`, for horizon `H`, `S` nonterminal states,
`N` candidates and `A` learner actions (natural logarithm). -/
noncomputable def cDelta (H S N A : ℕ) (δ : ℝ) : ℝ :=
  ((H : ℝ) + 1) * Real.log N + 2 * S * Real.log A + ((H : ℝ) + 1) * Real.log (2 / δ)

/-- **The learning rate of Theorem 2.1** (p.11 = PDF p.13):
`λ = min{[2(A + 1)S]⁻¹, √(C_δ / [2(A + 1)SK])}`. -/
noncomputable def lamThm (H K S N A : ℕ) (δ : ℝ) : ℝ :=
  min (1 / (2 * ((A : ℝ) + 1) * S)) (Real.sqrt (cDelta H S N A δ / (2 * ((A : ℝ) + 1) * S * K)))

end UninformedMG


