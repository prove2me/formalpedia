-- Prove2me | Definitions.Def_QCQPTightness_ConvHull_Recession
-- name    : QCQPTightness_ConvHull_Recession
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:06.841286+00:00
-- url     : https://prove2.me/theorems/22d4739f-3963-40bd-bd2a-8d6d96f04d90
-- title:
--   p. 13 — the recession part of the Lagrangian q̆(γ, x) = Σ_{i=1}^m γ_i q_i(x)
-- statement:
--   For $\gamma\in\mathbb R^m$ and $x\in\mathbb R^N$, the paper (p. 13) writes
--   $$\breve q(\gamma,x)=\sum_{i=1}^m\gamma_iq_i(x),$$
--   the Lagrangian $q(\gamma,x)$ without the objective $q_0(x)$. It governs the recession directions of $\Gamma$: along a direction $\gamma_r$ of the recession cone, $q(\gamma+\lambda\gamma_r,x)=q(\gamma,x)+\lambda\,\breve q(\gamma_r,x)$.
--
--   It appears in Lemma 8, where the face $\mathcal F(\hat x)$ decomposes into a polytope part and the cone over the directions $\gamma_r$ with $\breve q(\gamma_r,\hat x)=0$.
-- source:
--   arXiv:1911.09195v3, p. 13 (notation before Lemma 8)

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

noncomputable section

namespace QCQPTightness.ConvHull

open Matrix

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- The recession part of the Lagrangian, `q̆(γ, x) = Σ_{i=1}^m γ_i q_i(x)` (p. 13): the
Lagrangian `q(γ, x)` without the objective `q₀(x)`. -/
def qBreve (γ : Fin m → ℝ) (x : Fin N → ℝ) : ℝ := ∑ i, γ i * P.q i x

end QCQP

end QCQPTightness.ConvHull


