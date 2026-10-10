-- Prove2me | Definitions.Def_QCQPTightness_Exact_Recession
-- name    : QCQPTightness_Exact_Recession
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:56.169066+00:00
-- url     : https://prove2.me/theorems/88ee5750-559b-4914-945f-6284ad7db054
-- title:
--   Recession notation, p. 13 — q̆(γ, x) = Σ_{i=1}^m γ_i q_i(x)
-- statement:
--   For $\gamma\in\mathbb R^m$ and $x\in\mathbb R^N$, the recession part of the Lagrangian is
--
--   $$\breve q(\gamma,x) := \sum_{i=1}^m\gamma_i q_i(x),$$
--
--   the Lagrangian $q(\gamma,x)$ without the objective $q_0(x)$. It governs the behaviour of $q(\cdot,x)$ along the recession directions of $\Gamma$ (Lemma 8).
-- source:
--   arXiv:1911.09195v3, §4.1, p. 13, display before Lemma 8

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP

noncomputable section

namespace QCQPTightness.Exact

/-- The recession part of the Lagrangian, `q̆(γ, x) = Σ_{i=1}^m γ_i q_i(x)` (p. 13). -/
def qBreve {N m : ℕ} (P : QCQP N m) (γ : Fin m → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, γ i * P.q i x

end QCQPTightness.Exact


