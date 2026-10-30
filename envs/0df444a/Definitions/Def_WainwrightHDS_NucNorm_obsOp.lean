-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_obsOp
-- name    : WainwrightHDS_NucNorm_obsOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:26:53.461037+00:00
-- url     : https://prove2.me/theorems/db22a062-bcdf-40a4-a48a-f07bbb7775e9
-- title:
--   Observation operator $[\mathfrak X_n(\Theta)]_i=\langle\!\langle X_i,\Theta\rangle\!\rangle$
-- statement:
--   Given design matrices $X_1,\dots,X_n\in\mathbb R^{d_1\times d_2}$, the **observation operator** $\mathfrak X_n:\mathbb R^{d_1\times d_2}\to\mathbb R^n$ is
--
--   $$
--   [\mathfrak X_n(\Theta)]_i \;=\; \langle\!\langle X_i,\Theta\rangle\!\rangle, \qquad i=1,\dots,n .
--   $$
--
--   With it the linear matrix regression model $y_i=\langle\!\langle X_i,\Theta^*\rangle\!\rangle+w_i$ reads $y=\mathfrak X_n(\Theta^*)+w$.
--
--   **Formalization Note** The design is a family indexed by `Fin n` (0-based).
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.1, p. 312 (PDF p. 332), Eqs. (10.2)–(10.3)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner

namespace WainwrightHDS.NucNorm

/-- **Observation operator** `𝔛_n : ℝ^{d₁×d₂} → ℝⁿ`, `[𝔛_n(Θ)]_i = ⟨⟨X_i, Θ⟩⟩`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.1, p. 312 (PDF p. 332), the display before (10.3).

Formalization Note: the design matrices are a family `X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ`;
observation indices are 0-based. -/
def obsOp {n d₁ d₂ : ℕ} (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ)
    (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) : Fin n → ℝ :=
  fun i => traceInner (X i) Θ

end WainwrightHDS.NucNorm


