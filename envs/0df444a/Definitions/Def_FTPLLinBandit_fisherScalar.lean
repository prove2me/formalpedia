-- Prove2me | Definitions.Def_FTPLLinBandit_fisherScalar
-- name    : FTPLLinBandit_fisherScalar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:58.698205+00:00
-- url     : https://prove2.me/theorems/8254773e-3a4a-4e42-9806-e02608495bb3
-- title:
--   Scalar Fisher information $I_\varphi=\int\varphi'^2/\varphi$
-- statement:
--   For a density $\varphi$ on $\mathbb R$, the **Fisher information** is
--   $$I_\varphi=\int_{\mathbb R}\frac{\varphi'(\xi)^2}{\varphi(\xi)}\,d\xi\in[0,\infty].$$
--   It enters Lemma 5; for both laws of Table 3 it is finite ($I_\varphi=1$ for the standard Gaussian and the Laplace law).
--
--   **Formalization Note** $\varphi'$ is Mathlib's derivative, $0$ where $\varphi$ is not differentiable (the single point $0$ for the Laplace density).
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 5, p.11

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FTPLLinBandit

/-- **The Fisher information `I_φ` of a scalar density.** Wei, arXiv:2610.17818, Lemma 5, p.11:
"where I_φ = ∫ φ′(ξ)²/φ(ξ) dξ is the Fisher information associated with the scalar density φ".

`fisherScalar φ = ∫ φ′(ξ)² / φ(ξ) dξ ∈ [0, ∞]`.

**Formalization Note.** `deriv φ` is `0` where `φ` is not differentiable (for the Laplace density
of Table 3, the single point `ξ = 0`, a null set). Extended nonnegative value. -/
noncomputable def fisherScalar (φ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (deriv φ ξ ^ 2 / φ ξ)

end FTPLLinBandit


