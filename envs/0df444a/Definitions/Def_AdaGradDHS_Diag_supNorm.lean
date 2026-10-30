-- Prove2me | Definitions.Def_AdaGradDHS_Diag_supNorm
-- name    : AdaGradDHS_Diag_supNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:53.225772+00:00
-- url     : https://prove2.me/theorems/9a3ec7ba-b045-4b91-8083-0036a0f0cd0b
-- title:
--   The $\ell_\infty$ norm $\|x\|_\infty$
-- statement:
--   For $x \in \mathbb{R}^d$, the **$\ell_\infty$ norm** is
--   $$\|x\|_\infty = \max_{1 \le i \le d} |x_i| .$$
--
--   It enters Theorem 5 through the condition $\delta \ge \max_t \|g_t\|_\infty$ and the terms $\|x^*\|_\infty^2$ and $\max_{t \le T}\|x^* - x_t\|_\infty^2$.
--
--   **Formalization Note** On `EuclideanSpace` the norm $\|\cdot\|$ is the $\ell_2$ norm, so the $\ell_\infty$ norm is a separate definition, computed as a finite supremum in $\mathbb{R}_{\ge 0}$. For $d = 0$ it is $0$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §1.1, p. 2122 (notation ‖·‖∞); Theorem 5, p. 2132

import Mathlib

namespace AdaGradDHS.Diag

/-- **The ℓ∞ norm `‖x‖∞ = max_i |x_i|`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §1.1, p. 2122 (notation `‖·‖∞`); used in Theorem 5, p. 2132 ("δ ≥ maxt ‖gt‖∞",
"‖x∗‖∞²").

`supNorm x = max_i |x_i|`, computed as a finite supremum in `ℝ≥0` and cast to `ℝ`.

**Formalization Note.** On `EuclideanSpace` Mathlib's `‖·‖` is the ℓ2 norm, so the ℓ∞ norm is
this separate definition. For `d = 0` it is `0` (the empty supremum in `ℝ≥0`), the correct
value of the ℓ∞ norm on `ℝ^0`. -/
noncomputable def supNorm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((Finset.univ.sup fun i => ‖x i‖₊ : NNReal) : ℝ)

end AdaGradDHS.Diag


