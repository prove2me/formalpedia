-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_quadFun
-- name    : FourierRankQLB_Supplement_quadFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:13:59.398189+00:00
-- url     : https://prove2.me/theorems/69ee0f25-7ba0-4f6b-9567-8cb9178497a2
-- title:
--   Quadratic function $f(x) = \tfrac12 x^\top H x + b^\top x + c$
-- statement:
--   For a real $n\times n$ matrix $H$, a vector $b \in \mathbb R^n$ and a scalar $c \in \mathbb R$, the **quadratic function** with these data is
--
--   $$
--   f(x) = \tfrac12\, x^\top H x + b^\top x + c, \qquad x \in \mathbb R^n.
--   $$
--
--   When $H$ is symmetric it is the Hessian of $f$, and $\nabla f(x) = Hx + b$. The hard functions $f_{Q,b}$ of Eq. (64) and the two-function families $f_\pm(x) = \tfrac12\|x \mp 2\eta e_1\|^2$ of the proofs of Theorems 6.1 and 7.13 are of this form.
--
--   **Formalization Note** $H$ is unrestricted here; the class `IsSCSmoothQuadratic` adds symmetry and the spectral bounds.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §6, p.33 and Eq. (64), p.34

import Mathlib
import Definitions.Def_FourierRankQLB_Ambient

open Matrix

namespace FourierRankQLB

namespace Supplement

/-- The quadratic function `f(x) = ½ xᵀ H x + bᵀ x + c` on `ℝⁿ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §6, p. 33 (quadratic functions with Hessian `H`) and Eq. (64), p. 34.

**Formalization Note.** `H` is any real `n × n` matrix here; the statements that use quadratic
functions require `H` symmetric, so that `H` is the Hessian and `∇f(x) = Hx + b`. -/
noncomputable def quadFun {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (b : Ambient n) (c : ℝ) :
    Ambient n → ℝ :=
  fun x => (1 / 2 : ℝ) * (x.ofLp ⬝ᵥ (H *ᵥ x.ofLp)) + inner ℝ b x + c

end Supplement

end FourierRankQLB


