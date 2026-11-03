-- Prove2me | Definitions.Def_DCAExtrap_bregman
-- name    : DCAExtrap_bregman
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:16.465473+00:00
-- url     : https://prove2.me/theorems/1c4f45b3-5331-4b41-ab0b-f2ad7e683a82
-- title:
--   Bregman distance $D_\varphi(x,y)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $\varphi:E\to\mathbb R$. The **Bregman distance** of $\varphi$ is
--
--   $$
--   D_\varphi(x,y) := \varphi(x) - \bigl[\varphi(y) + \langle \nabla\varphi(y), x-y\rangle\bigr].
--   $$
--
--   The gradient is taken at the second argument $y$. For convex $\varphi$ it is nonnegative, and for $\rho$-strongly convex $\varphi$ it is at least $\tfrac{\rho}{2}\|x-y\|^2$. It measures the step sizes in the extrapolation rule (8) and enters the auxiliary function (24).
--
--   **Formalization Note** $\nabla\varphi$ is Mathlib's `gradient`.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, §3.1, p.5, D_φ(x, y) := φ(x) − [φ(y) + ⟨∇φ(y), x − y⟩]

import Mathlib

open scoped InnerProductSpace

namespace DCAExtrap

/-- **Bregman distance** of the kernel `φ` (Phan–Le Thi, arXiv:2106.04743v1, §3.1, p.5):
`D_φ(x, y) := φ(x) − [φ(y) + ⟨∇φ(y), x − y⟩]`.

**Formalization Note.** `E` is a real inner product space, so `∇φ(y)` is Mathlib's `gradient φ y`.
The argument order is the paper's: the gradient is taken at the second argument `y`. -/
noncomputable def bregman {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (φ : E → ℝ) (x y : E) : ℝ :=
  φ x - (φ y + ⟪gradient φ y, x - y⟫_ℝ)

end DCAExtrap


