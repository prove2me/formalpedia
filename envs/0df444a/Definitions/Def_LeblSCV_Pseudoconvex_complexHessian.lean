-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_complexHessian
-- name    : LeblSCV_Pseudoconvex_complexHessian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:59:55.45147+00:00
-- url     : https://prove2.me/theorems/8f28dd93-bc98-442d-a650-2d559ccfacc4
-- title:
--   Complex Hessian matrix $[\partial^2 f/\partial\bar z_k \partial z_\ell]_{k\ell}$
-- statement:
--   For a real-valued $f$ on $\mathbb{C}^n$ and $p \in \mathbb{C}^n$, the **complex Hessian matrix** of $f$ at $p$ is the $n \times n$ complex matrix
--   $$\left[ \frac{\partial^2 f}{\partial \bar z_k \partial z_\ell}(p) \right]_{k\ell},$$
--   whose $(k,\ell)$ entry applies $\partial/\partial\bar z_k$ to $\partial f/\partial z_\ell$. For a $C^2$ function it is Hermitian. It characterizes plurisubharmonicity (Proposition 2.4.9).
--
--   **Formalization Note.** $f$ is coerced to a complex-valued function, and the entries are built from the Wirtinger operators of this mission. The row index is $k$ (the $\bar z$ derivative) and the column index is $\ell$, so the quadratic form $\sum_{k,\ell} \bar c_k c_\ell \, \partial^2 f / \partial \bar z_k \partial z_\ell$ is Mathlib's `star c ⬝ᵥ (H *ᵥ c)`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 85, Proposition 2.4.9

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_wirtinger

namespace LeblSCV.Pseudoconvex

/-- The complex Hessian matrix `[∂²f/∂z̄_k∂z_ℓ]_{kℓ}` at `p` of a real function `f` on `ℂⁿ`
(Lebl, p. 85, Proposition 2.4.9): the `(k, ℓ)` entry is `∂/∂z̄_k` applied to `∂f/∂z_ℓ`. -/
noncomputable def complexHessian {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (p : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun k l => wirtingerZbar (wirtingerZ (fun z => (f z : ℂ)) l) k p

end LeblSCV.Pseudoconvex


