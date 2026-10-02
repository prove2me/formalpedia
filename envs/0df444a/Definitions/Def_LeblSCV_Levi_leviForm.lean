-- Prove2me | Definitions.Def_LeblSCV_Levi_leviForm
-- name    : LeblSCV_Levi_leviForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:27:30.025809+00:00
-- url     : https://prove2.me/theorems/e5bc760e-27ee-49ca-8401-48bb90f3c536
-- title:
--   Definition 2.3.5 — the Levi form $\mathcal{L}(X_p, X_p)$
-- statement:
--   Let $r$ be a real-valued defining function at $p$ and $X_p = \sum_{k=1}^n a_k \frac{\partial}{\partial z_k}\big|_p$ a holomorphic vector with coefficient vector $a = (a_1, \dots, a_n) \in \mathbb{C}^n$. The **Levi form** evaluated on $X_p$ is the Hermitian quadratic form
--   $$\mathcal{L}(X_p, X_p) = \sum_{k=1,\ell=1}^{n} \bar a_k a_\ell \left.\frac{\partial^2 r}{\partial \bar z_k \partial z_\ell}\right|_p .$$
--   The book uses it only for $X_p \in T^{(1,0)}_p \partial U$; on the whole of $T^{(1,0)}_p\mathbb{C}^n$ it would be the complex Hessian, which is a different object.
--
--   **Formalization Note.** `leviForm r p a` is the displayed sum as a complex number; for real $r$ it is real, and every statement of the mission uses its real part and restricts $a$ to `holTangent r p`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 66, Definition 2.3.5

import Mathlib
import Definitions.Def_LeblSCV_Levi_complexHessian

namespace LeblSCV.Levi

/-- The Levi form (Definition 2.3.5, Lebl, p. 66) of the defining function `r` at `p`, evaluated
on `X_p = ∑ a_k ∂/∂z_k|_p`: `𝓛(X_p, X_p) = ∑_{k,ℓ} ā_k a_ℓ ∂²r/∂z̄_k∂z_ℓ(p)`. It is only
meaningful for `a ∈ holTangent r p`; every statement restricts it there. -/
noncomputable def leviForm {n : ℕ} (r : (Fin n → ℂ) → ℝ) (p : Fin n → ℂ) (a : Fin n → ℂ) : ℂ :=
  ∑ k, ∑ l, (starRingEnd ℂ) (a k) * a l * complexHessian r p k l

end LeblSCV.Levi


