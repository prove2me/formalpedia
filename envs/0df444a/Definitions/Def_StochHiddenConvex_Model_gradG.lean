-- Prove2me | Definitions.Def_StochHiddenConvex_Model_gradG
-- name    : StochHiddenConvex_Model_gradG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:50.509621+00:00
-- url     : https://prove2.me/theorems/bf955a68-479d-4cb3-8837-ed45e40ca620
-- title:
--   Derivatives: $\nabla\phi$, $\nabla g$, $\nabla g(x)^\top v$ and the gradient formulas (4)–(5)
-- statement:
--   For the model of problem (1):
--
--   1. $\partial\phi_i(y,t)/\partial y$ is the $i$-th diagonal entry of $\nabla\phi(x,\xi)$ (two-sided derivative);
--   2. $g_i'(y)$ is the $i$-th diagonal entry of $\nabla g(x)$, the derivative of $g_i$ within $[\underline X_i,\bar X_i]$ (since $g:\mathcal X\to\mathcal U$);
--   3. $\nabla g(x)^\top v$ has coordinates $g_i'(x_i)\,v_i$;
--   4. the right side of (4), $\mathbb E_\xi[\nabla\phi(x,\xi)^\top\nabla f(\phi(x,\xi))]$, has coordinates $\mathbb E[\partial_i\phi_i(x_i,\xi_i)\,(\nabla f(\phi(x,\xi)))_i]$;
--   5. the right side of (5), $[\nabla g(g^{-1}(u))]^{-\top}\mathbb E_\xi[\nabla\phi(g^{-1}(u),\xi)^\top\nabla f(\phi(g^{-1}(u),\xi))]$, has coordinates $g_i'(g_i^{-1}(u_i))^{-1}$ times the $i$-th coordinate of item 4 at $g^{-1}(u)$.
--
--   Lemma 2.1 identifies items 4 and 5 with $\nabla F(x)$ and $\nabla G(u)$; the proof of Theorem 3.2 writes item 5 as $\nabla G(u^t)$.
--
--   **Formalization Note** Since $\phi$ is separable, all Jacobians are diagonal and are carried by their diagonal entries. The two-sided derivative of $\phi_i(\cdot,t)$ is $0$ where it does not exist; by Assumption 2.2(d) this happens only for a null set of samples.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Lemma 2.1 (4)–(5), p.10; Assumption 2.3, p.10; Eq. (29), p.39

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_G

open MeasureTheory

namespace StochHiddenConvex

namespace Model

variable {d : ℕ} (M : Model d)

/-- `∂ϕᵢ(y, t)/∂y`, the `i`-th diagonal entry of the Jacobian `∇ϕ(x, ξ)` of the separable random
function (Chen, He, Hu & Ye, arXiv:2205.01774v3, (4), p.10, and Algorithm 2, p.14).

**Formalization Note.** The two-sided `deriv`; it is `0` where `ϕᵢ(·, t)` is not differentiable,
which by Assumption 2.2(d) happens only on a null set of samples. -/
noncomputable def dphi (i : Fin d) (y t : ℝ) : ℝ := deriv (fun z => M.phi i z t) y

/-- `gᵢ′(y)`, the `i`-th diagonal entry of the Jacobian `∇g(x)` of `g : 𝒳 → 𝒰`
(arXiv:2205.01774v3, Assumption 2.3, p.10). Since `g` is separable, `∇g(x) = diag(gᵢ′(xᵢ))`.

**Formalization Note.** The derivative of `gᵢ` *within* `[X̲ᵢ, X̄ᵢ]`, because the paper's `g` maps
`𝒳` to `𝒰`; at a face it is the one-sided derivative. -/
noncomputable def dg (i : Fin d) (y : ℝ) : ℝ := derivWithin (M.gc i) (Set.Icc (M.lo i) (M.hi i)) y

/-- `∇g(x)ᵀ v`, the product of the (diagonal) transposed Jacobian of `g` at `x` with a vector `v`
(arXiv:2205.01774v3, (29), p.39). -/
noncomputable def gJacT (x v : Vec d) : Vec d := WithLp.toLp 2 (fun i => M.dg i (x i) * v i)

/-- The right side of (4), `𝔼_ξ[∇ϕ(x, ξ)ᵀ ∇f(ϕ(x, ξ))]` (arXiv:2205.01774v3, Lemma 2.1, p.10).
With `∇ϕ(x, ξ)` diagonal, its `i`-th coordinate is `𝔼[∂ϕᵢ(xᵢ, ξᵢ) · (∇f(ϕ(x, ξ)))ᵢ]`. -/
noncomputable def gradF (x : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => ∫ s, M.dphi i (x i) (s i) * (gradient M.f (M.phiVec x s)) i ∂M.P)

/-- The right side of (5), `[∇g(g⁻¹(u))]^{−⊤} 𝔼_ξ[∇ϕ(g⁻¹(u), ξ)ᵀ ∇f(ϕ(g⁻¹(u), ξ))]`
(arXiv:2205.01774v3, Lemma 2.1, p.10); with `∇g` diagonal its `i`-th coordinate is
`gᵢ′(gᵢ⁻¹(uᵢ))⁻¹ · (∇F(g⁻¹(u)))ᵢ`. The proof of Theorem 3.2 writes it `∇G(u)` (p.38). -/
noncomputable def gradG (u : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => (M.dg i (M.ginvC i (u i)))⁻¹ * M.gradF (M.ginv u) i)

end Model

end StochHiddenConvex


