-- Prove2me | Definitions.Def_ProxADMMLC_Conv_EpsSolution
-- name    : ProxADMMLC_Conv_EpsSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:37.266593+00:00
-- url     : https://prove2.me/theorems/c035c93d-92f2-4217-a09b-3def6130d673
-- title:
--   Definition 4.1, p. 2289 — ε-solution of (1.1): ‖Ax − b‖ ≤ ε and some v ∈ ∇f(x) + Aᵀy + ∂ι(x) with ‖v‖ ≤ ε
-- statement:
--   Let $\iota$ be the indicator function of the box $P=\{x:\ell_i\le x_i\le u_i\}$, so $\iota(x)=0$ for $x\in P$ and $\iota(x)=+\infty$ otherwise. Its subdifferential at $x\in P$ is the normal cone
--   $$\partial\iota(x)=\{w\in\mathbb R^n:\ \langle w,x'-x\rangle\le0\ \text{ for all } x'\in P\},$$
--   and $\partial\iota(x)=\emptyset$ for $x\notin P$.
--
--   **Definition 4.1.** A pair $(x,y)\in\mathbb R^n\times\mathbb R^m$ is an **$\varepsilon$-solution** of (1.1) if $\|Ax-b\|\le\varepsilon$ and there is a vector
--   $$v\in\nabla f(x)+A^\top y+\partial\iota(x)\qquad\text{with}\qquad \|v\|\le\varepsilon.$$
--
--   An $\varepsilon$-solution is an approximate KKT pair: at $\varepsilon=0$ it is exactly a primal-dual stationary pair of (1.1). The definition measures the iteration complexity of Theorem 4.2.
--
--   **Formalization Note** The membership $v\in\nabla f(x)+A^\top y+\partial\iota(x)$ is written as $v-(\nabla f(x)+A^\top y)\in\partial\iota(x)$, with $\partial\iota(x)$ the normal cone of the box (empty off $P$), so an $\varepsilon$-solution always has $x\in P$.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), pp. 2288–2289, ι (§4.1) and Definition 4.1

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

/-- `∂ι(x)`, p. 2288: the subdifferential of the indicator function `ι` of the box `P` at `x`,
i.e. the normal cone `{w | ⟨w, x' − x⟩ ≤ 0 ∀ x' ∈ P}` when `x ∈ P`, and the empty set when
`x ∉ P` (where `ι(x) = ∞`). -/
def normalConeBox {n : ℕ} (ℓ u : Fin n → ℝ) (x : E n) : Set (E n) :=
  {w | x ∈ box ℓ u ∧ ∀ x' ∈ box ℓ u, inner ℝ w (x' - x) ≤ 0}

/-- Definition 4.1, p. 2289: `(x, y)` is an `ε`-solution of (1.1) if `‖Ax − b‖ ≤ ε` and there is
a vector `v ∈ ∇f(x) + Aᵀy + ∂ι(x)` with `‖v‖ ≤ ε`. -/
def IsEpsSolution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (x : E n) (y : E m) (ε : ℝ) : Prop :=
  ‖A x - b‖ ≤ ε ∧
    ∃ v : E n, v - (gradient f x + (ContinuousLinearMap.adjoint A) y) ∈ normalConeBox ℓ u x ∧
      ‖v‖ ≤ ε

end ProxADMMLC.Conv


