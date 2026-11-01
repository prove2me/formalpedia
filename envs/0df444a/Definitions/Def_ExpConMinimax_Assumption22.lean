-- Prove2me | Definitions.Def_ExpConMinimax_Assumption22
-- name    : ExpConMinimax_Assumption22
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:50.10075+00:00
-- url     : https://prove2.me/theorems/c2dfa714-a016-4e92-b287-e3a7e845d8b5
-- title:
--   Assumption 2.2 — Lipschitz constraints, unbiased samples with bounded second moments and variances
-- statement:
--   Let $C_h,\sigma_h,C_g,\sigma_g>0$. **Assumption 2.2** requires:
--
--   1. $\|H(x_1)-H(x_2)\|\le C_h\|x_1-x_2\|$ on $\mathcal X$; for every $x\in\mathcal X$, $\mathbb E[\widetilde\nabla h(x,\xi)]=\widetilde\nabla H(x)\in\partial H(x)$, $\mathbb E\|\widetilde\nabla h(x,\xi)\|^2\le C_h^2$, $\mathbb E[h(x,\xi)]=H(x)$ and $\mathbb E\|h(x,\xi)-H(x)\|^2\le\sigma_h^2$;
--   2. $\|G(y_1)-G(y_2)\|\le C_g\|y_1-y_2\|$ on $\mathcal Y$; for every $y\in\mathcal Y$, $\mathbb E[\widetilde\nabla g(y,\zeta)]=\widetilde\nabla G(y)\in\partial G(y)$, $\mathbb E\|\widetilde\nabla g(y,\zeta)\|^2\le C_g^2$, $\mathbb E[g(y,\zeta)]=G(y)$ and $\mathbb E\|g(y,\zeta)-G(y)\|^2\le\sigma_g^2$.
--
--   **Formalization Note** $P_\xi,P_\zeta$ are probability measures. "$\widetilde\nabla H(x)\in\partial H(x)$" means that the $i$-th column of the mean Jacobian is a subgradient of the convex $H_i$ at $x$ relative to $\mathcal X$ (likewise for $G$). The Jacobian norm is the operator norm (at most the Frobenius norm). Finite second moments are stated as square integrability.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Assumption 2.2, p.9

import Mathlib
import Definitions.Def_ExpConMinimax_Problem
import Definitions.Def_ExpConMinimax_Oracle
import Definitions.Def_ExpConMinimax_IsSubgradOn

namespace ExpConMinimax

open MeasureTheory

/-- **Assumption 2.2** (constraints).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Assumption 2.2, p.9:

"Let `C_h, σ_h, C_g, σ_g` be positive scalars. Then functions `g` and `h` satisfy
1. The function `H` is Lipschitz continuous such that `‖H(x₁) − H(x₂)‖ ≤ C_h‖x₁ − x₂‖,
   ∀x₁,x₂ ∈ X`. For any `x ∈ X`, the sampled sub-gradient `∇̃h(x,ξ)` is unbiased and preserves
   bounded second moments such that `E[∇̃h(x,ξ)] = ∇̃H(x) ∈ ∂H(x)`, and
   `E[‖∇̃h(x,ξ)‖²] ≤ C_h²`. Moreover, the sampled value `h(x,ξ)` is unbiased and preserves
   bounded variance such that `E[h(x,ξ)] = H(x)`, and `E[‖h(x,ξ) − H(x)‖²] ≤ σ_h²`.
2. The function `G` is Lipschitz continuous such that `‖G(y₁) − G(y₂)‖ ≤ C_g‖y₁ − y₂‖,
   ∀y₁,y₂ ∈ Y`. For any `y ∈ Y`, the sampled sub-gradient `∇̃g(y,ζ)` is unbiased and preserves
   bounded second moments such that `E[∇̃g(y,ζ)] = ∇̃G(y) ∈ ∂G(y)`, and
   `E[‖∇̃g(y,ζ)‖²] ≤ C_g²`. The sampled value `g(y,ζ)` is unbiased and preserves bounded
   variance such that `E[g(y,ζ)] = G(y)`, and `E[‖g(y,ζ) − G(y)‖²] ≤ σ_g²`."

**Formalization Note.** `μξ`, `μζ` are probability measures. "`∇̃H(x) ∈ ∂H(x)`" means: for
every `i`, the `i`-th column `∇̃Hᵢ(x)` of the mean Jacobian `Oracle.meanGhs x` is a subgradient
of the convex function `Hᵢ` at `x` relative to `X`; likewise for `G` on `Y`. The norm of the
sampled Jacobian is the operator norm (the paper does not name a matrix norm; the operator
norm is at most the Frobenius norm, so this is the weaker reading of the bound). Finite
second moments are encoded as `MemLp · 2`. -/
def Assumption22 {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω]
    [MeasurableSpace Sξ] [MeasurableSpace Sζ] (P : Problem dx dy m₁ m₂)
    (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (Ch σh Cg σg : ℝ) : Prop :=
  0 < Ch ∧ 0 < σh ∧ 0 < Cg ∧ 0 < σg ∧
  IsProbabilityMeasure O.μξ ∧ IsProbabilityMeasure O.μζ ∧
  (∀ x₁ ∈ P.X, ∀ x₂ ∈ P.X, ‖P.H x₁ - P.H x₂‖ ≤ Ch * ‖x₁ - x₂‖) ∧
  (∀ x ∈ P.X,
    MemLp (O.ghs x) 2 O.μξ ∧
    (∀ i, IsSubgradOn (fun x' => P.H x' i) P.X x (O.meanGhs x (EuclideanSpace.single i 1))) ∧
    ∫ s, ‖O.ghs x s‖ ^ 2 ∂O.μξ ≤ Ch ^ 2 ∧
    MemLp (O.hs x) 2 O.μξ ∧
    ∫ s, O.hs x s ∂O.μξ = P.H x ∧
    ∫ s, ‖O.hs x s - P.H x‖ ^ 2 ∂O.μξ ≤ σh ^ 2) ∧
  (∀ y₁ ∈ P.Y, ∀ y₂ ∈ P.Y, ‖P.G y₁ - P.G y₂‖ ≤ Cg * ‖y₁ - y₂‖) ∧
  (∀ y ∈ P.Y,
    MemLp (O.ggs y) 2 O.μζ ∧
    (∀ j, IsSubgradOn (fun y' => P.G y' j) P.Y y (O.meanGgs y (EuclideanSpace.single j 1))) ∧
    ∫ s, ‖O.ggs y s‖ ^ 2 ∂O.μζ ≤ Cg ^ 2 ∧
    MemLp (O.gs y) 2 O.μζ ∧
    ∫ s, O.gs y s ∂O.μζ = P.G y ∧
    ∫ s, ‖O.gs y s - P.G y‖ ^ 2 ∂O.μζ ≤ σg ^ 2)

end ExpConMinimax


