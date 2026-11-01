-- Prove2me | Definitions.Def_StochCoordProx_IsCurvBound
-- name    : StochCoordProx_IsCurvBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:21.295984+00:00
-- url     : https://prove2.me/theorems/f29eb990-25b1-4461-b84f-7f2c8c392bb3
-- title:
--   $B$ bounds $H_{F,U}$ (18)
-- statement:
--   Let $F=f+\psi$, $x_0\in\mathbb R^n$ and $\mathcal L_F(x_0)=\{x: F(x)\le F(x_0)\}$. For $U\in\mathbb R^{n\times p}$ and $H\in\mathbb R$ (the step parameter $H_{f,U}$), a number $B$ **bounds $H_{F,U}$** if
--
--   $$
--   \|U^T\bar\nabla^2\Psi(z_1,\dots,z_n)U+H\,I_{p\times p}\|_F\le B\qquad\text{for all }z_1,\dots,z_n\in\operatorname{conv}(\mathcal L_F(x_0)),
--   $$
--
--   where $\|\cdot\|_F$ is the Frobenius norm. The paper defines
--
--   $$
--   H_{F,U}=\max_{z_1,\dots,z_n\in\operatorname{conv}(\mathcal L_F(x_0))}\|U^T\bar\nabla^2\Psi(z_1,\dots,z_n)U+H_{f,U}I_{p\times p}\|_F,
--   $$
--
--   so "$H_{F,U}\le B$" is exactly this predicate. $H_{F,U}$ is the curvature constant that enters the rate of Theorem 1.
--
--   **Formalization Note** $H_{F,U}$ is not defined as a supremum, because a real supremum of an unbounded set is $0$ in Lean. Every use is a bound $B$. The Frobenius norm is the published `LowRankMEG.frobNorm`, $\|A\|_F=(\sum_{i,j}A_{ij}^2)^{1/2}$. The paper writes "$\mathcal L_f(x_0)$" after (18); this is read as $\mathcal L_F(x_0)$, the only sublevel set it defines.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, display (18), p.10; sublevel set 𝓛_F(x₀), p.7

import Mathlib
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_StochCoordProx_hessRows

open Matrix

namespace StochCoordProx

/-- **`B` bounds `H_{F,U}`** (display (18)): for all points `z₁, …, zₙ` of the convex hull of the
sublevel set `𝓛_F(x₀) = {x : F(x) ≤ F(x₀)}`, `F = f + ψ`,
`‖Uᵀ ∇̄²Ψ(z₁, …, zₙ) U + H I_{p×p}‖_F ≤ B`.
The paper's `H_{F,U}` is the maximum of the left side over these points, so `H_{F,U} ≤ B` is
exactly this predicate; the paper's `H_{F,U}` itself is the least such `B`.

Necoara & Chorobura, arXiv:2104.13370v3, display (18), p.10; the sublevel set `𝓛_F(x₀)`, p.7.

**Formalization Note.** `H_{F,U}` is not defined as a supremum (a real `sSup` of an unbounded
set is `0`); every use is stated as a bound `B`. `‖·‖_F` is the Frobenius norm
`LowRankMEG.frobNorm A = √(∑ᵢ ∑ⱼ A_{ij}²)`. `H` is the step parameter `H_{f,U}` of
Algorithm 1. The paper's "𝓛_f(x₀)" on p.10 is read as `𝓛_F(x₀)`, the only sublevel set it
defines. -/
def IsCurvBound {n p : ℕ} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Matrix (Fin n) (Fin p) ℝ) (H B : ℝ) : Prop :=
  ∀ z : Fin n → EuclideanSpace ℝ (Fin n),
    (∀ i, z i ∈ convexHull ℝ {y : EuclideanSpace ℝ (Fin n) | f y + ψ y ≤ f x₀ + ψ x₀}) →
      LowRankMEG.frobNorm (Uᵀ * hessRows ψ z * U + H • (1 : Matrix (Fin p) (Fin p) ℝ)) ≤ B

end StochCoordProx


