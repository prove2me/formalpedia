-- Prove2me | Definitions.Def_ConicQuadIPM_NewtonStep_Setting
-- name    : ConicQuadIPM_NewtonStep_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:08:58.472724+00:00
-- url     : https://prove2.me/theorems/8e2b2443-d83b-4a6a-9db4-d13154af2192
-- title:
--   Definition 3.2, mat(v), µ⁽⁰⁾ and the Newton system (22), pp. 8–12 — Tⁱ, the arrow-head matrix, e, µ⁽⁰⁾, block form of (22)
-- statement:
--   This module fixes the objects of §3–§4 of Andersen, Roos and Terlaky that enter the Newton step of their homogeneous primal-dual interior-point method for conic quadratic optimization.
--
--   **The cone product.** The cone is a product $K = K^1\times\cdots\times K^k$ of $k$ cones, each of one of three kinds: the half-line $\mathbb R_+$ (13), the quadratic cone $K^q$ (14) or the rotated quadratic cone $K^r$ (15). Block $i$ has dimension $n^i$, and a vector is partitioned accordingly, $x = (x^1;\dots;x^k)$ with $x^i\in\mathbb R^{n^i}$, so that $x^Ts = \sum_{i=1}^k (x^i)^Ts^i$. The dimensions obey the conventions implicit in the paper: $n^i = 1$ for $\mathbb R_+$, $n^i\ge 1$ for $K^q$ and $n^i\ge 2$ for $K^r$.
--
--   **The matrices $T^i$ (Definition 3.2).** $T^i = 1$ for $\mathbb R_+$, $T^i = I_{n^i}$ for the quadratic cone, and for the rotated quadratic cone
--   $$
--   T^i = \begin{bmatrix} 1/\sqrt2 & 1/\sqrt2 & 0\\ 1/\sqrt2 & -1/\sqrt2 & 0\\ 0 & 0 & I_{n^i-2}\end{bmatrix}.
--   $$
--
--   **The arrow-head matrix (p. 9).** For $v\in\mathbb R^d$,
--   $$
--   \operatorname{mat}(v) = \begin{bmatrix} v_1 & v_{2:d}^T\\ v_{2:d} & v_1 I\end{bmatrix},
--   $$
--   and $e^i\in\mathbb R^{n^i}$ is the first unit vector; $e = (e^1;\dots;e^k)$. At a point $(x,s)$ one writes $X^i = \operatorname{mat}(T^ix^i)$, $S^i = \operatorname{mat}(T^is^i)$, and $X$, $S$, $T$ for the block-diagonal matrices with blocks $X^i$, $S^i$, $T^i$.
--
--   **The quantity $\mu^{(0)}$ (p. 10).** For a point $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$,
--   $$
--   \mu^{(0)} = \frac{(x^{(0)})^Ts^{(0)} + \tau^{(0)}\kappa^{(0)}}{k+1}.
--   $$
--
--   **The Newton system (22) (p. 12).** Given data $A = [A^1\ \cdots\ A^k]\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c = (c^1;\dots;c^k)$, a point $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$ and a parameter $\gamma$, a direction $(d_x,d_\tau,d_y,d_s,d_\kappa)$ solves (22) when
--   $$
--   \begin{aligned}
--   A d_x - b d_\tau &= (\gamma-1)(Ax^{(0)} - b\tau^{(0)}),\\
--   A^Td_y + d_s - c d_\tau &= (\gamma-1)(A^Ty^{(0)} + s^{(0)} - c\tau^{(0)}),\\
--   -c^Td_x + b^Td_y - d_\kappa &= (\gamma-1)(-c^Tx^{(0)} + b^Ty^{(0)} - \kappa^{(0)}),\\
--   X^{(0)}Td_s + S^{(0)}Td_x &= -X^{(0)}S^{(0)}e + \gamma\mu^{(0)}e,\\
--   \tau^{(0)}d_\kappa + \kappa^{(0)}d_\tau &= -\tau^{(0)}\kappa^{(0)} + \gamma\mu^{(0)}.
--   \end{aligned}
--   $$
--
--   These definitions are the vocabulary of Lemma 4.1: the Newton direction of the homogeneous model reduces the three residuals and the complementarity gap by the same factor.
--
--   **Formalization Note** Indices are 0-based: the paper's $v_1$ is `v 0` and $v_2$ is `v 1`. Vectors in $K$ are stored block by block as `(i : Fin k) → Fin (n i) → ℝ`, and $A$ by its column blocks `A i`, so $Ax = \sum_i A^ix^i$, $(A^Ty)^i = (A^i)^Ty$ and $c^Tx = \sum_i (c^i)^Tx^i$. The second and fourth lines of (22) are stated block by block, which is equivalent because $X$, $S$ and $T$ are block diagonal. The third line of (22) is printed with $\kappa$ on the right-hand side; it is read as $\kappa^{(0)}$, since the system is linearized at the current point and Lemma 4.1's third identity needs $\kappa^{(0)}$. The dimension conventions are the predicate `WellFormed`; the cone membership predicates themselves are not needed for Lemma 4.1 and are not defined here. The denominator $k+1$ is the real number $k+1>0$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 7 Definition 3.1 (13)–(15), p. 8 Definition 3.2 (16)–(18), p. 9 mat(v) and eⁱ, p. 10 X, S, µ⁽⁰⁾, e, pp. 12–13 (22) and T

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

/-- `µ⁽⁰⁾ := ((x⁽⁰⁾)ᵀs⁽⁰⁾ + τ⁽⁰⁾κ⁽⁰⁾)/(k + 1)` (p. 10), with `xᵀs = ∑ᵢ (xⁱ)ᵀsⁱ` and `k`
the number of cones. -/
noncomputable def mu0 {k : ℕ} {n : Fin k → ℕ} (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) : ℝ :=
  ((∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0) / ((k : ℝ) + 1)

/-- The Newton system (22), p. 12, written block by block. The data are
`A = [A¹ ⋯ Aᵏ]` (column blocks `A i : ℝ^{m × nⁱ}`), `b ∈ ℝᵐ`, `c = (c¹; …; cᵏ)`; the current
point is `(x⁽⁰⁾, τ⁽⁰⁾, y⁽⁰⁾, s⁽⁰⁾, κ⁽⁰⁾)`, `γ` is the centering parameter and
`(d_x, d_τ, d_y, d_s, d_κ)` the direction. `Ax = ∑ᵢ Aⁱxⁱ`, `(Aᵀy)ⁱ = (Aⁱ)ᵀy`,
`cᵀx = ∑ᵢ (cⁱ)ᵀxⁱ`. The fourth line is `X⁽⁰⁾T d_s + S⁽⁰⁾T d_x = −X⁽⁰⁾S⁽⁰⁾e + γµ⁽⁰⁾e`
for the block-diagonal `X⁽⁰⁾ = diag(mat(Tⁱx⁽⁰⁾ⁱ))`, `S⁽⁰⁾ = diag(mat(Tⁱs⁽⁰⁾ⁱ))`,
`T = diag(Tⁱ)`, `e = (e¹; …; eᵏ)`, read block by block. The third line uses `κ⁽⁰⁾`
(the page prints `κ`). -/
def NewtonSystem {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ) : Prop :=
  -- A d_x − b d_τ = (γ − 1)(A x⁽⁰⁾ − b τ⁽⁰⁾)
  ((∑ i, A i *ᵥ dx i) - dτ • b = (γ - 1) • ((∑ i, A i *ᵥ x0 i) - τ0 • b)) ∧
  -- Aᵀ d_y + d_s − c d_τ = (γ − 1)(Aᵀ y⁽⁰⁾ + s⁽⁰⁾ − c τ⁽⁰⁾), block by block
  (∀ i, (A i)ᵀ *ᵥ dy + ds i - dτ • c i = (γ - 1) • ((A i)ᵀ *ᵥ y0 + s0 i - τ0 • c i)) ∧
  -- −cᵀ d_x + bᵀ d_y − d_κ = (γ − 1)(−cᵀ x⁽⁰⁾ + bᵀ y⁽⁰⁾ − κ⁽⁰⁾)
  (-(∑ i, c i ⬝ᵥ dx i) + b ⬝ᵥ dy - dκ =
      (γ - 1) * (-(∑ i, c i ⬝ᵥ x0 i) + b ⬝ᵥ y0 - κ0)) ∧
  -- X⁽⁰⁾ T d_s + S⁽⁰⁾ T d_x = −X⁽⁰⁾ S⁽⁰⁾ e + γ µ⁽⁰⁾ e, block by block
  (∀ i, ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ ds i) +
        ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ dx i) =
      -((ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x0 i) * ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s0 i)) *ᵥ ConicQuadIPM.Complementarity.e1) +
        (γ * mu0 x0 τ0 s0 κ0) • ConicQuadIPM.Complementarity.e1) ∧
  -- τ⁽⁰⁾ d_κ + κ⁽⁰⁾ d_τ = −τ⁽⁰⁾ κ⁽⁰⁾ + γ µ⁽⁰⁾
  (τ0 * dκ + κ0 * dτ = -(τ0 * κ0) + γ * mu0 x0 τ0 s0 κ0)

end ConicQuadIPM.NewtonStep


