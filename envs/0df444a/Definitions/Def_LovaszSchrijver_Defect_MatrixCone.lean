-- Prove2me | Definitions.Def_LovaszSchrijver_Defect_MatrixCone
-- name    : LovaszSchrijver_Defect_MatrixCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:51:34.660614+00:00
-- url     : https://prove2.me/theorems/d9b0ee8b-b494-4c0e-a7cb-3e4f9a6b2546
-- title:
--   The matrix cone M(K₁, K₂), its projection N(K₁, K₂), N(K) = N(K, Q) and the iterates Nᵗ(K) (Sections 1.a–1.b)
-- statement:
--   Let $K_1, K_2 \subseteq \mathbb R^{n+1}$ be convex cones, with polar cones $K_1^*, K_2^*$, and let $e_0$ be the 0th unit vector.
--
--   1. **The matrix cone** (p. 169). $M(K_1, K_2)$ is the set of $(n+1)\times(n+1)$ real matrices $Y = (y_{ij})$ such that
--      (i) $Y$ is symmetric;
--      (ii) $y_{ii} = y_{0i}$ for all $1 \le i \le n$;
--      (iii) $u^{\mathsf T} Y v \ge 0$ for every $u \in K_1^*$ and $v \in K_2^*$.
--   2. **Projection** (p. 169). $N(K_1, K_2) = \{Y e_0 : Y \in M(K_1, K_2)\}$.
--   3. **The operator $N$** (p. 170). $N(K) = N(K, Q)$, where $Q$ is the cube cone.
--   4. **Iterates** (p. 171). "$N^0(K) = K$ and $N^t(K) = N(N^{t-1}(K))$."
--
--   $N$ is the Lovász–Schrijver lift-and-project operator: $N(K)$ is a convex cone between $K^\circ$ (the cone of 0–1 vectors of $K$) and $K$, and its iterates are the successive relaxations whose depth this mission measures.
--
--   **Formalization Note** Coordinates are indexed by `Option ι` (`none` = $x_0$), $e_0$ is `Pi.single none 1`, and $Y$ is a `Matrix (Option ι) (Option ι) ℝ`. $M$ is defined by condition (iii) itself, not by the reformulations (iii′), (iii″) of p. 169–170. The iterate $N^t$ is a structural recursion on $t$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 169, Section 1.a (M, N); p. 170, Section 1.a (N(K)); p. 171, Section 1.b (iterates)

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Basic

namespace LovaszSchrijver.Defect

open Matrix

/-- `M(K₁, K₂)` (p. 169): the symmetric `(n+1)×(n+1)` matrices `Y` with
(ii) `yᵢᵢ = y₀ᵢ` for `1 ≤ i ≤ n` and (iii) `uᵀYv ≥ 0` for every `u ∈ K₁*`, `v ∈ K₂*`. -/
def M {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y.IsSymm ∧ (∀ i : ι, Y (some i) (some i) = Y none (some i)) ∧
    ∀ u ∈ dualCone K₁, ∀ v ∈ dualCone K₂, 0 ≤ u ⬝ᵥ (Y *ᵥ v)}

/-- `N(K₁, K₂) = {Ye₀ : Y ∈ M(K₁, K₂)}` (p. 169), `e₀ = Pi.single none 1`. -/
def N {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ M K₁ K₂, Y *ᵥ Pi.single none 1 = x}

/-- `N(K) = N(K, Q)` (p. 170). -/
def N1 {ι : Type} [Fintype ι] [DecidableEq ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  N K Q

/-- The iterates `N⁰(K) = K`, `Nᵗ(K) = N(Nᵗ⁻¹(K))` (p. 171). -/
def Niter {ι : Type} [Fintype ι] [DecidableEq ι] : ℕ → Set (Option ι → ℝ) → Set (Option ι → ℝ)
  | 0, K => K
  | t + 1, K => N1 (Niter t K)

end LovaszSchrijver.Defect


