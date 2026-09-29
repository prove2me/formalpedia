-- Prove2me | Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
-- name    : LovaszSchrijver_IntegerHull_MatrixCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:40:27.512602+00:00
-- url     : https://prove2.me/theorems/aad81cd1-552f-4d6e-bb57-6d97de06c302
-- title:
--   The matrix cones M(K₁, K₂), M₊(K₁, K₂), their projections N, N₊, and the iterates Nᵗ(K) (Sections 1.a–1.b)
-- statement:
--   Let $e_0$ be the 0th unit vector of $\mathbb R^{n+1}$. Following p. 169: "Let $K_1 \subseteq Q$ and $K_2 \subseteq Q$ be convex cones. We define the cone $M(K_1, K_2) \subseteq \mathbb R^{(n+1)\times(n+1)}$ consisting of all $(n+1)\times(n+1)$ matrices $Y = (y_{ij})$ satisfying (i), (ii), and (iii) below":
--
--   1. $Y$ is symmetric;
--   2. $\bar Y = Y e_0$, i.e., $y_{ii} = y_{0i}$ for all $1 \le i \le n$;
--   3. $u^{\mathsf T} Y v \ge 0$ holds for every $u \in K_1^*$ and $v \in K_2^*$.
--
--   The cone $M_+(K_1, K_2)$ consists of the matrices satisfying, in addition to (i)–(iii),
--
--   4. $Y$ is positive semidefinite.
--
--   The projections are
--   $$N(K_1, K_2) = \{Y e_0 : Y \in M(K_1, K_2)\}, \qquad N_+(K_1, K_2) = \{Y e_0 : Y \in M_+(K_1, K_2)\}.$$
--   "To simplify notation, we set $N(K) = N(K, Q)$" (p. 170), and "Define $N^t(K)$ recursively by $N^0(K) = K$ and $N^t(K) = N(N^{t-1}(K))$ for $t \ge 1$" (p. 171).
--
--   The operator $K \mapsto N(K)$ is the lift-and-project cut operator of the paper: it lifts a cone of $\mathbb R^{n+1}$ to a cone of matrices that behave like $xx^{\mathsf T}$ for 0–1 vectors $x$, and projects back to the diagonal (equivalently, by (ii), the 0th column).
--
--   **Formalization Note** Coordinates are indexed by `Option ι` (`none` = $x_0$), and $e_0$ is `Pi.single none 1`. Condition (iii) is stated through the polar cones exactly as on the page; the column forms (iii′) and (iii″) are consequences and are not used as the definition. The operators are defined on arbitrary sets of vectors, so the iterates need no closure proof; the hypotheses (convex cone, $K \subseteq Q$) appear in the theorems.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 169, Section 1.a, conditions (i)–(iv) and the definitions of N, N₊; p. 170, Section 1.a (N(K) = N(K, Q)); p. 171, Section 1.b (Nᵗ(K))

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic

namespace LovaszSchrijver.IntegerHull

open Matrix

/-- `M(K₁, K₂)` (p. 169): the symmetric `(n+1)×(n+1)` matrices `Y` with
(ii) `yᵢᵢ = y₀ᵢ` for `1 ≤ i ≤ n` and (iii) `uᵀYv ≥ 0` for every `u ∈ K₁*`, `v ∈ K₂*`. -/
def M {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y.IsSymm ∧ (∀ i : ι, Y (some i) (some i) = Y none (some i)) ∧
    ∀ u ∈ dualCone K₁, ∀ v ∈ dualCone K₂, 0 ≤ u ⬝ᵥ (Y *ᵥ v)}

/-- `M₊(K₁, K₂)` (p. 169): the matrices of `M(K₁, K₂)` that are (iv) positive semidefinite. -/
def Mplus {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y ∈ M K₁ K₂ ∧ Y.PosSemidef}

/-- `N(K₁, K₂) = {Ye₀ : Y ∈ M(K₁, K₂)}` (p. 169), `e₀ = Pi.single none 1`. -/
def N {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ M K₁ K₂, Y *ᵥ Pi.single none 1 = x}

/-- `N₊(K₁, K₂) = {Ye₀ : Y ∈ M₊(K₁, K₂)}` (p. 169). -/
def Nplus {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ Mplus K₁ K₂, Y *ᵥ Pi.single none 1 = x}

/-- `N(K) = N(K, Q)` (p. 170). -/
def N1 {ι : Type} [Fintype ι] [DecidableEq ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  N K Q

/-- The iterates `N⁰(K) = K`, `Nᵗ(K) = N(Nᵗ⁻¹(K))` (p. 171). -/
def Niter {ι : Type} [Fintype ι] [DecidableEq ι] : ℕ → Set (Option ι → ℝ) → Set (Option ι → ℝ)
  | 0, K => K
  | t + 1, K => N1 (Niter t K)

end LovaszSchrijver.IntegerHull


