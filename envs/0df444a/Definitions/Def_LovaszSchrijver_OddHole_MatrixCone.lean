-- Prove2me | Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
-- name    : LovaszSchrijver_OddHole_MatrixCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:44:22.050397+00:00
-- url     : https://prove2.me/theorems/35d3f6e3-e63e-4449-a00d-9bcdb688ac1e
-- title:
--   Convex cones, polar cones, the cone Q, the matrix cone M(K₁, K₂) and its projections N(K₁, K₂), N(K) (Section 1.a)
-- statement:
--   Lovász and Schrijver embed $\mathbb{R}^n$ in $\mathbb{R}^{n+1}$ as the hyperplane $x_0 = 1$; "the 0th variable will play a special role throughout" (p. 168). Coordinates of $\mathbb{R}^{n+1}$ are indexed by $\{0\} \cup \{1, \dots, n\}$.
--
--   1. A **convex cone** is a nonempty set $K \subseteq \mathbb{R}^{n+1}$ closed under addition and under multiplication by nonnegative scalars.
--   2. The **polar cone** of $K$ (p. 168) is
--   $$K^* = \{u \in \mathbb{R}^{n+1} : u^{\mathsf T} x \ge 0 \text{ for all } x \in K\}.$$
--   3. $Q$ is "the cone spanned by all 0–1 vectors $x \in \mathbb{R}^{n+1}$ with $x_0 = 1$" (p. 169): the set of nonnegative combinations of such vectors.
--   4. For convex cones $K_1, K_2 \subseteq Q$, the cone $M(K_1, K_2)$ (p. 169) consists of all $(n+1)\times(n+1)$ matrices $Y = (y_{ij})$ satisfying
--      (i) $Y$ is symmetric;
--      (ii) $y_{ii} = y_{0i}$ for all $1 \le i \le n$;
--      (iii) $u^{\mathsf T} Y v \ge 0$ for every $u \in K_1^*$ and $v \in K_2^*$.
--   5. Its projection is $N(K_1, K_2) = \{Y e_0 : Y \in M(K_1, K_2)\}$, where $e_0$ is the 0th unit vector, and $N(K) = N(K, Q)$ (p. 170).
--
--   These objects are the lift-and-project operator of the paper: $N(K)$ is a convex cone between the cone spanned by the 0–1 vectors of $K$ and $K$ itself.
--
--   **Formalization Note** Coordinates are indexed by `Option ι` for a finite type `ι` with $n = |\iota|$: `none` is the coordinate $x_0$ and `some i` is $x_i$. Condition (iii) is the definition; the rewritings (iii′) and (iii″) of the paper are consequences, not definitions. The inclusions $K_1, K_2 \subseteq Q$ are not built into the definition; they are hypotheses of the theorems that use it.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), pp. 168–170, Section 1.a

import Mathlib

namespace LovaszSchrijver.OddHole

/-- A convex cone: a nonempty set closed under addition and under nonnegative scaling
(so it contains `0`). -/
def IsConvexCone {E : Type} [AddCommMonoid E] [SMul ℝ E] (K : Set E) : Prop :=
  K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧ ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K

/-- The polar (dual) cone `K* = {u : uᵀx ≥ 0 for all x ∈ K}` (p. 168). Coordinates of
`ℝ^{n+1}` are indexed by `Option ι`, with `none` the special 0th coordinate. -/
def dualCone {ι : Type} [Fintype ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  {u | ∀ x ∈ K, 0 ≤ dotProduct u x}

/-- `Q`: the cone spanned by all 0–1 vectors `x ∈ ℝ^{n+1}` with `x₀ = 1` (p. 169). -/
def Q (ι : Type) : Set (Option ι → ℝ) :=
  (PointedCone.hull ℝ {x : Option ι → ℝ | x none = 1 ∧ ∀ i : ι, x (some i) = 0 ∨ x (some i) = 1} :
    Set (Option ι → ℝ))

/-- The matrix cone `M(K₁, K₂)` (p. 169): the `(n+1) × (n+1)` matrices `Y` with
(i) `Y` symmetric, (ii) `yᵢᵢ = y₀ᵢ` for all `1 ≤ i ≤ n`, (iii) `uᵀYv ≥ 0` for every
`u ∈ K₁*` and `v ∈ K₂*`. -/
def M {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y.IsSymm ∧ (∀ i : ι, Y (some i) (some i) = Y none (some i)) ∧
    ∀ u ∈ dualCone K₁, ∀ v ∈ dualCone K₂, 0 ≤ dotProduct u (Y.mulVec v)}

/-- The projection `N(K₁, K₂) = {Y e₀ : Y ∈ M(K₁, K₂)}` (p. 169). -/
def Npair {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ M K₁ K₂, Y.mulVec (Pi.single none 1 : Option ι → ℝ) = x}

/-- `N(K) = N(K, Q)` (p. 170). -/
def N {ι : Type} [Fintype ι] [DecidableEq ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  Npair K (Q ι)

end LovaszSchrijver.OddHole


