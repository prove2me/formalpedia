-- Prove2me | Definitions.Def_LovaszSchrijver_NPlus_MatrixCone
-- name    : LovaszSchrijver_NPlus_MatrixCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:57:32.326088+00:00
-- url     : https://prove2.me/theorems/d999c05d-fe38-453b-9364-90005ba35db3
-- title:
--   Polar cone, the cube cone Q, the hyperplanes Gᵢ, the matrix cones M, M₊ and the operator N₊ with its iterates (Section 1.a)
-- statement:
--   Throughout, vectors live in $\mathbb R^{n+1}$ with coordinates $x_0, x_1, \dots, x_n$; "the 0th variable will play a special role throughout" (p. 168).
--
--   1. **Polar cone.** For a set $K \subseteq \mathbb R^{n+1}$, $K^* = \{u : u^{\mathsf T}x \ge 0 \text{ for all } x \in K\}$ (p. 168).
--   2. **Convex cone.** A nonempty set closed under addition and under multiplication by nonnegative scalars.
--   3. **The cube cone.** $Q$ is "the cone spanned by all 0–1 vectors $x \in \mathbb R^{n+1}$ with $x_0 = 1$" (p. 169), i.e. the set of all nonnegative combinations of these $2^n$ vectors.
--   4. **The hyperplanes** $G_i = \{x : x_i = x_0\}$ for $1 \le i \le n$ (p. 171).
--   5. **Matrix cones** (p. 169). For convex cones $K_1, K_2$, $M(K_1,K_2)$ is the set of $(n+1)\times(n+1)$ real matrices $Y = (y_{ij})$ such that
--      (i) $Y$ is symmetric;
--      (ii) $y_{ii} = y_{0i}$ for all $1 \le i \le n$;
--      (iii) $u^{\mathsf T} Y v \ge 0$ for every $u \in K_1^*$ and $v \in K_2^*$.
--      $M_+(K_1,K_2)$ consists of those $Y \in M(K_1,K_2)$ that are moreover (iv) positive semidefinite.
--   6. **Projections** (p. 169). With $e_0$ the 0th unit vector,
--   $$N_+(K_1,K_2) = \{Ye_0 : Y \in M_+(K_1,K_2)\}, \qquad N_+(K) = N_+(K, Q).$$
--   7. **Iterates** (p. 171): $N_+^0(K) = K$ and $N_+^t(K) = N_+(N_+^{t-1}(K))$.
--
--   These objects are the lift-and-project operator $N_+$ whose effect on the stable set problem the mission studies.
--
--   **Formalization Note** Coordinates are indexed by `Option ι` with `none` the 0th coordinate $x_0$ and `some i` the coordinate $x_i$, so $n = |\iota|$. Condition (iii) is used as the definition of $M$; its reformulations (iii′), (iii″) on pp. 169–170 are consequences. Only the $N_+$ side of the construction is defined here, since this mission does not use $N$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), pp. 168–171, Section 1.a

import Mathlib

namespace LovaszSchrijver.NPlus

open Matrix

/-- The paper's polar cone `K* = {u : uᵀx ≥ 0 for all x ∈ K}` (p. 168). Coordinates of
`ℝ^{n+1}` are indexed by `Option ι`; `none` is the 0th coordinate `x₀`. -/
def dualCone {ι : Type} [Fintype ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  {u | ∀ x ∈ K, 0 ≤ u ⬝ᵥ x}

/-- `K` is a convex cone: nonempty, closed under addition and under nonnegative scaling. -/
def IsConvexCone {ι : Type} (K : Set (Option ι → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧ ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K

/-- `cone S`: the convex cone spanned by `S` (all nonnegative combinations, `0` included). -/
def cone {ι : Type} (S : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  (PointedCone.hull ℝ S : Set (Option ι → ℝ))

/-- `x` is a 0–1 vector: every coordinate, `x₀` included, is `0` or `1`. -/
def IsZeroOne {ι : Type} (x : Option ι → ℝ) : Prop :=
  ∀ j, x j = 0 ∨ x j = 1

/-- `Q`: the cone spanned by all 0–1 vectors `x ∈ ℝ^{n+1}` with `x₀ = 1` (p. 169). -/
def Q {ι : Type} : Set (Option ι → ℝ) :=
  cone {x | IsZeroOne x ∧ x none = 1}

/-- The hyperplane `Gᵢ = {x : xᵢ = x₀}` (p. 171). -/
def G {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = x none}

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

/-- `N₊(K₁, K₂) = {Ye₀ : Y ∈ M₊(K₁, K₂)}` (p. 169), `e₀ = Pi.single none 1`. -/
def Nplus {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ Mplus K₁ K₂, Y *ᵥ Pi.single none 1 = x}

/-- `N₊(K) = N₊(K, Q)` (p. 170). -/
def N1plus {ι : Type} [Fintype ι] [DecidableEq ι] (K : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  Nplus K Q

/-- The iterates `N₊⁰(K) = K`, `N₊ᵗ(K) = N₊(N₊ᵗ⁻¹(K))` (p. 171, "and similarly for N₊"). -/
def NplusIter {ι : Type} [Fintype ι] [DecidableEq ι] :
    ℕ → Set (Option ι → ℝ) → Set (Option ι → ℝ)
  | 0, K => K
  | t + 1, K => N1plus (NplusIter t K)

end LovaszSchrijver.NPlus


