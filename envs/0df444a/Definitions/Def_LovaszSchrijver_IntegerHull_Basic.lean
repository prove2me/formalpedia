-- Prove2me | Definitions.Def_LovaszSchrijver_IntegerHull_Basic
-- name    : LovaszSchrijver_IntegerHull_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:39:53.164209+00:00
-- url     : https://prove2.me/theorems/f0d43c82-d0d2-4a60-906f-84517c9c294c
-- title:
--   Polar cone K*, the cube cone Q, the 0–1 cone K°, the hyperplanes Hᵢ, Gᵢ and the face unions F̄ (Sections 1.a–1.b)
-- statement:
--   The objects of Section 1 of Lovász and Schrijver live in $\mathbb R^{n+1}$, whose coordinates are $x_0, x_1, \dots, x_n$; "the 0th variable will play a special role throughout" (p. 168), since $\mathbb R^n$ is embedded as the hyperplane $x_0 = 1$.
--
--   1. **Polar cone** (p. 168). "Let $K$ be a convex cone in $\mathbb R^{n+1}$. Let $K^*$ be its polar cone, i.e., the cone defined by
--   $$K^* = \{u \in \mathbb R^{n+1} : u^{\mathsf T}x \ge 0 \text{ for all } x \in K\}."$$
--   2. **Convex cone.** A set $K \subseteq \mathbb R^{n+1}$ is a convex cone if it is nonempty and closed under addition and under multiplication by nonnegative scalars.
--   3. **Cone spanned by a set.** For $S \subseteq \mathbb R^{n+1}$, $\operatorname{cone}(S)$ is the set of all nonnegative linear combinations of finitely many vectors of $S$ (it contains $0$).
--   4. **0–1 vectors, $Q$ and $K^\circ$** (p. 169). A 0–1 vector is a vector all of whose coordinates, $x_0$ included, are $0$ or $1$. "We denote by $K^\circ$ the cone spanned by all 0–1 vectors in $K$. Let $Q$ denote the cone spanned by all 0–1 vectors $x \in \mathbb R^{n+1}$ with $x_0 = 1$." Thus
--   $$Q = \operatorname{cone}\{x \in \{0,1\}^{n+1} : x_0 = 1\}, \qquad K^\circ = \operatorname{cone}(K \cap \{0,1\}^{n+1}).$$
--   5. **Hyperplanes** (p. 171). "Let $H_i = \{x \in \mathbb R^{n+1} : x_i = 0\}$ and $G_i = \{x \in \mathbb R^{n+1} : x_i = x_0\}$", for $1 \le i \le n$.
--   6. **Unions of parallel cube faces** (proof of Theorem 1.4, pp. 171–172). The unit cube $Q'$ is $\{x : x_0 = 1,\ 0 \le x_i \le 1 \ (1 \le i \le n)\}$. A face $F$ of $Q'$ of dimension $n - t$ fixes a set $T$ of $t$ coordinates to values $0$ or $1$; the union $\bar F$ of the faces of $Q'$ parallel to $F$ depends only on $T$:
--   $$\bar F_T = \{x : x_0 = 1,\ 0 \le x_i \le 1 \text{ for all } i,\ x_i \in \{0,1\} \text{ for all } i \in T\}.$$
--
--   These are the basic objects of the lift-and-project construction: $Q$ is the homogenized unit cube, $K^\circ$ is the homogenized 0–1 hull the method approximates, and $H_i$, $G_i$ are the hyperplanes through the two opposite facets of $Q$ in direction $i$.
--
--   **Formalization Note** Coordinates of $\mathbb R^{n+1}$ are indexed by `Option ι` for a finite type `ι` with $n = |ι|$; `none` is the 0th coordinate $x_0$ and `some i` is $x_i$. $\operatorname{cone}(S)$ is Mathlib's `PointedCone.hull ℝ S` (the span over nonnegative reals). The paper's printed text places $Q'$ in the hyperplane "$x_0 = 0$"; this is a misprint for $x_0 = 1$ (the cube's vertices are the 0–1 vectors with $x_0 = 1$, and at $x_0 = 0$ the set $K \cap \bar F$ would be $\{0\}$ for every $K \subseteq Q$).
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 168, Section 1.a (polar cone); p. 169, Section 1.a (K°, Q); p. 171, Section 1.b (Hᵢ, Gᵢ); pp. 171–172, proof of Theorem 1.4 (Q′, F, F̄)

import Mathlib

namespace LovaszSchrijver.IntegerHull

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

/-- `K°`: the cone spanned by all 0–1 vectors in `K` (p. 169). -/
def hull01 {ι : Type} (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  cone {x | x ∈ K ∧ IsZeroOne x}

/-- The hyperplane `Hᵢ = {x : xᵢ = 0}` (p. 171). -/
def H {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = 0}

/-- The hyperplane `Gᵢ = {x : xᵢ = x₀}` (p. 171). -/
def G {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = x none}

/-- `F̄` for a set `T` of `t` coordinates (proof of Theorem 1.4, pp. 171–172): the union of the
faces of the unit cube `{x : x₀ = 1, 0 ≤ xᵢ ≤ 1}` that fix the coordinates in `T` to `0` or `1`,
i.e. the cube points whose coordinates in `T` are all `0` or `1`. -/
def Fbar {ι : Type} (T : Finset ι) : Set (Option ι → ℝ) :=
  {x | x none = 1 ∧ (∀ i : ι, 0 ≤ x (some i) ∧ x (some i) ≤ 1) ∧
    ∀ i ∈ T, x (some i) = 0 ∨ x (some i) = 1}

end LovaszSchrijver.IntegerHull


