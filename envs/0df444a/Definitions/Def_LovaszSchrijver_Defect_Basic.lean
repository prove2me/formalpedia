-- Prove2me | Definitions.Def_LovaszSchrijver_Defect_Basic
-- name    : LovaszSchrijver_Defect_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:51:01.675141+00:00
-- url     : https://prove2.me/theorems/b15b5247-0973-48dc-9571-01c00f76a2b6
-- title:
--   Polar cone K*, convex cones, the cone spanned by a set, and the cube cone Q (Section 1.a)
-- statement:
--   The objects of Section 1 of Lovász and Schrijver live in $\mathbb R^{n+1}$, with coordinates $x_0, x_1, \dots, x_n$; "the 0th variable will play a special role throughout" (p. 168).
--
--   1. **Polar cone** (p. 168). For a convex cone $K \subseteq \mathbb R^{n+1}$, "let $K^*$ be its polar cone, i.e., the cone defined by
--   $$K^* = \{u \in \mathbb R^{n+1} : u^{\mathsf T}x \ge 0 \text{ for all } x \in K\}."$$
--   2. **Convex cone.** A set $K \subseteq \mathbb R^{n+1}$ is a convex cone if it is nonempty and closed under addition and under multiplication by nonnegative scalars.
--   3. **Cone spanned by a set.** For $S \subseteq \mathbb R^{n+1}$, $\operatorname{cone}(S)$ is the set of all nonnegative linear combinations of finitely many vectors of $S$ (it contains $0$).
--   4. **0–1 vectors and $Q$** (p. 169). A 0–1 vector is a vector all of whose coordinates, $x_0$ included, are $0$ or $1$. "Let $Q$ denote the cone spanned by all 0–1 vectors $x \in \mathbb R^{n+1}$ with $x_0 = 1$":
--   $$Q = \operatorname{cone}\{x \in \{0,1\}^{n+1} : x_0 = 1\}.$$
--
--   $Q$ is the homogenized unit cube; the operator $N$ of Section 1 is defined relative to it.
--
--   **Formalization Note** Coordinates of $\mathbb R^{n+1}$ are indexed by `Option ι` for a finite type `ι` with $n = |ι|$; `none` is the 0th coordinate $x_0$ and `some i` is $x_i$. $\operatorname{cone}(S)$ is Mathlib's `PointedCone.hull ℝ S`. These definitions have the same shapes and names as those of the other missions of this series (sub-namespaces `IntegerHull`, `OddHole`, `NPlus`).
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 168, Section 1.a (polar cone); p. 169, Section 1.a (Q)

import Mathlib

namespace LovaszSchrijver.Defect

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

end LovaszSchrijver.Defect


