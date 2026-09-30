-- Prove2me | Definitions.Def_PolyhedralSOC_LowerBound_ProofObjects
-- name    : PolyhedralSOC_LowerBound_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:45:30.898102+00:00
-- url     : https://prove2.me/theorems/963a5a96-b416-4dc6-90d9-3c93324c6b52
-- title:
--   The cone $K=\{\Pi\ge0\}$, line-freeness, and the slice $G$
-- statement:
--   Let $\Pi:\mathbb R^k\times\mathbb R\times\mathbb R^p\to\mathbb R^q$ be a linear map. Three objects from the proof of Proposition 3.1 are defined.
--   1. The **polyhedral cone** $K=\{(y,t,u)\mid \Pi(y,t,u)\ge 0\}$ (componentwise inequality).
--   2. $K$ **does not contain lines** if $z\in K$ and $-z\in K$ imply $z=0$.
--   3. The **slice** of the projection $\widehat L^k$ of $K$ onto the $(y,t)$-space at height $t=1$:
--   $$G=\{y\in\mathbb R^k \mid (y,1)\in\widehat L^k\}=\{y\in\mathbb R^k\mid \Pi(y,1,u)\ge 0\ \text{for some } u\in\mathbb R^p\}.$$
--
--   These are the objects the lower-bound argument reasons about: the extreme rays of a line-free $K$ are counted, and $G$ is compared with Euclidean balls.
--
--   **Formalization Note** A convex cone contains a line exactly when it contains a pair $\pm z$ with $z\ne0$, which is the form used.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, proof of Proposition 3.1 (the cone K, "does not contain lines", the set G)

import Mathlib

namespace PolyhedralSOC.LowerBound

/-- The polyhedral cone `K = {(y, t, u) | Π(y, t, u) ≥ 0}` of a linear map `Π`
(Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), proof of Proposition 3.1, p. 202 (PDF p. 10)).
`≥ 0` is componentwise. -/
def coneK {k p q : ℕ} (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)) :
    Set ((Fin k → ℝ) × ℝ × (Fin p → ℝ)) :=
  {z | 0 ≤ P z}

/-- The cone `K = {z | Π z ≥ 0}` "does not contain lines" (Ben-Tal & Nemirovski 2001,
proof of Proposition 3.1, p. 202 (PDF p. 10)): if both `z` and `−z` lie in `K`, then
`z = 0`. (A convex cone contains a line iff it contains some `±z` with `z ≠ 0`.) -/
def IsLineFree {k p q : ℕ} (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)) : Prop :=
  ∀ z, z ∈ coneK P → -z ∈ coneK P → z = 0

/-- The set `G = {y | (y, 1) ∈ L̂^k}` of the proof of Proposition 3.1
(Ben-Tal & Nemirovski 2001, p. 202 (PDF p. 10)), where `L̂^k` is the projection of
`K = {(y, t, u) | Π(y, t, u) ≥ 0}` onto the `(y, t)`-space; that is,
`G = {y ∈ ℝ^k | Π(y, 1, u) ≥ 0 for some u ∈ ℝ^p}`. -/
def sliceG {k p q : ℕ} (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)) :
    Set (Fin k → ℝ) :=
  {y | ∃ u : Fin p → ℝ, 0 ≤ P (y, 1, u)}

end PolyhedralSOC.LowerBound


