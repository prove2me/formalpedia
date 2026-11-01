-- Prove2me | Definitions.Def_SConvexGS_IsGS
-- name    : SConvexGS_IsGS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:14.489654+00:00
-- url     : https://prove2.me/theorems/2aa2608b-eec7-4435-96a4-3e79a52967c8
-- title:
--   Gross substitutability (GS)
-- statement:
--   A function $f:\mathbb R^n\to[-\infty,\infty)$ is said to satisfy **GS** if for any $p,q\in\mathbb R^n$ with $p\le q$ and $x\in\arg\max f[-p]$, there exists $y\in\arg\max f[-q]$ such that $y_i\ge x_i$ whenever $q_i=p_i$.
--
--   When the prices of some goods rise, demand for the goods whose prices did not change does not fall. A function satisfying GS is called a GS-function.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Definition 3, p.21

import Mathlib
import Definitions.Def_SConvexGS_argMaxTilt

namespace SConvexGS

/-- Gross substitutability (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF
of 2021-10-29), Definition 3, p.21): `f : ℝⁿ → [−∞, ∞)` satisfies GS if for any `p ≤ q` and
`x ∈ arg max f[−p]` there exists `y ∈ arg max f[−q]` such that `yᵢ ≥ xᵢ` whenever `qᵢ = pᵢ`.

Formalization Note: `p ≤ q` is the componentwise order of `Fin n → ℝ`. -/
def IsGS {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ p q : Fin n → ℝ, p ≤ q → ∀ x ∈ argMaxTilt f p, ∃ y ∈ argMaxTilt f q,
    ∀ i, q i = p i → x i ≤ y i

end SConvexGS


