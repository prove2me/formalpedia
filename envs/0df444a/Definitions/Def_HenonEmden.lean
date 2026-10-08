-- Prove2me | Definitions.Def_HenonEmden
-- name    : HenonEmden
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.351987+00:00
-- url     : https://prove2.me/theorems/7c7553b2-f5b5-4c0a-9c6e-316454ca7ff2
-- statement:
--   Space(n) is n-dimensional real Euclidean space. For a dimension n and real parameters p, q, A, B, IsSolution(n,p,q,A,B,u,v) is the property that two real functions u and v on Space(n) form a positive solution of a Hénon–Lane–Emden system: u and v are continuous on all of Space(n), twice continuously differentiable on the complement of the origin, and strictly positive everywhere, and for every x≠0 they satisfy −Δu(x) = |x|^A · v(x)^p and −Δv(x) = |x|^B · u(x)^q, where Δ is the Laplacian and powers are real powers. No regularity is required at the origin beyond continuity, and no decay conditions or restrictions on the sign or size of p, q, A, B are imposed. Subcritical(n,p,q,A,B) is the defined condition (n+A)/(p+1) + (n+B)/(q+1) > n−2, an inequality on the exponents and dimension rather than a theorem. The block only defines this solution notion and the subcritical condition and proves nothing about when solutions exist.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HenonEmden.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HenonEmden.lean; bytes 16..777
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace HenonLaneEmden

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure IsSolution (n : ℕ) (p q A B : ℝ) (u v : Space n → ℝ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  regular_u : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))
  regular_v : ContDiffOn ℝ 2 v ({0}ᶜ : Set (Space n))
  positive_u : ∀ x, 0 < u x
  positive_v : ∀ x, 0 < v x
  equation_u : ∀ x, x ≠ 0 →
    -(Laplacian.laplacian u) x = Real.rpow ‖x‖ A * Real.rpow (v x) p
  equation_v : ∀ x, x ≠ 0 →
    -(Laplacian.laplacian v) x = Real.rpow ‖x‖ B * Real.rpow (u x) q

def Subcritical (n : ℕ) (p q A B : ℝ) : Prop :=
  ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - (1 + 1)



end HenonLaneEmden
end OAI


