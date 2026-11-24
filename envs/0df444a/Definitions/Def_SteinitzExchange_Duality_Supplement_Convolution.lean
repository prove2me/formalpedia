-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_Convolution
-- name    : SteinitzExchange_Duality_Supplement_Convolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:23:29.168283+00:00
-- url     : https://prove2.me/theorems/d12ff9d9-ef65-4425-8968-decd2e1e6f5f
-- title:
--   Supremum convolution $\omega_1\,\square\,\omega_2$ on the Minkowski sum $B_1+B_2$
-- statement:
--   Let $V$ be a finite set and let $B_1,B_2\subseteq\mathbb Z^V$ be finite sets of integer vectors. Their **Minkowski sum** is
--   $$B_1+B_2=\{x_1+x_2\mid x_1\in B_1,\ x_2\in B_2\}.$$
--   For $\omega_1:B_1\to\mathbb R$ and $\omega_2:B_2\to\mathbb R$ the **(supremum) convolution** $\omega_1\,\square\,\omega_2:B_1+B_2\to\mathbb R$ is
--   $$(\omega_1\,\square\,\omega_2)(x)=\sup\{\omega_1(x_1)+\omega_2(x_2)\mid x_1+x_2=x,\ x_1\in B_1,\ x_2\in B_2\}.$$
--   For $x\in B_1+B_2$ the family is finite and nonempty, so the supremum is a maximum.
--
--   The convolution is the discrete analogue of the supremal convolution of concave functions; Theorem 6.10 of the paper shows that it preserves the exchange property (EXC).
--
--   **Formalization Note.** `minkSum B₁ B₂` is the image of $B_1\times B_2$ under addition. `supConv B₁ ω₁ B₂ ω₂ x` is a real `⨆` over the finite subtype of pairs $(x_1,x_2)\in B_1\times B_2$ with $x_1+x_2=x$; it is the paper's maximum for $x\in B_1+B_2$, and the junk value $0$ (empty family) off $B_1+B_2$, where it is never used. Functions on $B_i$ are total functions $\mathbb Z^V\to\mathbb R$ of which only the values on $B_i$ matter.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 302, Section 6.4 (definition of ω₁ □ ω₂ and B₁ + B₂)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet

namespace SteinitzExchange.Duality.Supplement

/-- The Minkowski sum `B₁ + B₂ = {x₁ + x₂ | x₁ ∈ B₁, x₂ ∈ B₂}` of two finite sets of integer
vectors (Murota 1996, p. 302, §6.4). -/
noncomputable def minkSum {V : Type*} (B₁ B₂ : Finset (V → ℤ)) : Finset (V → ℤ) := by
  classical
  exact (B₁ ×ˢ B₂).image (fun q => q.1 + q.2)

/-- The supremum convolution `ω₁ □ ω₂ : B₁ + B₂ → ℝ` (Murota 1996, p. 302, §6.4):
`(ω₁ □ ω₂)(x) = sup{ω₁(x₁) + ω₂(x₂) | x₁ + x₂ = x, x₁ ∈ B₁, x₂ ∈ B₂}`.
For `x ∈ B₁ + B₂` the index family is finite and nonempty, so this real supremum is the maximum,
which is the paper's value. For `x ∉ B₁ + B₂` the family is empty and the value is the junk value
`0`; every statement uses `supConv` only on `minkSum B₁ B₂`. -/
noncomputable def supConv {V : Type*} (B₁ : Finset (V → ℤ)) (ω₁ : (V → ℤ) → ℝ)
    (B₂ : Finset (V → ℤ)) (ω₂ : (V → ℤ) → ℝ) (x : V → ℤ) : ℝ :=
  ⨆ q : {q : (V → ℤ) × (V → ℤ) // q.1 ∈ B₁ ∧ q.2 ∈ B₂ ∧ q.1 + q.2 = x}, ω₁ q.1.1 + ω₂ q.1.2

end SteinitzExchange.Duality.Supplement


