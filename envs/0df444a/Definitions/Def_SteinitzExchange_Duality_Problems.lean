-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Problems
-- name    : SteinitzExchange_Duality_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:55:20.837274+00:00
-- url     : https://prove2.me/theorems/7c8ea431-e7c0-4de4-a852-b410867c2061
-- title:
--   Optimal values of the primal, relaxed primal and dual problems, valued in $[-\infty,+\infty]$
-- statement:
--   Let $B_1,B_2\subseteq\mathbb Z^V$ be finite, $\omega:B_1\to\mathbb R$ and $\zeta:B_2\to\mathbb R$. Take $\omega^\circ$ and $\hat\omega$ with respect to $B_1$ and $\zeta^\bullet$ and $\check\zeta$ with respect to $B_2$. The three problems of §6.2 have the optimal values
--
--   $$\begin{aligned}
--   \text{primal:}&\quad \max\{\omega(x)-\zeta(x)\mid x\in B_1\cap B_2\},\\
--   \text{relaxed primal:}&\quad \max\{\hat\omega(b)-\check\zeta(b)\mid b\in\overline{B_1}\cap\overline{B_2}\},\\
--   \text{dual:}&\quad \inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb R^V\},
--   \end{aligned}$$
--
--   together with the integral dual value $\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb Z^V\}$. All values lie in the extended reals $[-\infty,+\infty]$; following the paper, the maximum over an empty family is $-\infty$, and the dual infimum is $-\infty$ when the objective is unbounded below.
--
--   **Formalization Note.** The values are `EReal` suprema and infima of coerced real numbers, so no expression $\infty-\infty$ ever arises; `EReal`'s supremum of the empty family is $\bot=-\infty$, which is exactly the paper's convention. The relaxed value evaluates `concaveClosure B₁ ω` and `convexClosure B₂ ζ` only on $\overline{B_1}\cap\overline{B_2}$, where they are the paper's finite values.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 294 (PRIMAL, DUAL and RELAXED PRIMAL PROBLEM), p. 295 (convention after Eq. (6.5), Theorem 6.4(2))

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality

/-- Optimal value of the PRIMAL PROBLEM (Murota 1996, p. 294):
`max{ω(x) − ζ(x) | x ∈ B₁ ∩ B₂}` in `EReal`. The supremum of the empty family is `⊥ = −∞`,
which is the paper's convention "the maximum taken over an empty family is equal to −∞"
(p. 295). Every term is a coerced real, so no `⊤ − ⊤` arises. -/
noncomputable def primalValue {V : Type*} (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) : EReal :=
  ⨆ (x : V → ℤ) (_ : x ∈ B₁) (_ : x ∈ B₂), ((ω x - ζ x : ℝ) : EReal)

/-- Optimal value of the RELAXED PRIMAL PROBLEM (Murota 1996, p. 294):
`max{ω̂(b) − ζ̌(b) | b ∈ B̄₁ ∩ B̄₂}` in `EReal`, with `ω̂` the concave closure of `ω` with respect
to `B₁` (Eq. (4.2)) and `ζ̌` the convex closure of `ζ` with respect to `B₂` (Eq. (6.2)). Both are
evaluated only on `B̄₁ ∩ B̄₂`, where they are the paper's finite values. The supremum of the empty
family is `⊥ = −∞` (the paper's convention, p. 295). -/
noncomputable def relaxedValue {V : Type*} [Fintype V] (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) : EReal :=
  ⨆ (b : V → ℝ) (_ : b ∈ hull B₁ ∩ hull B₂),
    ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal)

/-- Optimal value of the DUAL PROBLEM (Murota 1996, p. 294):
`inf{ζ•(p) − ω°(p) | p ∈ ℝ^V}` in `EReal`, with `ω°` the concave conjugate of `ω` w.r.t. `B₁`
(Eq. (4.1)) and `ζ•` the convex conjugate of `ζ` w.r.t. `B₂` (Eq. (6.1)). It is `⊥ = −∞`
exactly when the family is unbounded below. -/
noncomputable def dualValue {V : Type*} [Fintype V] (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) : EReal :=
  ⨅ p : V → ℝ, ((convexConj B₂ ζ p - concaveConj B₁ ω p : ℝ) : EReal)

/-- The dual optimal value over integral vectors: `inf{ζ•(p) − ω°(p) | p ∈ ℤ^V}` in `EReal`
(Murota 1996, p. 295, Theorem 6.4(2); p. 297, Eq. (6.7)). -/
noncomputable def dualValueInt {V : Type*} [Fintype V] (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) : EReal :=
  ⨅ p : V → ℤ, ((convexConj B₂ ζ (toReal p) - concaveConj B₁ ω (toReal p) : ℝ) : EReal)

end SteinitzExchange.Duality


