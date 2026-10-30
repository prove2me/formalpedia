-- Prove2me | Definitions.Def_RoughgardenPOA_robustPOA
-- name    : RoughgardenPOA_robustPOA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:36:28.904888+00:00
-- url     : https://prove2.me/theorems/000362fe-092b-4a04-8955-500a3a45e44c
-- title:
--   Robust price of anarchy $\rho(G)$ (Definition 2.2)
-- statement:
--   The **robust price of anarchy** of a cost-minimization game $G$ is
--
--   $$\rho(G) = \inf\Big\{ \frac{\lambda}{1-\mu} \;:\; (\lambda, \mu) \in \mathbb R^2,\ \mu < 1,\ \text{the game is } (\lambda,\mu)\text{-smooth} \Big\} \in [-\infty, +\infty].$$
--
--   It is the best upper bound on the price of anarchy that a smoothness argument can certify.
--
--   **Formalization Note** The infimum is taken in the extended reals (`EReal`), so it is the true infimum: $\rho(G) = +\infty$ when no pair $(\lambda, \mu)$ with $\mu < 1$ is smooth (empty set), and $\rho(G) = -\infty$ when the quotients are unbounded below (for instance when every cost is $0$). $\lambda$ ranges over all real numbers, exactly as in Definition 2.2; since $\mu < 1$ the quotient never divides by zero.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, Definition 2.2, p. 5

import Mathlib
import Definitions.Def_RoughgardenPOA_IsSmooth

namespace RoughgardenPOA

/-- **The robust price of anarchy ρ(G) (Definition 2.2).**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, Definition 2.2, p. 5: "The robust price of anarchy of a cost-minimization
game is inf { λ/(1 − µ) : (λ, µ) such that the game is (λ, µ)-smooth }, with µ always
constrained to be less than 1."

`robustPOA C` is the infimum, in the extended reals `EReal`, of `λ / (1 − µ)` over all real
pairs `(λ, µ)` with `µ < 1` such that the game is `(λ, µ)`-smooth.

**Formalization Note.** The infimum is taken in `EReal` so that it is the true infimum in
`[−∞, +∞]`: it is `⊤ = +∞` when no pair `(λ, µ)` with `µ < 1` is smooth (empty index set), and
`⊥ = −∞` when the values `λ/(1 − µ)` are unbounded below (e.g. when every cost is `0`). The
index set is exactly Definition 2.2's: `λ` is any real number and `µ < 1`; no `λ > 0` is
imposed. Since `µ < 1`, the real division `λ / (1 − µ)` never divides by zero. -/
noncomputable def robustPOA {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) : EReal :=
  ⨅ (p : ℝ × ℝ) (_ : p.2 < 1 ∧ IsSmooth C p.1 p.2), ((p.1 / (1 - p.2) : ℝ) : EReal)

end RoughgardenPOA


