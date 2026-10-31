-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_RS
-- name    : KallMayerSLP_ValueOfInfo_RS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:49.007097+00:00
-- url     : https://prove2.me/theorems/08b4e2a7-d59f-4af2-8ead-8639fda2d069
-- title:
--   Optimal value $RS$ of the recourse problem (2.66)
-- statement:
--   The optimal value of the two-stage stochastic program with recourse,
--
--   $$
--   RS=\min_x\big\{c^{\mathsf T}x+\mathbb E_\xi[Q(x;T(\xi),h(\xi),W(\xi),q(\xi))]\big\}\quad\text{s.t. } Ax=b,\ x\ge0 .
--   $$
--
--   **Formalization Note** $\mu$ is the law of $\xi$. The minimum is the infimum in $[-\infty,+\infty]$ over $\mathcal B_1$ ($+\infty$ if $\mathcal B_1=\emptyset$), and the expectation is the extended-real expectation `eExp`, which gives $+\infty$ to a decision whose expected recourse is $+\infty$ or undefined.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.66), p.243 (PDF 252)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_firstStageSet
import Definitions.Def_KallMayerSLP_ValueOfInfo_eExp
import Definitions.Def_KallMayerSLP_ValueOfInfo_recourse

open MeasureTheory Matrix

namespace KallMayerSLP.ValueOfInfo

/-- **The optimal value `RS` of the recourse problem, (2.66).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, eq. (2.66), p.243 (PDF 252):
`RS := min_x {cᵀx + 𝔼_ξ[Q(x; T(ξ), h(ξ), W(ξ), q(ξ))]}` s.t. `Ax = b`, `x ≥ 0`.

**Formalization Note.** `μ` is the law `ℙ_ξ` on `ℝʳ`. The book's `min` is the infimum in `EReal`
over `B₁ = {x | Ax = b, x ≥ 0}` (`+∞` if `B₁ = ∅`); the expectation is `eExp`, which gives `+∞` to a
decision whose expected recourse is `+∞` or undefined, the decisions the book says (p.200) are "not to
be chosen". -/
noncomputable def RS {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) : EReal :=
  ⨅ x ∈ firstStageSet P, ((P.c ⬝ᵥ x : ℝ) : EReal) + eExp μ (fun ξ => recourse P x ξ)

end KallMayerSLP.ValueOfInfo


