-- Prove2me | Definitions.Def_NashStackelberg_IsMNE
-- name    : NashStackelberg_IsMNE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:05.97691+00:00
-- url     : https://prove2.me/theorems/9c874a7f-8fcf-44fe-bf91-8fc6862b610d
-- title:
--   Mixed Nash equilibrium of a simultaneous game
-- statement:
--   In a simultaneous game in which player $i$ minimizes $f^i(x^i,x^{-i})$ over $x^i\in\mathcal F^i$, a **mixed strategy** $\sigma^i$ of player $i$ is a probability distribution over $\mathcal F^i$. Players randomize independently, so a profile $\sigma=(\sigma^1,\dots,\sigma^n)$ induces the product distribution $\sigma^1\otimes\cdots\otimes\sigma^n$ on profiles.
--
--   The profile $\sigma$ is a **mixed Nash equilibrium (MNE)** if, for every player $i$ and every pure strategy $\tilde x^i\in\mathcal F^i$,
--   $$
--   \mathbb E_{X\sim\sigma}\big[f^i(X^i,X^{-i})\big]\;\le\;\mathbb E_{X^{-i}\sim\sigma^{-i}}\big[f^i(\tilde x^i,X^{-i})\big],
--   $$
--   where both expectations exist.
--
--   **Formalization Note** $\sigma^i$ is a Borel probability measure on $\mathbb R^{V_i}$ with $\sigma^i\big((\mathcal F^i)^{\mathrm c}\big)=0$. The right-hand expectation is the integral over the whole product measure of the cost with coordinate $i$ replaced by $\tilde x^i$, which does not depend on $X^i$. Both the cost and every deviation cost are required to be integrable, which is what "the expectations exist" means; without this requirement Lean's integral of a non-integrable function would be $0$ and the inequality would be vacuous.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 1 and Definition 2, pp.6–7

import Mathlib

open MeasureTheory

namespace NashStackelberg

/-- **Mixed Nash equilibrium of a simultaneous game** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Definition 1 and
Definition 2, pp.6–7).

A mixed strategy `σ i` of player `i` is a probability distribution over its feasible set `F i`.
Players randomize independently, so a profile `σ = (σ¹, …, σⁿ)` induces the product measure
`Measure.pi σ` on profiles. `σ` is an MNE if for every player `i` and every pure deviation
`x' ∈ F i`,
`E_{X∼σ}[fⁱ(Xⁱ, X⁻ⁱ)] ≤ E_{X⁻ⁱ∼σ⁻ⁱ}[fⁱ(x', X⁻ⁱ)]`.

**Formalization Note.** `σ i` is a Borel probability measure on `V i → ℝ` with `σ i (F i)ᶜ = 0`.
The right-hand expectation over `σ⁻ⁱ` is written as the integral over the full product measure of
the cost with coordinate `i` replaced by `x'`, which does not depend on `Xⁱ`. Definition 2 compares
expectations, so both are required to exist: the cost and each deviation cost are integrable
(without this the Bochner integral would be `0` and the inequality vacuous). Objectives are
minimized, as in Definitions 1, 2 and 4. -/
def IsMNE {n : ℕ} {V : Fin n → Type*} (F : (i : Fin n) → Set (V i → ℝ))
    (f : Fin n → ((j : Fin n) → V j → ℝ) → ℝ) (σ : (i : Fin n) → Measure (V i → ℝ)) : Prop :=
  (∀ i, IsProbabilityMeasure (σ i) ∧ σ i (F i)ᶜ = 0) ∧
  ∀ i, Integrable (f i) (Measure.pi σ) ∧
    ∀ x' ∈ F i, Integrable (fun x => f i (Function.update x i x')) (Measure.pi σ) ∧
      ∫ x, f i x ∂(Measure.pi σ) ≤ ∫ x, f i (Function.update x i x') ∂(Measure.pi σ)

end NashStackelberg


