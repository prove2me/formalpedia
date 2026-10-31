-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_levelEvents
-- name    : KallMayerSLP_ProbConstr_levelEvents
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:23.667251+00:00
-- url     : https://prove2.me/theorems/24302ced-1f5a-47eb-8a4a-3ef80ea9740a
-- title:
--   The family $\mathcal G_\alpha$ of events of probability at least $\alpha$
-- statement:
--   For a level $\alpha\in\mathbb R$ let
--   $$
--   \mathcal G_\alpha=\{A\in\mathcal B^r \mid \mathbb P_\xi(A)\ge\alpha\}
--   $$
--   be the family of Borel events whose probability is at least $\alpha$. The probability constraint $G(x)\ge\alpha$ asks that the event $S(x)$ belong to $\mathcal G_\alpha$.
--
--   **Formalization Note** Membership in $\mathcal B^r$ is measurability for the Borel $\sigma$-algebra of `Fin r → ℝ`; probabilities are `(μ A).toReal`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.1, p.96 (PDF 106)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- The family `𝒢_α = {A ∈ 𝓑^r | ℙ_ξ(A) ≥ α}` of Borel events of probability at least `α`.

Kall & Mayer 2005, Chapter 2, §2.1, p.96 (PDF 106).

**Formalization Note.** `μ` is the distribution `ℙ_ξ`; membership in `𝓑^r` is `MeasurableSet A`
for the Borel σ-algebra of `Fin r → ℝ`; the probability is `(μ A).toReal`, exact for a
probability measure. -/
def levelEvents {r : ℕ} (μ : Measure (Fin r → ℝ)) (α : ℝ) : Set (Set (Fin r → ℝ)) :=
  {A | MeasurableSet A ∧ α ≤ (μ A).toReal}

end KallMayerSLP.ProbConstr


