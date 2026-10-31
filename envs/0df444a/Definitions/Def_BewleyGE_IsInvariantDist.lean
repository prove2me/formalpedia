-- Prove2me | Definitions.Def_BewleyGE_IsInvariantDist
-- name    : BewleyGE_IsInvariantDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:13.300815+00:00
-- url     : https://prove2.me/theorems/35c533b7-5a6a-45b5-bd8b-3ac86afe0ea2
-- title:
--   Invariant wealth distribution $\mu=M\mu$
-- statement:
--   A measure $\mu$ is an **invariant wealth distribution** at prices $(p,r)$ for the policy $g$ if $\mu$ is a probability measure on $A(p,r)$ and $\mu=M\mu$.
--
--   **Formalization Note** "$\mu\in\mathcal P(A(p,r))$" is a probability measure on $\mathbb R$ giving the complement of $A(p,r)$ measure zero.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, p.8

import Mathlib
import Definitions.Def_BewleyGE_wealthOperator
import Definitions.Def_BewleyGE_wealthSet

open MeasureTheory

namespace BewleyGE

/-- **Invariant wealth distribution.** Light, arXiv:1906.06810v2, p.8: "A wealth distribution
μ ∈ P(A(p, r)) is called an invariant wealth distribution if μ = Mμ."

**Formalization Note.** `μ ∈ P(A(p, r))` is a probability measure on `ℝ` with
`μ(A(p, r)ᶜ) = 0`. -/
def IsInvariantDist {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ) (g : ℝ → ℝ)
    (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (wealthSet E p r)ᶜ = 0 ∧ wealthOperator E p r g μ = μ

end BewleyGE


