-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsStationaryJoint
-- name    : RBMSensitivity_Data_IsStationaryJoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:24.354347+00:00
-- url     : https://prove2.me/theorems/bd9e7006-0c8b-4b51-aa85-1c9427070a35
-- title:
--   Definition 3.3: stationary distribution of the joint process
-- statement:
--   Given a probability measure $\mu$ on $(\mathbb X,\mathcal B(\mathbb X))$, define $(\mu P_t^\alpha)(A):=\int_{\mathbb X}P_t^\alpha(\xi,A)\,\mu(d\xi)$. A **stationary distribution of the joint process associated with $\alpha$** is a probability measure $\mu^\alpha$ on $(\mathbb X,\mathcal B(\mathbb X))$ such that $\mu^\alpha(A)=(\mu^\alpha P_t^\alpha)(A)$ for all $A\in\mathcal B(\mathbb X)$ and $t\ge 0$.
--
--   The law of $(Z^\alpha(\infty),\mathcal J^\alpha(\infty))$ in the goal theorem is this distribution.
--
--   **Formalization Note** A probability measure on the Borel subset $\mathbb X$ is represented by a probability measure on $\mathbb R^J\times\mathbb R^J$ that gives the complement of $\mathbb X$ measure zero.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 3.3, p.10; §3.2, p.9

import Mathlib
import Definitions.Def_RBMSensitivity_jointTransition
import Definitions.Def_RBMSensitivity_SimpleCone_X
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Definition 3.3: arXiv:1907.00472v2, p.10. A stationary distribution of the joint process associated
with `α`: a probability measure `μ^α` on `(X, B(X))` with `μ^α(A) = (μ^α P_t^α)(A)` for all
`A ∈ B(X)` and `t ≥ 0`, where `(μ P_t^α)(A) := ∫_X P_t^α(ξ, A) μ(dξ)` (p.9).

**Formalization Note.** `X` is a Borel subset of `E J × E J`, so a probability measure on `X` is the
same as a probability measure on `E J × E J` that gives `Xᶜ` measure zero, and the Borel sets of `X`
are the traces of Borel sets `A`. For `ξ ∈ X` the event `Ξ^{α,ξ}(t) ∈ Xᶜ` is null, so testing all
Borel `A` is the same as testing those in `X`. -/
structure Data.IsStationaryJoint {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (D : Data J)
    (P : Measure Ω) (Z : ℝ → E J → ℝ≥0 → Ω → E J) (𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J) (α : ℝ)
    (ν : Measure (E J × E J)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ν
  support : ν D.Xᶜ = 0
  invariant : ∀ A : Set (E J × E J), MeasurableSet A → ∀ t : ℝ≥0,
    ν A = ∫⁻ ξ, jointTransition P Z 𝒥 α t ξ A ∂ν

end RBMSensitivity


