-- Prove2me | Definitions.Def_RBMSensitivity_jointTransition
-- name    : RBMSensitivity_jointTransition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:28.540208+00:00
-- url     : https://prove2.me/theorems/e616ab72-e9d9-41bd-8625-fd5909074855
-- title:
--   The transition functions $P_t^\alpha(\xi,A)$
-- statement:
--   The family of transition functions on $\mathbb X$ associated with the joint processes:
--   $$P_t^\alpha(\xi,A):=\mathbb P(\Xi^{\alpha,\xi}(t)\in A),\qquad \xi\in\mathbb X,\ A\in\mathcal B(\mathbb X).$$
--
--   It defines the stationary distributions of the joint process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §3.1, (3.2), p.9

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The transition function `P_t^α(ξ, A) := P(Ξ^{α,ξ}(t) ∈ A)` of (3.2): arXiv:1907.00472v2, p.9. -/
noncomputable def jointTransition {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → E J → ℝ≥0 → Ω → E J) (𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J) (α : ℝ) (t : ℝ≥0)
    (ξ : E J × E J) (A : Set (E J × E J)) : ℝ≥0∞ :=
  P {ω | (Z α ξ.1 t ω, 𝒥 α ξ t ω) ∈ A}

end RBMSensitivity


