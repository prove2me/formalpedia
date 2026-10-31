-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsStationaryRBM
-- name    : RBMSensitivity_Data_IsStationaryRBM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:51.641977+00:00
-- url     : https://prove2.me/theorems/605f0097-0493-473a-9f8b-5489182fb789
-- title:
--   Stationary distribution of the RBM
-- statement:
--   A **stationary distribution of the RBM $Z^\alpha$** is a probability measure $\nu$ on $G$ such that
--   $$\nu(A)=\int_G\mathbb P(Z^{\alpha,x}(t)\in A)\,\nu(dx)$$
--   for all Borel $A\subseteq G$ and all $t\ge 0$.
--
--   It is the first marginal of the stationary distribution of the joint process, and $Z^\alpha(\infty)$ has this law.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.5, p.10

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone_G
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- A stationary distribution of the RBM `Z^α`, used in Theorem 3.5: arXiv:1907.00472v2, p.10. It is the
analogue of Definition 3.3 on `G`: a probability measure `ν` on `G` with
`ν(A) = ∫ P(Z^{α,x}(t) ∈ A) ν(dx)` for all Borel `A` and `t ≥ 0`.

**Formalization Note.** As in `Data.IsStationaryJoint`, a measure on the closed set `G` is a measure on
`E J` with `ν Gᶜ = 0`. -/
structure Data.IsStationaryRBM {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (D : Data J)
    (P : Measure Ω) (Z : ℝ → E J → ℝ≥0 → Ω → E J) (α : ℝ) (ν : Measure (E J)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ν
  support : ν D.Gᶜ = 0
  invariant : ∀ A : Set (E J), MeasurableSet A → ∀ t : ℝ≥0,
    ν A = ∫⁻ x, P {ω | Z α x t ω ∈ A} ∂ν

end RBMSensitivity


