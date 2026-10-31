-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_objective
-- name    : KallMayerSLP_Multistage_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:56.7279+00:00
-- url     : https://prove2.me/theorems/55a4f8de-57dd-4bb9-8f5f-07b36c45f51f
-- title:
--   Objective of (3.10)
-- statement:
--   The objective of a policy in problem (3.10) is
--   $$
--   c_1^{\mathsf T}x_1+\mathbb E\sum_{t=2}^Tc_t^{\mathsf T}x_t(\zeta_t)=\sum_{t=1}^T\mathbb E\big[c_t^{\mathsf T}x_t(\zeta_t)\big].
--   $$
--
--   **Formalization Note** A Bochner integral. On feasible policies, which are square-integrable, it is never Lean's default value.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.10), p.261 (PDF 270)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_MSLP
import Definitions.Def_KallMayerSLP_Multistage_zeta

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The objective `c_1ᵀ x_1 + 𝔼 Σ_{t=2}^T c_tᵀ x_t(ζ_t)` of problem (3.10) (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, (3.10), p.261, PDF 270).

**Formalization Note.** Written as `Σ_{t=1}^T 𝔼[c_tᵀ x_t(ζ_t)]`. A Bochner integral: on the feasible
policies, which are square-integrable, it is never Lean's junk value `0`, and the expectation of the
finite sum is the sum of the expectations. At `t = 1` the integrand is the constant `c_1ᵀ x_1`. -/
noncomputable def objective (D : MSLP) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) (x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D.T, ∫ ω, D.c t ⬝ᵥ x t (zeta ξ t ω) ∂P

end KallMayerSLP.Multistage


