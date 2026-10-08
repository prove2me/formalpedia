-- Prove2me | Definitions.Def_AMPUniversality_StateEvol_SE
-- name    : AMPUniversality_StateEvol_SE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:31:08.373066+00:00
-- url     : https://prove2.me/theorems/dcd31cdc-c945-4680-85b8-5f965835ba51
-- title:
--   Gaussian state-evolution recursion, (1.10)–(1.11)
-- statement:
--   Starting from the prescribed positive semidefinite matrices $\widehat\Sigma_a^0$, state evolution defines, for $t\ge1$,
--
--   $$\Sigma_a^t=\sum_b c_bW_{ab}\widehat\Sigma_b^{t-1},\qquad \widehat\Sigma_a^t=\mathbb E[g(Z_a^t,Y_a,a,t)g(Z_a^t,Y_a,a,t)^\mathsf T].$$
--
--   Here $Z_a^t$ is centered Gaussian with covariance $\Sigma_a^t$ and is independent of $Y_a\sim P_a$. A joint recursion computes the covariance and its hatted second moment at each step; the Gaussian law is transported from Mathlib's Euclidean-space representation to coordinate vectors.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 9, (1.10)–(1.11)

import Definitions.Def_AMPUniversality_StateEvol_Converging

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AMPUniversality.StateEvol

/-- A Gaussian law on coordinate vectors, transported from Euclidean space. -/
noncomputable def gaussianVec {q : ℕ} (S : Matrix (Fin q) (Fin q) ℝ) :
    Measure (Fin q → ℝ) :=
  Measure.map (fun z : EuclideanSpace ℝ (Fin q) => fun r => z r)
    (multivariateGaussian 0 S)

/-- Equation (1.10), with the class weights and variance profile. -/
def Model.seCovStep {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ}
    (M : Model Ω q h k d)
    (hat : Fin k → Matrix (Fin q) (Fin q) ℝ) :
    Fin k → Matrix (Fin q) (Fin q) ℝ :=
  fun a r s => ∑ b, M.ca b * M.W a b * hat b r s

/-- Equation (1.11), the second moment of `g`, with an independent label. -/
noncomputable def Model.seHatStep {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d)
    (t : ℕ) (cov : Fin k → Matrix (Fin q) (Fin q) ℝ) :
    Fin k → Matrix (Fin q) (Fin q) ℝ :=
  fun a r s =>
    ∫ zy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h),
      M.gvec zy.1 zy.2 a t r * M.gvec zy.1 zy.2 a t s
      ∂((gaussianVec (cov a)).prod (M.Pa a))

/-- Joint recursion: at time zero only the hatted covariance is prescribed. -/
noncomputable def Model.seState {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d) :
    ℕ → (Fin k → Matrix (Fin q) (Fin q) ℝ) ×
      (Fin k → Matrix (Fin q) (Fin q) ℝ)
  | 0 => (0, M.hat0)
  | t + 1 =>
      let old := M.seState t
      let cov := M.seCovStep old.2
      (cov, M.seHatStep (t + 1) cov)

/-- The covariance `Σᵗ` for t ≥ 1. -/
noncomputable def Model.se {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d) (t : ℕ) :
    Fin k → Matrix (Fin q) (Fin q) ℝ :=
  (M.seState t).1

/-- The hatted covariance `Σ̂ᵗ`, initialized by (1.9). -/
noncomputable def Model.seHat {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d) (t : ℕ) :
    Fin k → Matrix (Fin q) (Fin q) ℝ :=
  (M.seState t).2

end AMPUniversality.StateEvol


