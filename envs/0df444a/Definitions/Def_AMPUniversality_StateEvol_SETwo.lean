-- Prove2me | Definitions.Def_AMPUniversality_StateEvol_SETwo
-- name    : AMPUniversality_StateEvol_SETwo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:32:22.63902+00:00
-- url     : https://prove2.me/theorems/c79eb3bb-c540-4cb9-bb91-8dc712cb851a
-- title:
--   Two-time Gaussian state evolution, (4.1)–(4.3)
-- statement:
--   The two-time recursion tracks a joint Gaussian pair of AMP iterates. Its hatted covariance has the three boundary forms of (4.1): four equal $\widehat\Sigma_a^0$ blocks at $(0,0)$, and diagonal blocks $\widehat\Sigma_a^t,\widehat\Sigma_a^0$ when one time is zero. For positive times, the covariance uses the same class-weighted variance profile as one-time state evolution, and the hatted covariance is the second-moment matrix of the concatenated vector $(g(Z_a^t,Y_a,a,t),g(Z_a^s,Y_a,a,s))$ with a shared label $Y_a$.
--
--   $$\Sigma_a^{t,s}=\sum_b c_bW_{ab}\widehat\Sigma_b^{t-1,s-1},\qquad \widehat\Sigma_a^{t,s}=\mathbb E[X_aX_a^\mathsf T].$$
--
--   This definition supports the diagonal identity (4.4) and the paper's two-time theorem.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 14–15, (4.1)–(4.3)

import Definitions.Def_AMPUniversality_StateEvol_SE

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AMPUniversality.StateEvol

/-- Coordinate law of a jointly Gaussian pair of `q`-vectors. -/
noncomputable def gaussianPair {q : ℕ}
    (S : Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℝ) :
    Measure ((Fin q ⊕ Fin q) → ℝ) :=
  Measure.map
    (fun z : EuclideanSpace ℝ (Fin q ⊕ Fin q) => fun r => z r)
    (multivariateGaussian 0 S)

/-- Concatenation of the two polynomial outputs in (4.3). -/
def Model.pairG {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ}
    (M : Model Ω q h k d) (t s : ℕ) (a : Fin k)
    (z : (Fin q ⊕ Fin q) → ℝ) (y : EuclideanSpace ℝ (Fin h)) :
    (Fin q ⊕ Fin q) → ℝ :=
  fun r => match r with
  | Sum.inl u => M.gvec (fun v => z (Sum.inl v)) y a t u
  | Sum.inr u => M.gvec (fun v => z (Sum.inr v)) y a s u

/-- The second-moment update in (4.3). -/
noncomputable def Model.seTwoHatStep {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d) (t s : ℕ)
    (cov : Fin k → Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℝ) :
    Fin k → Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℝ :=
  fun a r u =>
    ∫ zy : ((Fin q ⊕ Fin q) → ℝ) × EuclideanSpace ℝ (Fin h),
      M.pairG t s a zy.1 zy.2 r * M.pairG t s a zy.1 zy.2 u
      ∂((gaussianPair (cov a)).prod (M.Pa a))

/-- Hatted two-time covariance from (4.1)–(4.3). -/
noncomputable def Model.seTwoHat {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d) :
    ℕ → ℕ → Fin k → Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℝ
  | 0, 0 => fun a => Matrix.fromBlocks (M.hat0 a) (M.hat0 a)
      (M.hat0 a) (M.hat0 a)
  | t + 1, 0 => fun a => Matrix.fromBlocks (M.seHat (t + 1) a) 0 0 (M.hat0 a)
  | 0, s + 1 => fun a => Matrix.fromBlocks (M.hat0 a) 0 0 (M.seHat (s + 1) a)
  | t + 1, s + 1 =>
      let old := M.seTwoHat t s
      let cov : Fin k → Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℝ :=
        fun a r u => ∑ b, M.ca b * M.W a b * old b r u
      M.seTwoHatStep (t + 1) (s + 1) cov
termination_by t s => t + s

/-- The two-time covariance `Σᵗ˒ˢ` of (4.2), defined for t,s ≥ 1. -/
noncomputable def Model.seTwo {Ω : Type*} [MeasurableSpace Ω]
    {q h k d : ℕ} (M : Model Ω q h k d)
    (t s : ℕ) : Fin k → Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℝ :=
  match t, s with
  | t + 1, s + 1 =>
      fun a r u => ∑ b, M.ca b * M.W a b * M.seTwoHat t s b r u
  | _, _ => 0

end AMPUniversality.StateEvol


