-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_Proper
-- name    : PrivateAgnosticHalfspace_Gaussian_Supplement_Proper
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:05:47.442207+00:00
-- url     : https://prove2.me/theorems/a03318b3-4ec4-400c-84a0-67f63a7973c6
-- title:
--   Algorithm 2: noisy correlations, spectral cover and proper output
-- statement:
--   Fix public constants $C_0,c,C_{\rm dim},K,A,K_0$. Set $p=\lceil C_0/(c\alpha)^2\rceil$, $D_p=\binom{d+p}{p}$ and $T=2\sqrt{D_p}$. On an even ordered sample of size $n$, Algorithm 2 uses two disjoint halves and releases
--   $$\widetilde m=\operatorname{Proj}_{B_2}\left(\frac2n\sum_{i\in S_1}Y_i\bar\psi_{p,T}(X_i)+Z\right),\qquad Z\sim N(0,\sigma^2 I),\quad \sigma=\frac{4T\sqrt{2\log(1.25/\delta)}}{\varepsilon n}.$$
--   The actual polynomial is $q(x)=\langle\widetilde m,\psi_p(x)\rangle$, using the unclipped features. Squared population loss uses the clipped label $U=s(X)Y$, where $s=T/\max(T,\|\psi_p(X)\|)$.
--
--   Its derivative covariance is $M=E[\nabla q\nabla q^\top]$. The cover uses the spectral subspace at cutoff $(c\alpha)^2/C_0$, a public sphere net at tolerance $c\alpha$, and thresholds $j c\alpha$ with $|j|\le\lceil\sqrt{K_0\log(1/(c\alpha))}/(c\alpha)\rceil$. Two tail halfspaces with normal $e_1$ remain even when the subspace has dimension zero. Duplicate halfspace pairs are removed. Validation on $S_2$ weights each remaining halfspace by the exponential of minus $\varepsilon/2$ times its number of mistakes.
--
--   The sample schedule is the least even $n\ge2$ satisfying (31) and the exact private-validation slack at most $c\alpha$, using the public upper bound $K_H=\lceil\exp(A(c\alpha)^{-4}\log(1/(c\alpha)))\rceil$. Thus the schedule never depends on random cover size or conditional labels. The learning, cover-size and runtime guarantees are not part of these definitions.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), pp.7–10,31–34, Theorem 3.1, Algorithm 2, Eq. (31), Appendix E

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_Core

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

noncomputable section

/-- All constants are public; this structure contains no learning guarantees. -/
structure ProperConstants where
  degree : ℝ
  accuracy : ℝ
  dimension : ℝ
  meanSample : ℝ
  cover : ℝ
  tail : ℝ

def properDegree (c : ProperConstants) (α : ℝ) : ℕ := ⌈c.degree / (c.accuracy * α) ^ 2⌉₊

def coverBound (c : ProperConstants) (α : ℝ) : ℕ :=
  ⌈Real.exp (c.cover * (c.accuracy * α)⁻¹ ^ 4 * Real.log (1 / (c.accuracy * α)))⌉₊

def properCondition (c : ProperConstants) (d : ℕ) (α β ε δ : ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ Even n ∧
  c.meanSample * ((featureDimension d (properDegree c α) : ℝ) * Real.log (8 / β) / α ^ 2 +
    featureDimension d (properDegree c α) * Real.log (8 / β) * Real.sqrt (Real.log (1.25 / δ)) /
      (ε * α)) ≤ n ∧
  2 * Real.sqrt (Real.log (8 * (coverBound c α : ℝ) / β) / n) +
    4 * Real.log (4 * (coverBound c α : ℝ) / β) / (ε * n) ≤ c.accuracy * α

def properSize (c : ProperConstants) (d : ℕ) (α β ε δ : ℝ) : ℕ :=
  firstSize (properCondition c d α β ε δ)

def squaredLoss (d p : ℕ) (P : Measure (Example d)) (v : Coeff d p) : ℝ :=
  ∫ z, (clipScale d p z.1 * label z.2 - polynomialPredictor d p v z.1) ^ 2 ∂P

/-- This uses the unmodified polynomial features, not the clipped score. -/
def derivativeCovariance {d p : ℕ} (v : Coeff d p) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, (fderiv ℝ (polynomialPredictor d p v) x (WithLp.toLp 2 (Pi.single i 1))) *
    (fderiv ℝ (polynomialPredictor d p v) x (WithLp.toLp 2 (Pi.single j 1))) ∂gaussian d

/-- Appendix E: spectral subspace, explicit sphere net, threshold grid, and two tails.
At rank zero only the two tail halfspaces occur. -/
def properCandidates {d p : ℕ} (c : ProperConstants) (α : ℝ) (v : Coeff d p) : List (Halfspace d) :=
  let γ := c.accuracy * α
  let V := spectralBasis (derivativeCovariance v) (γ ^ 2 / c.degree)
  let directions := sphereNet V γ
  let J := ⌈Real.sqrt (c.tail * Real.log (1 / γ)) / γ⌉₊
  let R := γ * J
  let thresholds := List.ofFn fun j : Fin (2 * J + 1) => ((j.val : ℝ) - J) * γ
  (directions.flatMap (fun w => thresholds.map fun t => (w,t)) ++ [(axis d, R), (axis d, -R)]).dedup

/-- Algorithm 2, including projection of the noisy mean and independent private validation. -/
def properLaw (c : ProperConstants) (d : ℕ) (α ε δ : ℝ)
    (S : List (Example d)) : Measure (Halfspace d) :=
  let p := properDegree c α
  let n := S.length
  let S₁ := block S 0 (n / 2)
  let S₂ := block S (n / 2) (n / 2)
  let mean := ((2 : ℝ) / n) • (S₁.map fun z => label z.2 • clipped d p z.1).sum
  let σ := 4 * radius d p * Real.sqrt (2 * Real.log (1.25 / δ)) / (ε * n)
  (stdGaussian (Coeff d p)).bind fun Z =>
    let v := radial 1 (mean + σ • Z)
    select (properCandidates c α v) classifier ε S₂

def properInput (c : ProperConstants) (d : ℕ) (α β ε δ : ℝ)
    (S : List (Example d)) : ℕ → ℝ :=
  input [d, S.length, α, β, ε, δ, c.degree, c.accuracy, c.dimension,
    c.meanSample, c.cover, c.tail] S

def properSampleScale (d : ℕ) (p : ℕ) (α ε : ℝ) : ℝ :=
  featureDimension d p / α ^ 2 + featureDimension d p / (ε * α) + α⁻¹ ^ 6 + 1 / (ε * α ^ 5)

end
end PrivateAgnosticHalfspace.Gaussian.Supplement


