-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47
-- name    : QAlgorithms_Papers_Independent_Intake100_P47
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:21:24.100073+00:00
-- url     : https://prove2.me/theorems/9a2c267b-5952-46b9-a755-16b3e626f3f0
-- title:
--   Definitions for Correlation Detection and an Operational Interpretation of the Renyi Mutual Information
-- statement:
--   The objects the formalized statements of *Correlation Detection and an Operational Interpretation of the Renyi Mutual Information* (arXiv:1408.6894) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RenyiOrder`
--   - `logMatrix`: PDF p.6: logarithm on support. The kernel value 0 is used only inside traces whose first argument is supported by the reference.
--   - `rawRenyi`: PDF p.6, (2.8)--(2.9): the finite, positive, nonunit-order formula. The Boolean selects sandwiched (true) or Petz (false). The raw function is used only on that domain, including when taking endpoint limits.
--   - `completedRenyiDivergence`: PDF pp.6--7: endpoint-completed divergence. The source defines orders 0 and infinity by the corresponding one-sided limits; EReal liminf gives those values, including infinity, without a nonconstructive chosen limit. The unit-order value is (2.15). Negative orders have the unused value infinity.
--   - `spectrumCount`: PDF p.7: number of distinct eigenvalues, including the zero eigenspace.
--   - `groupedCopies`: PDF p.12, (4.9): copies regrouped as A^n:B^n.
--   - `generalizedInformation`: PDF p.8, (3.3)--(3.4): infimum over ALL normalized B states. References tau are positive operators and need not be states. EReal preserves negative information values for unnormalized tau.
--   - `marginalReferenceInformation`: PDF p.9, (3.6): the marginal-reference mutual information.
--   - `optimizedConditionalEntropy`: PDF p.9, (3.7)--(3.8): optimized conditional entropy, identity reference.
--   - `informationOne`: PDF p.9, (3.9): the order-one information as the explicit marginal formula.
--   - `relativeLogVariance`: PDF p.7, (2.16): information variance, used only under support inclusion.
--   - `generalizedInformationVariance`: PDF p.8, (3.5): generalized marginalReferenceInformation-information variance.
--   - `universalFactor`: PDF p.5, (2.4): exact dimension of the symmetric purification register.
--   - `universal`: PDF p.5, (2.7): the source's SPECIFIC universal state, as the trace-weighted permutation sum. For positive d the denominator is nonzero also when n=0.
--   - `StatePermutationInvariant`: PDF p.5: invariance under the actual tensor permutation representation.
--   - `universalReference`: PDF p.10: reference tau^n tensor the specific universal B-state.
--   - `classicalNull`: PDF p.10: the constructed classical, pinched null state.
--   - `rejectionError`: PDF p.12, (4.3): rejection probability of a joint effect.
--   - `compositeAcceptanceError`: PDF p.12, (4.4): worst-case error over EVERY B-state, including correlated states when B itself is B^n. The range is nonempty and bounded on states/effects.
--   - `alphaHat`: PDF p.12, (4.5): finite-block constrained type-I optimum. For mu>=0, states and nonempty systems the zero test is feasible, and the value set lies in [0,1].
--   - `exponentialCompositeError`: PDF pp.12--20: finite-block error at an exponential type-II constraint.
--   - `normalizedErrorExponent`: PDF pp.13,15: the extended error exponent, with strictly positive n.
--   - `hoeffdingValue`: PDF p.13, (5.1): extended supremum over all strictly subunit positive orders.
--   - `strongValue`: PDF p.15, (6.1): extended supremum over all finite orders strictly above one.
--   - `thresholdTest`: PDF p.16, (6.4): acceptance includes the zero eigenspace of L-exp(mu)K.
--   - `basisLaw`: PDF p.16, (6.5): distribution in the supplied common orthonormal eigenbasis.
--   - `pureAC`: PDF p.9: the AC marginal of a pure state on AB:C, in A:C order.
--   - `inverseRenyiOrder`: PDF p.9: reciprocal order with 1/0=infinity, rather than real division by zero.
--   - `HalfConvexlike`: PDF p.22, (A.2): a single midpoint-convexlike witness y3 works for EVERY x.
--   - `attainedValueInfimum`: PDF p.28: the constructed minimum-value function. It is used only where an interior global minimizer exists, making the real infimum nonempty and bounded.
--   - `minimizer`: PDF p.28: the unique interior argmin, constructed from f and Gamma. The off-domain fallback 0 is never used in the theorem.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, https://arxiv.org/abs/1408.6894v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

/-! Hayashi--Tomamichel, arXiv:1408.6894v5. Natural logarithms throughout.
All page numbers are PDF pages. Exact accepted support, spectral-power, pinching,
tensor-power, trace, regrouping, mixed-state and diagonalization definitions are
imported. Distinct local concepts use specific names rather than colliding with
unrelated accepted short names. Orders zero and infinity are endpoint limits.
Source defects and cited background deferrals are recorded in HARD.md.
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology
open Filter QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)
open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)
open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev RenyiOrder := WithTop ℝ

variable {A B C D I J : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
variable [DecidableEq I] [DecidableEq J]

/-- PDF p.6: logarithm on support. The kernel value 0 is used only inside
traces whose first argument is supported by the reference. -/
def logMatrix (X : Op I) : Op I := cfc Real.log X

/-- PDF p.6, (2.8)--(2.9): the finite, positive, nonunit-order formula.
The Boolean selects sandwiched (true) or Petz (false). The raw function is
used only on that domain, including when taking endpoint limits. -/
def rawRenyi (sandwiched : Bool) (a : ℝ) (rho sigma : Op I) : EReal :=
  if (1 < a ∧ ¬ SupportLE rho sigma) ∨
      (a < 1 ∧ ¬ 0 < (rho * sigma).trace.re) then ⊤
  else
    let q := if sandwiched then
      let S := supportPower sigma ((1-a)/(2*a))
      (supportPower (S * rho * S) a).trace.re
    else (supportPower rho a * supportPower sigma (1-a)).trace.re
    (((a-1)⁻¹ : ℝ) : EReal) * logNonnegativeExtended q

/-- PDF pp.6--7: endpoint-completed divergence. The source defines orders
0 and infinity by the corresponding one-sided limits; EReal liminf gives
those values, including infinity, without a nonconstructive chosen limit.
The unit-order value is (2.15). Negative orders have the unused value infinity. -/
def completedRenyiDivergence (sandwiched : Bool) (a : RenyiOrder) (rho sigma : Op I) : EReal :=
  if a = ⊤ then Filter.liminf (fun t : ℝ => rawRenyi sandwiched t rho sigma) atTop
  else
    let t := a.untopD 0
    if t < 0 then ⊤ else if t = 0 then
      Filter.liminf (fun s : ℝ => rawRenyi sandwiched s rho sigma) (𝓝[>] (0 : ℝ))
    else if t = 1 then relativeEntropy rho sigma
    else rawRenyi sandwiched t rho sigma

/-- PDF p.7: number of distinct eigenvalues, including the zero eigenspace. -/
def spectrumCount (sigma : Op I) : ℕ :=
  if h : sigma.IsHermitian then (Finset.univ.image h.eigenvalues).card else 0

/-- PDF p.12, (4.9): copies regrouped as A^n:B^n. -/
def groupedCopies (n : ℕ) (rho : Op (A × B)) : Op ((Fin n → A) × (Fin n → B)) :=
  fun p q => ∏ k, rho (p.1 k,p.2 k) (q.1 k,q.2 k)

/-- PDF p.8, (3.3)--(3.4): infimum over ALL normalized B states.
References tau are positive operators and need not be states. EReal preserves
negative information values for unnormalized tau. -/
def generalizedInformation (sandwiched : Bool) (a : RenyiOrder) (rho : Op (A × B)) (tau : Op A) : EReal :=
  ⨅ sigma : {X : Op B // IsDensityMatrix X},
    completedRenyiDivergence sandwiched a rho (Matrix.kronecker tau sigma.val)

/-- PDF p.9, (3.6): the marginal-reference mutual information. -/
def marginalReferenceInformation (sandwiched : Bool) (a : RenyiOrder) (rho : Op (A × B)) : EReal :=
  generalizedInformation sandwiched a rho (traceRight rho)

/-- PDF p.9, (3.7)--(3.8): optimized conditional entropy, identity reference. -/
def optimizedConditionalEntropy (sandwiched : Bool) (a : RenyiOrder) (rho : Op (A × B)) : EReal :=
  -generalizedInformation sandwiched a rho 1

/-- PDF p.9, (3.9): the order-one information as the explicit marginal formula. -/
def informationOne (rho : Op (A × B)) (tau : Op A) : EReal :=
  relativeEntropy rho (Matrix.kronecker tau (traceLeft rho))

/-- PDF p.7, (2.16): information variance, used only under support inclusion. -/
def relativeLogVariance (rho sigma : Op I) : ℝ :=
  let L := logMatrix rho - logMatrix sigma - ((relativeEntropy rho sigma).toReal : ℂ) • 1
  (rho * (L * L)).trace.re

/-- PDF p.8, (3.5): generalized marginalReferenceInformation-information variance. -/
def generalizedInformationVariance (rho : Op (A × B)) (tau : Op A) : ℝ :=
  relativeLogVariance rho (Matrix.kronecker tau (traceLeft rho))

/-- PDF p.5, (2.4): exact dimension of the symmetric purification register. -/
def universalFactor (n d : ℕ) : ℕ := Nat.choose (n + d*d - 1) n

/-- PDF p.5, (2.7): the source's SPECIFIC universal state, as the trace-weighted
permutation sum. For positive d the denominator is nonzero also when n=0. -/
def universal (n d : ℕ) : Op (Fin n → Fin d) :=
  ((universalFactor n d * n.factorial : ℕ) : ℂ)⁻¹ •
    ∑ pi : Equiv.Perm (Fin n),
      (Schur.tensorPermutation d n pi).trace • Schur.tensorPermutation d n pi

/-- PDF p.5: invariance under the actual tensor permutation representation. -/
def StatePermutationInvariant (n d : ℕ) (X : Op (Fin n → Fin d)) : Prop :=
  ∀ pi : Equiv.Perm (Fin n),
    Schur.tensorPermutation d n pi * X * (Schur.tensorPermutation d n pi)ᴴ = X

/-- PDF p.10: reference tau^n tensor the specific universal B-state. -/
def universalReference {d : ℕ} (n : ℕ) (tau : Op A) : Op ((Fin n → A) × (Fin n → Fin d)) :=
  Matrix.kronecker (copies n tau) (universal n d)

/-- PDF p.10: the constructed classical, pinched null state. -/
def classicalNull {d : ℕ} (n : ℕ) (rho : Op (A × Fin d)) (tau : Op A) :=
  pinch (universalReference n tau) (groupedCopies n rho)

/-- PDF p.12, (4.3): rejection probability of a joint effect. -/
def rejectionError (rho Q : Op I) : ℝ := ((1-Q) * rho).trace.re

/-- PDF p.12, (4.4): worst-case error over EVERY B-state, including correlated
states when B itself is B^n. The range is nonempty and bounded on states/effects. -/
def compositeAcceptanceError (tau : Op A) (Q : Op (A × B)) : ℝ :=
  sSup {p : ℝ | ∃ sigma : Op B, IsDensityMatrix sigma ∧
    p = (Q * Matrix.kronecker tau sigma).trace.re}

/-- PDF p.12, (4.5): finite-block constrained type-I optimum. For mu>=0, states
and nonempty systems the zero test is feasible, and the value set lies in [0,1]. -/
def alphaHat (mu : ℝ) (rho : Op (A × B)) (tau : Op A) : ℝ :=
  sInf {p : ℝ | ∃ Q : Op (A × B), IsEffect Q ∧ compositeAcceptanceError tau Q ≤ mu ∧ p = rejectionError rho Q}

/-- PDF pp.12--20: finite-block error at an exponential type-II constraint. -/
def exponentialCompositeError (rho : Op (A × B)) (tau : Op A) (n : ℕ) (R : ℝ) : ℝ :=
  alphaHat (Real.exp (-(n : ℝ)*R)) (groupedCopies n rho) (copies n tau)

/-- PDF pp.13,15: the extended error exponent, with strictly positive n. -/
def normalizedErrorExponent (n : ℕ) (p : ℝ) : EReal :=
  (((n : ℝ)⁻¹ : ℝ) : EReal) * (-logNonnegativeExtended p)

/-- PDF p.13, (5.1): extended supremum over all strictly subunit positive orders. -/
def hoeffdingValue (rho : Op (A × B)) (tau : Op A) (R : ℝ) : EReal :=
  ⨆ s : {s : ℝ // 0 < s ∧ s < 1},
    (((1-s.val)/s.val : ℝ) : EReal) * (generalizedInformation false (s.val : RenyiOrder) rho tau - (R : EReal))

/-- PDF p.15, (6.1): extended supremum over all finite orders strictly above one. -/
def strongValue (rho : Op (A × B)) (tau : Op A) (R : ℝ) : EReal :=
  ⨆ s : {s : ℝ // 1 < s},
    (((s.val-1)/s.val : ℝ) : EReal) * ((R : EReal) - generalizedInformation true (s.val : RenyiOrder) rho tau)

/-- PDF p.16, (6.4): acceptance includes the zero eigenspace of L-exp(mu)K. -/
def thresholdTest (L K : Op I) (mu : ℝ) : Op I :=
  1 - cfc (fun x : ℝ => if 0 < x then 1 else 0) ((Real.exp mu : ℂ) • K - L)

/-- PDF p.16, (6.5): distribution in the supplied common orthonormal eigenbasis. -/
def basisLaw (X : Op I) (U : Matrix.unitaryGroup I ℂ) (i : I) : ℝ :=
  (((U : Op I)ᴴ * X * (U : Op I)) i i).re

/-- PDF p.9: the AC marginal of a pure state on AB:C, in A:C order. -/
def pureAC (psi : EuclideanSpace ℂ ((A × B) × C)) : Op (A × C) :=
  fun p q => ∑ b, pureDensity psi ((p.1,b),p.2) ((q.1,b),q.2)

/-- PDF p.9: reciprocal order with 1/0=infinity, rather than real division by zero. -/
def inverseRenyiOrder (a : ℝ) : RenyiOrder :=
  if a = 0 then ⊤ else (a⁻¹ : ℝ)

example : logNonnegativeExtended 0 = ⊥ := by simp [logNonnegativeExtended]

example (rho sigma : Op I) (h : ¬ SupportLE rho sigma) : relativeEntropy rho sigma = ⊤ := by
  simp [relativeEntropy, show ¬ IsSupported rho sigma from h]

example (X : Op I) (x y : Fin 0 → I) : copies 0 X x y = 1 := by simp [copies]

example (d : ℕ) : universalFactor 0 d = 1 := by simp [universalFactor]

example : inverseRenyiOrder 0 = ⊤ := by simp [inverseRenyiOrder]

example (rho : Op (A × B)) : optimizedConditionalEntropy true 1 rho = -generalizedInformation true 1 rho 1 := rfl

/-- PDF p.22, (A.2): a single midpoint-convexlike witness y3 works for EVERY x. -/
def HalfConvexlike {Y : Type} (X : Set ℝ) (f : ℝ → Y → ℝ) : Prop :=
  ∀ y1 y2, ∃ y3, ∀ x ∈ X, f x y3 ≤ (f x y1 + f x y2)/2

/-- PDF p.28: the constructed minimum-value function. It is used only where
an interior global minimizer exists, making the real infimum nonempty and bounded. -/
def attainedValueInfimum {X Y : Type} (f : X × Y → ℝ) (Gamma : Set Y) (x : X) : ℝ :=
  sInf ((fun y => f (x,y)) '' Gamma)

/-- PDF p.28: the unique interior argmin, constructed from f and Gamma.
The off-domain fallback 0 is never used in the theorem. -/
def minimizer {X Y : Type} [Zero Y] (f : X × Y → ℝ) (Gamma : Set Y) (x : X) : Y :=
  if h : ∃ y ∈ Gamma, ∀ z ∈ Gamma, f (x,y) ≤ f (x,z) then h.choose else 0

example {X Y : Type} (f : X × Y → ℝ) (x : X) (y : Y) :
    attainedValueInfimum f {y} x = f (x,y) := by simp [attainedValueInfimum]

end QAlgorithms.Papers.Independent.Intake100.P47


