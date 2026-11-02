-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P94
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P94
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:31:46.816095+00:00
-- url     : https://prove2.me/theorems/ef268e4d-b935-4b65-999c-8bfa420190df
-- title:
--   Definitions for One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering
-- statement:
--   The objects the formalized statements of *One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering* (arXiv:1109.1435) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BobBases`: PDF pp.2,6: Bob's two binary rank-one projective bases, as columns of unitaries.
--   - `basisEffect`: PDF p.6, (S2): the rank-one projector for outcome b in basis j.
--   - `squaredOverlap`: PDF pp.3,6, q of (S4): squared overlap of two specified basis vectors. The first vector is conjugated, consistently with the accepted inner-product convention.
--   - `maximumOverlap`: PDF pp.3,6: the maximum over the FOUR pairs of binary basis vectors.
--   - `projectiveOverlapIncompatibility`: PDF pp.3,6: q=-log2(max squared overlap), the projective specialization of [20]. Unitarity makes the maximum positive; q is computed, never supplied as a free bound. This overlap uncertainty parameter is distinct from Dependency50.P32.incompatibility, which is generalized POVM robustness (an ENNReal infimum of 1+r).
--   - `MutuallyUnbiased`: PDF p.6, (S10): mutually unbiased qubit bases, including Pauli Z/X.
--   - `HiddenModel`: PDF p.6, (S2): a single setting-independent normalized hidden ensemble. Alice's response may depend on her setting and the hidden state. Bob's response is Born's rule on that SAME state for every pair of settings. Integrability prevents Bochner's default value on non-integrable input; coordinate measurability expresses the usual standing convention for a continuous classical hidden variable. The no-click output is fixed in advance, and the detection flag is part of Alice's output.
--   - `observed`: PDF p.6, (S2): actual observed P(a,s,b|i,j), including the flag. The integral permits arbitrary discrete or continuous ensembles, not just finite mixtures.
--   - `conditionalEntropyBits`: PDF p.6, definitions following (S3): binary conditional Shannon entropy in bits. P is the joint law of the conditioning symbol x and binary B. Zero-mass rows contribute zero, so no conditional law is assigned to an impossible event.
--   - `binaryError`: PDF p.6, (S7): disagreement probability for a joint binary law, without postselection.
--   - `detectionProbability`: PDF p.6, (S6): Alice's detection probability at setting i, after Bob selection.
--   - `fullError`: PDF p.6, (S7)--(S9): Q_i from all Alice outputs, including assigned no-click bits.
--   - `detectedErrorMass`: PDF p.6, (S8),(S10): unnormalized probability of a detected disagreement.
--   - `weightedDetectedEntropy`: PDF p.6, (S8),(S10): eta_i*h(Q_i^ps), with the zero-efficiency continuation explicitly defined to be zero. Conditional Q_i^ps is used only on a positive-mass branch.
--   - `flaggedConditionalEntropy`: PDF p.6, (S5): entropy of the actual same-setting marginal B_i conditioned on (A_i,s_i). This definition never posits joint outcomes for Bob's two incompatible measurements.
-- source:
--   One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering, arXiv:1109.1435v3, https://arxiv.org/abs/1109.1435v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Statements from Branciard et al., arXiv:1109.1435v3, PDF p.6.
The operational security statements are explicitly deferred in the unit artifacts.
Bool false/true labels settings 1/2, binary outcomes, and no-click/click flags.
A single arbitrary probability space supplies the hidden ensemble for all settings.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P94

open MeasureTheory
open scoped ComplexConjugate

/-- PDF pp.2,6: Bob's two binary rank-one projective bases, as columns of unitaries. -/
abbrev BobBases := Bool → Matrix.unitaryGroup Bool ℂ

/-- PDF p.6, (S2): the rank-one projector for outcome b in basis j. -/
def basisEffect (U : BobBases) (j b : Bool) : Matrix Bool Bool ℂ :=
  fun x y => (U j : Matrix Bool Bool ℂ) x b * conj ((U j : Matrix Bool Bool ℂ) y b)

/-- PDF pp.3,6, q of (S4): squared overlap of two specified basis vectors.
The first vector is conjugated, consistently with the accepted inner-product convention. -/
def squaredOverlap (U : BobBases) (a b : Bool) : ℝ :=
  Complex.normSq (∑ x : Bool,
    conj ((U false : Matrix Bool Bool ℂ) x a) * (U true : Matrix Bool Bool ℂ) x b)

/-- PDF pp.3,6: the maximum over the FOUR pairs of binary basis vectors. -/
def maximumOverlap (U : BobBases) : ℝ :=
  max (max (squaredOverlap U false false) (squaredOverlap U false true))
    (max (squaredOverlap U true false) (squaredOverlap U true true))

/-- PDF pp.3,6: q=-log2(max squared overlap), the projective specialization of [20].
Unitarity makes the maximum positive; q is computed, never supplied as a free bound.
This overlap uncertainty parameter is distinct from Dependency50.P32.incompatibility,
which is generalized POVM robustness (an ENNReal infimum of 1+r). -/
def projectiveOverlapIncompatibility (U : BobBases) : ℝ :=
  -Real.logb 2 (maximumOverlap U)

/-- PDF p.6, (S10): mutually unbiased qubit bases, including Pauli Z/X. -/
def MutuallyUnbiased (U : BobBases) : Prop :=
  ∀ a b, squaredOverlap U a b = 1 / 2

/-- PDF p.6, (S2): a single setting-independent normalized hidden ensemble.
Alice's response may depend on her setting and the hidden state. Bob's response is
Born's rule on that SAME state for every pair of settings. Integrability prevents
Bochner's default value on non-integrable input; coordinate measurability expresses
the usual standing convention for a continuous classical hidden variable.
The no-click output is fixed in advance, and the detection flag is part of Alice's output. -/
structure HiddenModel (Lambda : Type*) [MeasurableSpace Lambda] (U : BobBases) where
  law : Measure Lambda
  probability : IsProbabilityMeasure law
  rho : Lambda → Matrix Bool Bool ℂ
  normalized : ∀ l, QAlgorithms.IsDensityMatrix (rho l)
  rhoMeasurable : ∀ x y, Measurable (fun l => rho l x y)
  response : Bool → Lambda → Bool → Bool → ℝ
  responseNonneg : ∀ i l a s, 0 ≤ response i l a s
  responseSum : ∀ i l, ∑ a : Bool, ∑ s : Bool, response i l a s = 1
  responseMeasurable : ∀ i a s, Measurable (fun l => response i l a s)
  noClickBit : Bool → Bool
  assignedNoClick : ∀ i l a, a ≠ noClickBit i → response i l a false = 0
  bornIntegrable : ∀ i j a s b,
    Integrable (fun l => response i l a s *
      QAlgorithms.effectProb (basisEffect U j b) (rho l)) law

/-- PDF p.6, (S2): actual observed P(a,s,b|i,j), including the flag.
The integral permits arbitrary discrete or continuous ensembles, not just finite mixtures. -/
def observed {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i j a s b : Bool) : ℝ :=
  ∫ l, L.response i l a s * QAlgorithms.effectProb (basisEffect U j b) (L.rho l) ∂L.law

/-- PDF p.6, definitions following (S3): binary conditional Shannon entropy in bits.
P is the joint law of the conditioning symbol x and binary B. Zero-mass rows
contribute zero, so no conditional law is assigned to an impossible event. -/
def conditionalEntropyBits {X : Type*} [Fintype X] (P : X → Bool → ℝ) : ℝ :=
  ∑ x, if (∑ b : Bool, P x b) = 0 then 0 else
    (∑ b : Bool, P x b) * QAlgorithms.binEntropy2 (P x true / (∑ b : Bool, P x b))

/-- PDF p.6, (S7): disagreement probability for a joint binary law, without postselection. -/
def binaryError (P : Bool → Bool → ℝ) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, if a ≠ b then P a b else 0

/-- PDF p.6, (S6): Alice's detection probability at setting i, after Bob selection. -/
def detectionProbability {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i : Bool) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, observed L i i a true b

/-- PDF p.6, (S7)--(S9): Q_i from all Alice outputs, including assigned no-click bits. -/
def fullError {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i : Bool) : ℝ :=
  binaryError (fun a b => ∑ s : Bool, observed L i i a s b)

/-- PDF p.6, (S8),(S10): unnormalized probability of a detected disagreement. -/
def detectedErrorMass {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i : Bool) : ℝ :=
  binaryError (fun a b => observed L i i a true b)

/-- PDF p.6, (S8),(S10): eta_i*h(Q_i^ps), with the zero-efficiency continuation
explicitly defined to be zero. Conditional Q_i^ps is used only on a positive-mass branch. -/
def weightedDetectedEntropy {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i : Bool) : ℝ :=
  if detectionProbability L i = 0 then 0 else
    detectionProbability L i * QAlgorithms.binEntropy2
      (detectedErrorMass L i / detectionProbability L i)

/-- PDF p.6, (S5): entropy of the actual same-setting marginal B_i conditioned on (A_i,s_i).
This definition never posits joint outcomes for Bob's two incompatible measurements. -/
def flaggedConditionalEntropy {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i : Bool) : ℝ :=
  conditionalEntropyBits (fun t : Bool × Bool => fun b => observed L i i t.1 t.2 b)

/-- A zero-mass conditioning row contributes exactly zero. -/
example : conditionalEntropyBits (fun (_ : Unit) (_ : Bool) => (0 : ℝ)) = 0 := by
  simp [conditionalEntropyBits]

/-- Identity columns give the computational-basis rank-one projector. -/
example : basisEffect (fun _ => 1) false false false false = 1 := by
  simp [basisEffect]

/-- No detections give a zero entropy penalty; no conditional error is evaluated. -/
example {Lambda : Type*} [MeasurableSpace Lambda] {U : BobBases}
    (L : HiddenModel Lambda U) (i : Bool) (h : detectionProbability L i = 0) :
    weightedDetectedEntropy L i = 0 := by
  simp [weightedDetectedEntropy, h]

end QAlgorithms.Papers.Independent.Intakethird100.P94


