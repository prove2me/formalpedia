-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46
-- name    : QAlgorithms_Papers_Independent_Claimed50_P46
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:16:55.078106+00:00
-- url     : https://prove2.me/theorems/68e21d0b-0a8e-4e24-bff1-b05d60648ef9
-- title:
--   Definitions for An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses
-- statement:
--   The objects the formalized statements of *An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses* (arXiv:quant-ph/0206185) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ClassicalData`: Sections II,VII, PDF pp.2,13: countable alphabet, pointwise finite weights.
--   - `QuantumData`: Section II, PDF p.2: positive bounded operators on an arbitrary Hilbert space. Normalization is imposed separately; the basis only defines the extended trace.
--   - `SimpleHypothesisSystem`: Section II, PDF pp.2–3: the two concrete models, with no dimension restriction.
--   - `SimpleHypothesisTest`: Section II, PDF p.2: all randomized functions or all quantum effects.
--   - `testRejection`: Sections II–III, PDF pp.2–4: rejection effect I-T.
--   - `positiveTrace`: Section II, PDF p.2: extended nonnegative trace, retaining divergent sums.
--   - `quantumWeight`: Section II, PDF p.2: Tr(sqrt(T) A sqrt(T)) avoids signed divergent traces.
--   - `totalMass`: Sections II,VII, PDF pp.2,13: total mass, false=rho, true=sigma.
--   - `hypothesisWeight`: Section II, PDF p.2: positive effect expectation, false=rho, true=sigma.
--   - `testingTypeI`: Equations (1),(54), PDF pp.2,13: rho[I-T]; equals 1-rho[T] when normalized.
--   - `testingTypeII`: Equation (1), PDF p.2: sigma[T].
--   - `UniformModel`: Section II, PDF pp.2–3: a sequence is classical throughout or quantum throughout.
--   - `OriginalNormalization`: Section II, PDF pp.2–3: rho normalized, sigma an unrestricted weight.
--   - `SwitchedNormalization`: Equation (54), PDF p.13: rho has nonzero mass, sigma normalized.
--   - `IsLikelihood`: Equation (6), PDF p.4: arbitrary boundary randomization/effect. For self-adjoint A, A_+(I-S)=0 and (-A)_+ S=0 characterize precisely the effects between the strict-positive and nonnegative spectral projections. Positive parts use continuous functional calculus, so continuous spectrum is also covered.
--   - `LikelihoodFamily`: Section III, PDF pp.4–5: every permitted likelihood family is quantified.
--   - `perBlock`: Section II, PDF p.3: positive block length k+1, including at k=0.
--   - `blockErrorExponent`: Sections II–III, PDF pp.3,5: error exponent, retaining both infinities.
--   - `alphaL`: Section II, PDF p.3: lower asymptotic alpha.
--   - `alphaU`: Section II, PDF p.3: upper asymptotic alpha.
--   - `etaL`: Section II, PDF p.3: lower type-I exponent.
--   - `etaU`: Section II, PDF p.3: upper type-I exponent.
--   - `zetaL`: Section II, PDF p.3: lower type-II exponent.
--   - `zetaU`: Section II, PDF p.3: upper type-II exponent.
--   - `zetaLc`: Sections III,VII, PDF pp.5,13: lower complementary correct-testing exponent.
--   - `zetaUc`: Sections III,VII, PDF pp.5,13: upper complementary correct-testing exponent.
--   - `steinB`: Section IV, PDF p.6: Stein optimum, with limsup-alpha <= epsilon.
--   - `steinBdag`: Section IV, PDF p.6: dagger optimum, with strict liminf-alpha < epsilon.
--   - `divergenceL`: Section IV, PDF p.6: lower epsilon-spectral rate.
--   - `divergenceU`: Section IV, PDF p.6: upper epsilon-spectral rate.
--   - `errorTradeoff`: Equation (38), PDF p.10: optimal second-kind error exponent.
--   - `correctTradeoff`: Equations (51),(62),(73),(74), PDF pp.13–15: choose upper/lower correct exponent and every-block/asymptotic constraint independently.
--   - `dualTradeoff`: Equation (90), PDF p.17: dual correct-testing supremum.
--   - `increasingLeft`: Theorem 3, PDF pp.10–11: strict-threshold supremum, equal to the left limit at finite cutoffs. At cutoff -infinity its empty supremum is -infinity. This corrects the printed zeta(a0-0) at that endpoint: Remark 5's literal monotone endpoint limit can be +infinity even when Remark 6 gives Be=-infinity.
--   - `decreasingRight`: Remark 5, PDF p.11: right limit for a nonincreasing function at a finite point.
--   - `errorCutoff`: Theorem 3, PDF pp.10–11: plateau-extended cutoff a0.
--   - `errorCutoffValue`: Theorem 3, Remark 6, PDF p.11: explicit singular endpoint values.
--   - `correctCutoff`: Equations (63),(75), PDF pp.14–15: crossing cutoff (finite translations).
--   - `hanExpression`: Corollary 1, PDF pp.15–16: infinity-safe primitive form of Han's expression.
--   - `plateauHeight`: Corollary 1, PDF p.15: zeta^c(-infinity), a monotone endpoint limit.
--   - `plateauThreshold`: Equation (80), PDF p.15: inf(M-a) over the plateau; avoids infinity-infinity.
--   - `Source`: Section VIII, PDF p.17: a general source, with countable nonproduct alphabets.
--   - `sourceSystem`: Section VIII, PDF p.17: comparison with counting measure.
--   - `StochasticSourceCode`: Section VIII, PDF p.17: stochastic finite nonempty-message code. Fin size only labels the messages and imposes no restriction on a finite code.
--   - `codeAcceptance`: Equation (93), PDF p.17: the code's raw acceptance function.
--   - `sourceCodeSuccess`: Section VIII, PDF p.17: correct decoding probability.
--   - `sourceCodeError`: Section VIII, PDF p.17: error is one minus success.
--   - `codeRate`: Section VIII, PDF pp.17–18: ordinary finite size logarithm, embedded before limsup.
--   - `compressionRate`: Equations (96),(98), PDF p.18: ordinary/dagger coding rate.
--   - `codingErrorRate`: Equation (104), PDF p.18: optimum rate at a lower error-exponent constraint.
--   - `codingCorrectRate`: Equation (107), PDF p.18: optimum rate at an upper correct-decoding constraint.
--   - `sourceTail`: Equations (97),(99),(106), PDF p.18: upper self-information tail, with boundary randomization matched to the chosen counting-measure likelihood family.
--   - `spectralEntropy`: Equations (101),(103), PDF p.18: spectral sup-entropy (upper=true) and inf-entropy, using the limit-in-probability tail characterizations.
--   - `sourceSigmaL`: Equation (106), PDF p.18: liminf upper-tail exponent sigma(a)=eta(-a).
--   - `sourceSigmaStarU`: Theorem 7, PDF p.19: limsup exponent of the matched lower tail. Acceptance rho[S(-a)] is the complement of sourceTail, including its boundary choice.
--   - `sourceCutoff`: Theorem 7, PDF p.19: threshold b0, with real thresholds embedded in EReal.
--   - `revisedHanRate`: Section VIII, PDF p.20: infinity-safe unconditional Han-form coding expression.
--   - `finiteAcceptanceTest`: Section VIII, PDF p.18: deterministic test of a finite acceptance region.
--   - `strictClassicalTest`: Section III, PDF p.4: the strict deterministic classical likelihood test.
--   - `strictClassicalFamily`: Section III, PDF p.4: strict tests as an actual chosen likelihood family.
--   - `twoPointData`: Example 3, PDF p.16, (86)–(87): the explicit two-point distributions. The theorem supplies b_k>0,c>0, so both coordinates are genuine probabilities.
--   - `reverseClassical`: Example 3, PDF p.16: reverse the two classical hypotheses.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, https://arxiv.org/abs/quant-ph/0206185v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-! Paper-local models for Nagaoka–Hayashi, arXiv:quant-ph/0206185v2.
Index k denotes the positive block length n=k+1. All logarithms are natural.
All optimizations and exponent limits preserve both infinities in EReal.
Compilation is pending the separate mechanical handoff. -/

noncomputable section

open Filter
open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Sections II,VII, PDF pp.2,13: countable alphabet, pointwise finite weights. -/
structure ClassicalData where
  X : Type u
  countableX : Countable X
  rho : X → ℝ≥0
  sigma : X → ℝ≥0

/-- Section II, PDF p.2: positive bounded operators on an arbitrary Hilbert space.
Normalization is imposed separately; the basis only defines the extended trace. -/
structure QuantumData where
  H : Type u
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  J : Type u
  basis : HilbertBasis J ℂ H
  rho : H →L[ℂ] H
  sigma : H →L[ℂ] H
  rho_positive : IsPositive rho
  sigma_positive : IsPositive sigma

attribute [instance] QuantumData.normed QuantumData.innerSpace QuantumData.complete

/-- Section II, PDF pp.2–3: the two concrete models, with no dimension restriction. -/
inductive SimpleHypothesisSystem where
  | classical (data : ClassicalData.{u})
  | quantum (data : QuantumData.{u})

/-- Section II, PDF p.2: all randomized functions or all quantum effects. -/
def SimpleHypothesisTest : SimpleHypothesisSystem.{u} → Type u
  | .classical C => C.X → Set.Icc (0 : ℝ) 1
  | .quantum Q => {T : Q.H →L[ℂ] Q.H // IsPositive T ∧ IsPositive (1 - T)}

/-- Sections II–III, PDF pp.2–4: rejection effect I-T. -/
def testRejection : {P : SimpleHypothesisSystem.{u}} → SimpleHypothesisTest P → SimpleHypothesisTest P
  | .classical _, T => fun x =>
      ⟨1 - (T x).val, by constructor <;> linarith [(T x).property.1, (T x).property.2]⟩
  | .quantum _, T => ⟨1 - T.val, T.property.2, by simpa using T.property.1⟩

/-- Section II, PDF p.2: extended nonnegative trace, retaining divergent sums. -/
def positiveTrace (Q : QuantumData.{u}) (A : Q.H →L[ℂ] Q.H) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal (inner ℂ (Q.basis j) (A (Q.basis j))).re

/-- Section II, PDF p.2: Tr(sqrt(T) A sqrt(T)) avoids signed divergent traces. -/
def quantumWeight (Q : QuantumData.{u}) (A T : Q.H →L[ℂ] Q.H) : ℝ≥0∞ :=
  let R := cfc Real.sqrt T
  positiveTrace Q (R.comp (A.comp R))

/-- Sections II,VII, PDF pp.2,13: total mass, false=rho, true=sigma. -/
def totalMass : SimpleHypothesisSystem.{u} → Bool → ℝ≥0∞
  | .classical C, false => ∑' x, (C.rho x : ℝ≥0∞)
  | .classical C, true => ∑' x, (C.sigma x : ℝ≥0∞)
  | .quantum Q, false => positiveTrace Q Q.rho
  | .quantum Q, true => positiveTrace Q Q.sigma

/-- Section II, PDF p.2: positive effect expectation, false=rho, true=sigma. -/
def hypothesisWeight : (P : SimpleHypothesisSystem.{u}) → Bool → SimpleHypothesisTest P → ℝ≥0∞
  | .classical C, false, T => ∑' x, (C.rho x : ℝ≥0∞) * ENNReal.ofReal (T x).val
  | .classical C, true, T => ∑' x, (C.sigma x : ℝ≥0∞) * ENNReal.ofReal (T x).val
  | .quantum Q, false, T => quantumWeight Q Q.rho T.val
  | .quantum Q, true, T => quantumWeight Q Q.sigma T.val

/-- Equations (1),(54), PDF pp.2,13: rho[I-T]; equals 1-rho[T] when normalized. -/
def testingTypeI {P : SimpleHypothesisSystem.{u}} (T : SimpleHypothesisTest P) : ℝ≥0∞ := hypothesisWeight P false (testRejection T)

/-- Equation (1), PDF p.2: sigma[T]. -/
def testingTypeII {P : SimpleHypothesisSystem.{u}} (T : SimpleHypothesisTest P) : ℝ≥0∞ := hypothesisWeight P true T

/-- Section II, PDF pp.2–3: a sequence is classical throughout or quantum throughout. -/
def UniformModel (P : ℕ → SimpleHypothesisSystem.{u}) : Prop :=
  (∀ k, ∃ C : ClassicalData.{u}, P k = SimpleHypothesisSystem.classical C) ∨
  (∀ k, ∃ Q : QuantumData.{u}, P k = SimpleHypothesisSystem.quantum Q)

/-- Section II, PDF pp.2–3: rho normalized, sigma an unrestricted weight. -/
def OriginalNormalization (P : ℕ → SimpleHypothesisSystem.{u}) : Prop :=
  UniformModel P ∧ ∀ k, totalMass (P k) false = 1

/-- Equation (54), PDF p.13: rho has nonzero mass, sigma normalized. -/
def SwitchedNormalization (P : ℕ → SimpleHypothesisSystem.{u}) : Prop :=
  UniformModel P ∧ ∀ k, 0 < totalMass (P k) false ∧ totalMass (P k) true = 1

/-- Equation (6), PDF p.4: arbitrary boundary randomization/effect.
For self-adjoint A, A_+(I-S)=0 and (-A)_+ S=0 characterize precisely the effects
between the strict-positive and nonnegative spectral projections. Positive parts
use continuous functional calculus, so continuous spectrum is also covered. -/
def IsLikelihood : (P : SimpleHypothesisSystem.{u}) → ℕ → ℝ → SimpleHypothesisTest P → Prop
  | .classical C, k, a, S => ∀ x,
      ((C.rho x : ℝ) > Real.exp (((k : ℝ) + 1) * a) * (C.sigma x : ℝ) → (S x).val = 1) ∧
      ((C.rho x : ℝ) < Real.exp (((k : ℝ) + 1) * a) * (C.sigma x : ℝ) → (S x).val = 0)
  | .quantum Q, k, a, S =>
      let A := Q.rho - (Real.exp (((k : ℝ) + 1) * a) : ℂ) • Q.sigma
      (cfc (fun x : ℝ => max x 0) A).comp (1 - S.val) = 0 ∧
      (cfc (fun x : ℝ => max x 0) (-A)).comp S.val = 0

/-- Section III, PDF pp.4–5: every permitted likelihood family is quantified. -/
structure LikelihoodFamily (P : ℕ → SimpleHypothesisSystem.{u}) where
  tests : ℝ → (k : ℕ) → SimpleHypothesisTest (P k)
  valid : ∀ a k, IsLikelihood (P k) k a (tests a k)

-- Section II, PDF p.3: reuse Mathlib ENNReal.log with both extended endpoints.

/-- Section II, PDF p.3: positive block length k+1, including at k=0. -/
def perBlock (k : ℕ) (x : EReal) : EReal := ((1 / (k + 1 : ℝ) : ℝ) : EReal) * x

/-- Sections II–III, PDF pp.3,5: error exponent, retaining both infinities. -/
def blockErrorExponent (k : ℕ) (p : ℝ≥0∞) : EReal := -perBlock k (ENNReal.log p)

/-- Section II, PDF p.3: lower asymptotic alpha. -/
def alphaL {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : ℝ≥0∞ :=
  liminf (fun k => testingTypeI (T k)) atTop

/-- Section II, PDF p.3: upper asymptotic alpha. -/
def alphaU {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : ℝ≥0∞ :=
  limsup (fun k => testingTypeI (T k)) atTop

/-- Section II, PDF p.3: lower type-I exponent. -/
def etaL {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : EReal :=
  liminf (fun k => blockErrorExponent k (testingTypeI (T k))) atTop

/-- Section II, PDF p.3: upper type-I exponent. -/
def etaU {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : EReal :=
  limsup (fun k => blockErrorExponent k (testingTypeI (T k))) atTop

/-- Section II, PDF p.3: lower type-II exponent. -/
def zetaL {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : EReal :=
  liminf (fun k => blockErrorExponent k (testingTypeII (T k))) atTop

/-- Section II, PDF p.3: upper type-II exponent. -/
def zetaU {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : EReal :=
  limsup (fun k => blockErrorExponent k (testingTypeII (T k))) atTop

/-- Sections III,VII, PDF pp.5,13: lower complementary correct-testing exponent. -/
def zetaLc {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : EReal :=
  zetaL (fun k => testRejection (T k))

/-- Sections III,VII, PDF pp.5,13: upper complementary correct-testing exponent. -/
def zetaUc {P : ℕ → SimpleHypothesisSystem.{u}} (T : (k : ℕ) → SimpleHypothesisTest (P k)) : EReal :=
  zetaU (fun k => testRejection (T k))

/-- Section IV, PDF p.6: Stein optimum, with limsup-alpha <= epsilon. -/
def steinB (P : ℕ → SimpleHypothesisSystem.{u}) (eps : ℝ) : EReal :=
  sSup {z | ∃ T : (k : ℕ) → SimpleHypothesisTest (P k), alphaU T ≤ ENNReal.ofReal eps ∧ z = zetaL T}

/-- Section IV, PDF p.6: dagger optimum, with strict liminf-alpha < epsilon. -/
def steinBdag (P : ℕ → SimpleHypothesisSystem.{u}) (eps : ℝ) : EReal :=
  sSup {z | ∃ T : (k : ℕ) → SimpleHypothesisTest (P k), alphaL T < ENNReal.ofReal eps ∧ z = zetaL T}

/-- Section IV, PDF p.6: lower epsilon-spectral rate. -/
def divergenceL {P : ℕ → SimpleHypothesisSystem.{u}} (S : LikelihoodFamily P) (eps : ℝ) : EReal :=
  sSup {z | ∃ a : ℝ, alphaU (S.tests a) ≤ ENNReal.ofReal eps ∧ z = (a : EReal)}

/-- Section IV, PDF p.6: upper epsilon-spectral rate. -/
def divergenceU {P : ℕ → SimpleHypothesisSystem.{u}} (S : LikelihoodFamily P) (eps : ℝ) : EReal :=
  sSup {z | ∃ a : ℝ, alphaL (S.tests a) < ENNReal.ofReal eps ∧ z = (a : EReal)}

/-- Equation (38), PDF p.10: optimal second-kind error exponent. -/
def errorTradeoff (P : ℕ → SimpleHypothesisSystem.{u}) (r : ℝ) : EReal :=
  sSup {z | ∃ T : (k : ℕ) → SimpleHypothesisTest (P k), (r : EReal) ≤ etaL T ∧ z = zetaL T}

/-- Equations (51),(62),(73),(74), PDF pp.13–15: choose upper/lower correct
exponent and every-block/asymptotic constraint independently. -/
def correctTradeoff (P : ℕ → SimpleHypothesisSystem.{u}) (upper pointwise : Bool) (r : ℝ) : EReal :=
  sInf {z | ∃ T : (k : ℕ) → SimpleHypothesisTest (P k),
    (if pointwise then ∀ k, (r : EReal) ≤ blockErrorExponent k (testingTypeI (T k)) else (r : EReal) ≤ etaL T) ∧
    z = (if upper then zetaUc T else zetaLc T)}

/-- Equation (90), PDF p.17: dual correct-testing supremum. -/
def dualTradeoff (P : ℕ → SimpleHypothesisSystem.{u}) (r : ℝ) : EReal :=
  sSup {z | ∃ T : (k : ℕ) → SimpleHypothesisTest (P k), zetaUc T ≤ (r : EReal) ∧ z = etaL T}

/-- Theorem 3, PDF pp.10–11: strict-threshold supremum, equal to the left limit
at finite cutoffs. At cutoff -infinity its empty supremum is -infinity.
This corrects the printed zeta(a0-0) at that endpoint: Remark 5's literal
monotone endpoint limit can be +infinity even when Remark 6 gives Be=-infinity. -/
def increasingLeft (f : ℝ → EReal) (c : EReal) : EReal :=
  sSup {z | ∃ a : ℝ, (a : EReal) < c ∧ z = f a}

/-- Remark 5, PDF p.11: right limit for a nonincreasing function at a finite point. -/
def decreasingRight (f : ℝ → EReal) (a : ℝ) : EReal :=
  sSup {z | ∃ b : ℝ, a < b ∧ z = f b}

/-- Theorem 3, PDF pp.10–11: plateau-extended cutoff a0. -/
def errorCutoff {P : ℕ → SimpleHypothesisSystem.{u}} (S : LikelihoodFamily P) (r : ℝ) : EReal :=
  sSup {z | ∃ a b : ℝ, (r : EReal) ≤ etaL (S.tests a) ∧
    zetaL (S.tests b) = zetaL (S.tests a) ∧ z = (b : EReal)}

/-- Theorem 3, Remark 6, PDF p.11: explicit singular endpoint values. -/
def errorCutoffValue {P : ℕ → SimpleHypothesisSystem.{u}} (S : LikelihoodFamily P) (r : ℝ) : EReal :=
  let c := errorCutoff S r
  if c = ⊥ then ⊥ else if c = ⊤ then ⊤ else
    c + decreasingRight (fun a => etaL (S.tests a)) c.toReal

/-- Equations (63),(75), PDF pp.14–15: crossing cutoff (finite translations). -/
def correctCutoff (f : ℝ → EReal) (r : ℝ) : EReal :=
  sSup {z | ∃ a : ℝ, ((r + a : ℝ) : EReal) ≤ f a ∧ z = (a : EReal)}

/-- Corollary 1, PDF pp.15–16: infinity-safe primitive form of Han's expression. -/
def hanExpression (eta : ℝ → EReal) (r : ℝ) : EReal :=
  ⨅ a : ℝ, (a : EReal) + max (eta a) (r : EReal)

/-- Corollary 1, PDF p.15: zeta^c(-infinity), a monotone endpoint limit. -/
def plateauHeight (f : ℝ → EReal) : EReal := ⨆ a : ℝ, f a

/-- Equation (80), PDF p.15: inf(M-a) over the plateau; avoids infinity-infinity. -/
def plateauThreshold (f : ℝ → EReal) : EReal :=
  sInf {z | ∃ a : ℝ, f a = plateauHeight f ∧ z = plateauHeight f - (a : EReal)}

example : ENNReal.log 0 = ⊥ := by simp [ENNReal.log]

example : ENNReal.log ⊤ = ⊤ := by simp [ENNReal.log]

example : perBlock 0 (3 : EReal) = 3 := by norm_num [perBlock]

example : blockErrorExponent 0 0 = ⊤ := by simp [blockErrorExponent, perBlock, ENNReal.log]

example : blockErrorExponent 0 ⊤ = ⊥ := by simp [blockErrorExponent, perBlock, ENNReal.log]

example : increasingLeft (fun a : ℝ => (a : EReal)) ⊥ = ⊥ := by
  simp [increasingLeft]

/-- Section VIII, PDF p.17: a general source, with countable nonproduct alphabets. -/
structure Source where
  X : ℕ → Type u
  countableX : ∀ k, Countable (X k)
  p : (k : ℕ) → X k → ℝ≥0
  normalized : ∀ k, (∑' x, (p k x : ℝ≥0∞)) = 1

/-- Section VIII, PDF p.17: comparison with counting measure. -/
def sourceSystem (P : Source.{u}) (k : ℕ) : SimpleHypothesisSystem.{u} :=
  .classical ⟨P.X k, P.countableX k, P.p k, fun _ => 1⟩

/-- Section VIII, PDF p.17: stochastic finite nonempty-message code.
Fin size only labels the messages and imposes no restriction on a finite code. -/
structure StochasticSourceCode (X : Type u) where
  size : ℕ
  size_pos : 0 < size
  encoder : X → Fin size → ℝ≥0
  decoder : Fin size → X → ℝ≥0
  encoder_normalized : ∀ x, (∑ y, encoder x y) = 1
  decoder_normalized : ∀ y, (∑' x, (decoder y x : ℝ≥0∞)) = 1

/-- Equation (93), PDF p.17: the code's raw acceptance function. -/
def codeAcceptance {X : Type u} (C : StochasticSourceCode X) (x : X) : ℝ :=
  ∑ y, (C.encoder x y : ℝ) * (C.decoder y x : ℝ)

/-- Section VIII, PDF p.17: correct decoding probability. -/
def sourceCodeSuccess (P : Source.{u}) (k : ℕ) (C : StochasticSourceCode (P.X k)) : ℝ≥0∞ :=
  ∑' x, (P.p k x : ℝ≥0∞) * ENNReal.ofReal (codeAcceptance C x)

/-- Section VIII, PDF p.17: error is one minus success. -/
def sourceCodeError (P : Source.{u}) (k : ℕ) (C : StochasticSourceCode (P.X k)) : ℝ≥0∞ :=
  1 - sourceCodeSuccess P k C

/-- Section VIII, PDF pp.17–18: ordinary finite size logarithm, embedded before limsup. -/
def codeRate (P : Source.{u}) (C : (k : ℕ) → StochasticSourceCode (P.X k)) : EReal :=
  limsup (fun k => perBlock k (Real.log ((C k).size : ℝ) : EReal)) atTop

/-- Equations (96),(98), PDF p.18: ordinary/dagger coding rate. -/
def compressionRate (P : Source.{u}) (dagger : Bool) (eps : ℝ) : EReal :=
  sInf {z | ∃ C : (k : ℕ) → StochasticSourceCode (P.X k), z = codeRate P C ∧
    (if dagger then liminf (fun k => sourceCodeError P k (C k)) atTop < ENNReal.ofReal eps
     else limsup (fun k => sourceCodeError P k (C k)) atTop ≤ ENNReal.ofReal eps)}

/-- Equation (104), PDF p.18: optimum rate at a lower error-exponent constraint. -/
def codingErrorRate (P : Source.{u}) (r : ℝ) : EReal :=
  sInf {z | ∃ C : (k : ℕ) → StochasticSourceCode (P.X k), z = codeRate P C ∧
    (r : EReal) ≤ liminf (fun k => blockErrorExponent k (sourceCodeError P k (C k))) atTop}

/-- Equation (107), PDF p.18: optimum rate at an upper correct-decoding constraint. -/
def codingCorrectRate (P : Source.{u}) (r : ℝ) : EReal :=
  sInf {z | ∃ C : (k : ℕ) → StochasticSourceCode (P.X k), z = codeRate P C ∧
    limsup (fun k => blockErrorExponent k (sourceCodeSuccess P k (C k))) atTop ≤ (r : EReal)}

/-- Equations (97),(99),(106), PDF p.18: upper self-information tail, with
boundary randomization matched to the chosen counting-measure likelihood family. -/
def sourceTail {P : Source.{u}} (S : LikelihoodFamily (sourceSystem P))
    (a : ℝ) (k : ℕ) : ℝ≥0∞ := testingTypeI (S.tests (-a) k)

/-- Equations (101),(103), PDF p.18: spectral sup-entropy (upper=true)
and inf-entropy, using the limit-in-probability tail characterizations. -/
def spectralEntropy {P : Source.{u}} (S : LikelihoodFamily (sourceSystem P))
    (upper : Bool) : EReal :=
  if upper then sInf {z | ∃ a : ℝ, z = (a : EReal) ∧
    Tendsto (sourceTail S a) atTop (nhds 0)}
  else sSup {z | ∃ a : ℝ, z = (a : EReal) ∧
    Tendsto (sourceTail S a) atTop (nhds 1)}

/-- Equation (106), PDF p.18: liminf upper-tail exponent sigma(a)=eta(-a). -/
def sourceSigmaL {P : Source.{u}} (S : LikelihoodFamily (sourceSystem P)) (a : ℝ) : EReal :=
  liminf (fun k => blockErrorExponent k (sourceTail S a k)) atTop

/-- Theorem 7, PDF p.19: limsup exponent of the matched lower tail.
Acceptance rho[S(-a)] is the complement of sourceTail, including its boundary choice. -/
def sourceSigmaStarU {P : Source.{u}} (S : LikelihoodFamily (sourceSystem P)) (a : ℝ) : EReal :=
  limsup (fun k => blockErrorExponent k (hypothesisWeight (sourceSystem P k) false (S.tests (-a) k))) atTop

/-- Theorem 7, PDF p.19: threshold b0, with real thresholds embedded in EReal. -/
def sourceCutoff {P : Source.{u}} (S : LikelihoodFamily (sourceSystem P)) (r : ℝ) : EReal :=
  sSup {z | ∃ a : ℝ, (r : EReal) < sourceSigmaStarU S a ∧ z = (a : EReal)}

/-- Section VIII, PDF p.20: infinity-safe unconditional Han-form coding expression. -/
def revisedHanRate {P : Source.{u}} (S : LikelihoodFamily (sourceSystem P)) (r : ℝ) : EReal :=
  sInf {z | ∃ h : ℝ, 0 ≤ h ∧ z = (h : EReal) ∧
    (⨅ a : ℝ, max (sourceSigmaStarU S a) ((a - h : ℝ) : EReal)) ≤ (r : EReal)}

example (P : Source.{u}) (S : LikelihoodFamily (sourceSystem P)) (a : ℝ) :
    sourceSigmaL S a = etaL (S.tests (-a)) := by rfl

example (P : Source.{u}) (C : (k : ℕ) → StochasticSourceCode (P.X k)) :
    codeRate P C = limsup (fun k => perBlock k (Real.log ((C k).size : ℝ) : EReal)) atTop := by rfl

/-- Section VIII, PDF p.18: deterministic test of a finite acceptance region. -/
def finiteAcceptanceTest (P : Source.{u}) (k : ℕ) (A : Finset (P.X k)) :
    SimpleHypothesisTest (sourceSystem P k) :=
  fun x => if x ∈ A then ⟨1, by constructor <;> norm_num⟩ else ⟨0, by constructor <;> norm_num⟩

example (P : Source.{u}) (k : ℕ) (x : P.X k) :
    (finiteAcceptanceTest P k ∅ x).val = 0 := by simp [finiteAcceptanceTest]

/-- Section III, PDF p.4: the strict deterministic classical likelihood test. -/
def strictClassicalTest (C : ClassicalData.{u}) (k : ℕ) (a : ℝ) : SimpleHypothesisTest (.classical C) :=
  fun x => if (C.rho x : ℝ) > Real.exp (((k : ℝ) + 1) * a) * (C.sigma x : ℝ)
    then ⟨1, by constructor <;> norm_num⟩ else ⟨0, by constructor <;> norm_num⟩

/-- Section III, PDF p.4: strict tests as an actual chosen likelihood family. -/
def strictClassicalFamily (C : ℕ → ClassicalData.{u}) :
    LikelihoodFamily (fun k => .classical (C k)) where
  tests := fun a k => strictClassicalTest (C k) k a
  valid := by
    intro a k x
    constructor
    · intro h
      simp [strictClassicalTest, h]
    · intro h
      simp [strictClassicalTest, not_lt_of_ge (le_of_lt h)]

/-- Example 3, PDF p.16, (86)–(87): the explicit two-point distributions.
The theorem supplies b_k>0,c>0, so both coordinates are genuine probabilities. -/
def twoPointData (b : ℕ → ℝ) (c : ℝ) (k : ℕ) : ClassicalData where
  X := Bool
  countableX := inferInstance
  rho := fun x => Real.toNNReal (if x then 1 - Real.exp (-((k : ℝ) + 1) * b k)
    else Real.exp (-((k : ℝ) + 1) * b k))
  sigma := fun x => Real.toNNReal (if x then 1 - Real.exp (-((k : ℝ) + 1) * c)
    else Real.exp (-((k : ℝ) + 1) * c))

/-- Example 3, PDF p.16: reverse the two classical hypotheses. -/
def reverseClassical (C : ClassicalData.{u}) : ClassicalData.{u} :=
  ⟨C.X, C.countableX, C.sigma, C.rho⟩

example (C : ClassicalData.{u}) : reverseClassical (reverseClassical C) = C := by
  cases C
  rfl

example (Q : QuantumData.{u}) : positiveTrace Q 0 = 0 := by
  simp [positiveTrace]

end QAlgorithms.Papers.Independent.Claimed50.P46


