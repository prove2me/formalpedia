-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P28
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T00:27:01.696555+00:00
-- url     : https://prove2.me/theorems/a2659e25-1e77-444a-b714-ebf04144a35b
-- title:
--   Definitions for $f$-divergence Inequalities
-- statement:
--   The objects the formalized statements of *$f$-divergence Inequalities* (arXiv:1508.00335) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LogBase`: Common logarithm base, footnote 5, PDF p.7.
--   - `logB`: Source logarithm, PDF p.7.
--   - `logBaseE`: The scalar `log e`, PDF pp.7,9.
--   - `expB`: Source exponential, PDF p.7.
--   - `elogB`: Extended logarithm, with log 0 = -infinity, PDF p.7.
--   - `eIntegral`: Signed extended expectation, used only with integrable negative part.
--   - `generatorAtZero`: Right endpoint limit of a convex generator, (33), PDF p.8.
--   - `generatorConjugate`: Conjugate generator, (34), PDF p.8.
--   - `generatorValue`: Continuous extension at zero, (33), PDF p.8.
--   - `fDiv`: Full singular-mass extension (30),(33)--(37), PDF p.8.
--   - `Generator`: Normalized convex generator on the open positive half-line, PDF p.8.
--   - `StrictAtOne`: Strict convexity at 1, rather than global strict convexity, Proposition 1, p.9.
--   - `PositiveGenerator`: Positivity away from 1, Theorem 1, PDF p.13.
--   - `nDiv`: Nonnegative value of a normalized convex-generator divergence.
--   - `kl`: KL in the chosen base, (28),(43), PDF pp.7,9.
--   - `rnDensityReal`: Real rnDensityReal, finite almost everywhere under a finite reference measure.
--   - `fullVariation`: Full L1 total variation, including singular mass, (55)--(58), PDF p.10.
--   - `chiSquareDiv`: Chi-square divergence, with infinite value when P is not AC, (47), p.9.
--   - `triangularGenerator`: Triangular generator, (60), PDF p.10.
--   - `triangular`: Triangular discrimination, (59), PDF p.10.
--   - `marton`: Marton's squared divergence through its exact f-generator (73)--(74), p.11.
--   - `martonSum`: Symmetric Marton sum, PDF p.20.
--   - `probabilityMixture`: Probability probabilityMixture, used at (63),(457).
--   - `js`: Jensen--Shannon without the factor 1/2, (63), PDF p.10.
--   - `hellingerOrderGenerator`: Hellinger generator, (53), PDF p.10.
--   - `hellinger`: Hellinger divergence, with H_1 = KL in nats, (52)--(54), PDF p.10.
--   - `hockey`: Hockey-stick divergence with singular extension, (66)--(67), PDF p.11.
--   - `renyiDiv`: Renyi divergence for orders other than 0,1 via its extended moment, (75), p.12.
--   - `upperDensity`: Upper essential rnDensityReal, with infinity in the non-AC case, (79),(149).
--   - `inverseUpperDensity`: Beta_1(P,Q); beta_2(P,Q) is inverseUpperDensity Q P, (149)--(152), PDF pp.22--23.
--   - `relativeInfo`: Relative information with the source's infinite endpoints, (26), PDF p.7.
--   - `informationSpectrum`: CDF under P, (27), PDF p.7.
--   - `r`: Normalized shannonEntropyBase generator r, (43), PDF p.9.
--   - `jsBaseGenerator`: Jensen--Shannon generator, (65), PDF p.11.
--   - `functionalConstant`: Functional supremum; ENNReal retains an infinite optimal coefficient, (86).
--   - `densityInterval`: The restricted open rnDensityReal interval in (163), including unbounded endpoints.
--   - `ClassicalDivergenceFamily`: Polymorphic divergence, so sharp constants quantify over every alphabet.
--   - `PairCondition`: Polymorphic admissibility predicate.
--   - `acPairs`: AC domain for sharp comparisons.
--   - `mutualPairs`: Mutual-AC domain for sharp comparisons.
--   - `exactPairs`: Exact essential bounds, not unrelated free parameters.
--   - `UniversalBound`: All-alphabet upper comparison. Probability normalization is mandatory.
--   - `Sharp`: Best universal multiplicative coefficient, including infinite constants.
--   - `entropyKernel`: The ratio in (172), continuously extended at 1.
--   - `samsonKernel`: Kernel (134), PDF p.20. Used away from 1.
--   - `entropyHellingerKernel`: Continuous kernel (176) with all four endpoint cases, PDF pp.26--27.
--   - `jsTriangularKernel`: Kernel (187), including t=0,1,infinity, PDF p.28.
--   - `triangularTVKernel`: Kernel (188), including infinity, PDF p.28.
--   - `jsHellingerKernel`: Kernel (195); the maximum for alpha<1 ranges over the entire interval.
--   - `reversePinskerPhi`: Phi of (333), PDF p.47.
--   - `scalarLogSecant`: Smooth continuous extension in (539), PDF p.76.
--   - `phiAlpha`: Phi_alpha of (536),(537), PDF pp.75--76; its value at 1 is alpha/(alpha-1).
--   - `triangularC1`: Exact coefficients in Theorem 3, (117),(119)--(120), PDF p.18.
--   - `triangularC2`: Least scalar correction in (119), avoiding rounded decimal constants.
--   - `KLLinearBound`: KL/TV/chiSquareDiv-square bound with both scalar coefficients, (97), PDF p.15.
--   - `symmetricKL`: Symmetric KL and chiSquareDiv-square divergences in (98).
--   - `symmetricChi`: Symmetric chiSquareDiv-square sum in (98), PDF p.15.
--   - `binary`: Binary law with mass p at false; valid for p in [0,1].
--   - `binaryKL`: Two-sided binary relative shannonEntropyBase on its finite domain, (310), PDF p.43.
--   - `spectrumEnvelope`: Lower informationSpectrum envelope (277), PDF p.39.
--   - `absInfo`: Absolute and negative information moments; extended, not default-zero.
--   - `negativeInfo`: Negative information moment in (288), PDF p.41.
--   - `momentKLBound`: Continuous limiting RHS of (292), PDF p.41; explicit infinite/zero cases.
--   - `kernelMean`: The conditional mean from one common Markov kernel, Lemma 1, PDF p.33.
--   - `jensenGap`: Jensen gap from that kernel, with extended outer expectation, (228).
--   - `tGamma`: Secondary-branch Lambert root, equivalently gamma ln t = t-1, (435), p.61. Theorem 33 asserts existence and uniqueness on the stated gamma>1 domain.
--   - `hockeyKLConstant`: Exact optimal coefficient (434), before the probability pair is chosen.
--   - `spectrumCoefficient`: Open-interval objective minimum (461); attainment is stated in Theorem 34.
--   - `cGammaApprox`: Approximation (453)--(454) with the exact printed decimal 1.1791, p.63.
--   - `tailMoment`: Tail moment zeta (470) expressed through its nonnegative rnDensityReal.
--   - `cdfMoment`: The nonnegative CDF rnDensityReal inverseUpperDensity^(alpha-2) F(log inverseUpperDensity), (471)--(472). This is pointwise inverseUpperDensity^(alpha-2)-zeta, not a difference of infinite integrals.
--   - `truncatedSecond`: Nonnegative truncated rnDensityReal moment in Remark 28, PDF p.48.
--   - `FiniteProbabilityLaw`: Nonnegative normalized probability vector on a finite alphabet.
--   - `finiteTV`: Full L1 distance and unweighted squared l2 distance for finite laws.
--   - `finiteL2`: Unweighted squared Euclidean distance in (373), PDF p.51.
--   - `finiteKL`: Finite KL on the strictly-positive-reference domain used below.
--   - `finiteChi`: Finite chiSquareDiv-square on the strictly-positive-reference domain.
--   - `minReferenceMass`: Minimum and maximum symbol mass; n>1 in every theorem using them.
--   - `qMax`: Largest finite-alphabet mass, PDF p.56.
--   - `finiteBeta2`: Reverse essential rnDensityReal bound when Q is strictly positive.
--   - `shannonEntropyBase`: Shannon shannonEntropyBase with continuous zero-mass convention, PDF p.52.
--   - `uniformLaw`: Equiprobable vector.
--   - `binaryEntropyBase`: Binary shannonEntropyBase, PDF p.52.
--   - `entropyMaxLaw`: The two-level attaining law (378), indexed from zero.
--   - `uniformEntropyThreshold`: Threshold sequence (379), PDF p.53.
--   - `entropyMinLaw`: The attaining law (381), indexed from zero, PDF p.53.
--   - `balance`: Balance coefficient (390), for the finite setting of Theorem 30.
--   - `balancePhi`: Phi in (391), distinct from the rnDensityReal function (333).
--   - `RelativeCoordinateTypical`: Strong typicality closed relative-coordinate ball, (389), PDF p.54.
--   - `typicalExponent`: Exponent (388) as an extended infimum over the open complement. The proof (396) takes limits, so a minimum is not substituted for an infimum.
--   - `ratioEndpoint`: Extended scalar endpoint of f/g; no quotient of infinite limits.
--   - `scalarInterval`: Open scalar interval (163) at fixed betas, including zero betas.
--   - `LowerSharp`: Sharp lower-coefficient counterpart of Sharp.
--   - `uAlpha`: Signed u_alpha in (511); the printed nonnegative codomain is a typo for alpha<1.
--   - `renyiKLTransform`: Logarithmic KL transform (512)--(515); toENNReal is the positive part.
--   - `renyiLower`: Complete lower expression in parts (a),(b) of Theorem 38.
--   - `renyiUpper`: Complete upper expression in parts (a),(b) of Theorem 38.
--   - `expNeg`: exp_b(-D), with its zero endpoint at infinite D.
--   - `deltaBar`: Delta-bar of (517), with the square root covering the whole minimum.
--   - `renyiDeltaBound`: Scalar endpoint-safe TV transform (516).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, https://arxiv.org/abs/1508.00335v7

import Mathlib

/-!
Statements from Sason and Verdu, arXiv:1508.00335v7.
All definitions are local to this paper. KL uses Mathlib's extended nats primitive;
TV is the full L1 distance. Signed extended expectations use positive and negative
parts, never a nonintegrable Bochner integral. Theorems are statement targets only.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Common logarithm base, footnote 5, PDF p.7. -/
structure LogBase where
  val : ℝ
  one_lt : 1 < val

/-- Source logarithm, PDF p.7. -/
def logB (b : LogBase) (t : ℝ) : ℝ := Real.log t / Real.log b.val

/-- The scalar `log e`, PDF pp.7,9. -/
def logBaseE (b : LogBase) : ℝ := 1 / Real.log b.val

/-- Source exponential, PDF p.7. -/
def expB (b : LogBase) (t : ℝ) : ℝ := Real.exp (t * Real.log b.val)

/-- Extended logarithm, with log 0 = -infinity, PDF p.7. -/
def elogB (b : LogBase) (t : ℝ≥0∞) : EReal := ENNReal.log t * (logBaseE b : EReal)

/-- Signed extended expectation, used only with integrable negative part. -/
def eIntegral {A : Type*} [MeasurableSpace A] (P : Measure A) (h : A → EReal) : EReal :=
  ((∫⁻ x, (h x).toENNReal ∂P) : EReal) - ((∫⁻ x, (-h x).toENNReal ∂P) : EReal)

/-- Right endpoint limit of a convex generator, (33), PDF p.8. -/
def generatorAtZero (f : ℝ → ℝ) : EReal :=
  Filter.liminf (fun t : ℝ => (f t : EReal)) (nhdsWithin 0 (Ioi 0))

/-- Conjugate generator, (34), PDF p.8. -/
def generatorConjugate (f : ℝ → ℝ) (t : ℝ) : ℝ := t * f t⁻¹

/-- Continuous extension at zero, (33), PDF p.8. -/
def generatorValue (f : ℝ → ℝ) (t : ℝ) : EReal :=
  if t = 0 then generatorAtZero f else (f t : EReal)

/-- Full singular-mass extension (30),(33)--(37), PDF p.8. -/
def fDiv {A : Type*} [MeasurableSpace A] (f : ℝ → ℝ) (P Q : Measure A) : EReal :=
  eIntegral Q (fun x => generatorValue f (P.rnDeriv Q x).toReal) +
    generatorAtZero (generatorConjugate f) * ((P.singularPart Q) univ : EReal)

/-- Normalized convex generator on the open positive half-line, PDF p.8. -/
def Generator (f : ℝ → ℝ) : Prop := ConvexOn ℝ (Ioi 0) f ∧ f 1 = 0

/-- Strict convexity at 1, rather than global strict convexity, Proposition 1, p.9. -/
def StrictAtOne (f : ℝ → ℝ) : Prop :=
  ∀ x y a : ℝ, 0 < x → x < 1 → 1 < y → 0 < a → a < 1 →
    a * x + (1 - a) * y = 1 → f 1 < a * f x + (1 - a) * f y

/-- Positivity away from 1, Theorem 1, PDF p.13. -/
def PositiveGenerator (f : ℝ → ℝ) : Prop :=
  Generator f ∧ ∀ t : ℝ, 0 < t → t ≠ 1 → 0 < f t

/-- Nonnegative value of a normalized convex-generator divergence. -/
def nDiv {A : Type*} [MeasurableSpace A] (f : ℝ → ℝ) (P Q : Measure A) : ℝ≥0∞ :=
  (fDiv f P Q).toENNReal

/-- KL in the chosen base, (28),(43), PDF pp.7,9. -/
def kl {A : Type*} [MeasurableSpace A] (b : LogBase) (P Q : Measure A) : ℝ≥0∞ :=
  ENNReal.ofReal (logBaseE b) * InformationTheory.klDiv P Q

/-- Real rnDensityReal, finite almost everywhere under a finite reference measure. -/
def rnDensityReal {A : Type*} [MeasurableSpace A] (P Q : Measure A) (x : A) : ℝ :=
  (P.rnDeriv Q x).toReal

/-- Full L1 total variation, including singular mass, (55)--(58), PDF p.10. -/
def fullVariation {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal |rnDensityReal P (P + Q) x - rnDensityReal Q (P + Q) x| ∂(P + Q)

/-- Chi-square divergence, with infinite value when P is not AC, (47), p.9. -/
def chiSquareDiv {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  if P ≪ Q then ∫⁻ x, ENNReal.ofReal ((rnDensityReal P Q x - 1) ^ 2) ∂Q else ∞

/-- Triangular generator, (60), PDF p.10. -/
def triangularGenerator (t : ℝ) : ℝ := (t - 1) ^ 2 / (t + 1)

/-- Triangular discrimination, (59), PDF p.10. -/
def triangular {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  nDiv triangularGenerator P Q

/-- Marton's squared divergence through its exact f-generator (73)--(74), p.11. -/
def marton {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  nDiv (fun t => if t < 1 then (t - 1) ^ 2 else 0) P Q

/-- Symmetric Marton sum, PDF p.20. -/
def martonSum {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  marton P Q + marton Q P

/-- Probability probabilityMixture, used at (63),(457). -/
def probabilityMixture {A : Type*} [MeasurableSpace A] (P Q : Measure A) (t : ℝ) : Measure A :=
  ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q

/-- Jensen--Shannon without the factor 1/2, (63), PDF p.10. -/
def js {A : Type*} [MeasurableSpace A] (b : LogBase) (P Q : Measure A) : ℝ≥0∞ :=
  kl b P (probabilityMixture P Q (1 / 2)) + kl b Q (probabilityMixture P Q (1 / 2))

/-- Hellinger generator, (53), PDF p.10. -/
def hellingerOrderGenerator (a t : ℝ) : ℝ := (Real.rpow t a - 1) / (a - 1)

/-- Hellinger divergence, with H_1 = KL in nats, (52)--(54), PDF p.10. -/
def hellinger {A : Type*} [MeasurableSpace A] (a : ℝ) (P Q : Measure A) : ℝ≥0∞ :=
  if a = 1 then InformationTheory.klDiv P Q else nDiv (hellingerOrderGenerator a) P Q

/-- Hockey-stick divergence with singular extension, (66)--(67), PDF p.11. -/
def hockey {A : Type*} [MeasurableSpace A] (g : ℝ) (P Q : Measure A) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (max (rnDensityReal P Q x - g) 0) ∂Q) + (P.singularPart Q) univ

/-- Renyi divergence for orders other than 0,1 via its extended moment, (75), p.12. -/
def renyiDiv {A : Type*} [MeasurableSpace A] (b : LogBase) (a : ℝ)
    (P Q : Measure A) : EReal :=
  if a = 0 then -elogB b (Q {x | 0 < P.rnDeriv Q x})
  else if a = 1 then (kl b P Q : EReal)
  else ((1 / (a - 1) : ℝ) : EReal) * elogB b (∫⁻ x, (P.rnDeriv Q x) ^ a ∂Q)

/-- Upper essential rnDensityReal, with infinity in the non-AC case, (79),(149). -/
def upperDensity {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  if P ≪ Q then essSup (P.rnDeriv Q) Q else ∞

/-- Beta_1(P,Q); beta_2(P,Q) is inverseUpperDensity Q P, (149)--(152), PDF pp.22--23. -/
def inverseUpperDensity {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ :=
  ((upperDensity P Q)⁻¹).toReal

/-- Relative information with the source's infinite endpoints, (26), PDF p.7. -/
def relativeInfo {A : Type*} [MeasurableSpace A] (b : LogBase) (P Q : Measure A) (x : A) : EReal :=
  elogB b (P.rnDeriv Q x)

/-- CDF under P, (27), PDF p.7. -/
def informationSpectrum {A : Type*} [MeasurableSpace A] (b : LogBase) (P Q : Measure A)
    (a : EReal) : ℝ≥0∞ := P {x | relativeInfo b P Q x ≤ a}

/-- Normalized shannonEntropyBase generator r, (43), PDF p.9. -/
def r (b : LogBase) (t : ℝ) : ℝ := t * logB b t + (1 - t) * logBaseE b

/-- Jensen--Shannon generator, (65), PDF p.11. -/
def jsBaseGenerator (b : LogBase) (t : ℝ) : ℝ :=
  t * logB b t - (t + 1) * logB b ((t + 1) / 2)

/-- Functional supremum; ENNReal retains an infinite optimal coefficient, (86). -/
def functionalConstant (f g : ℝ → ℝ) (S : Set ℝ := Ioi 0 \ {1}) : ℝ≥0∞ :=
  ⨆ t : S, ENNReal.ofReal (f t / g t)

/-- The restricted open rnDensityReal interval in (163), including unbounded endpoints. -/
def densityInterval {A : Type*} [MeasurableSpace A] (P Q : Measure A) : Set ℝ :=
  {t | inverseUpperDensity Q P < t ∧ (ENNReal.ofReal t) < upperDensity P Q ∧ t ≠ 1}

/-- Polymorphic divergence, so sharp constants quantify over every alphabet. -/
abbrev ClassicalDivergenceFamily := ∀ {A : Type u} [MeasurableSpace A], Measure A → Measure A → ℝ≥0∞

/-- Polymorphic admissibility predicate. -/
abbrev PairCondition := ∀ {A : Type u} [MeasurableSpace A], Measure A → Measure A → Prop

/-- AC domain for sharp comparisons. -/
def acPairs : PairCondition := fun P Q => P ≪ Q

/-- Mutual-AC domain for sharp comparisons. -/
def mutualPairs : PairCondition := fun P Q => P ≪ Q ∧ Q ≪ P

/-- Exact essential bounds, not unrelated free parameters. -/
def exactPairs (b1 b2 : ℝ) : PairCondition :=
  fun P Q => inverseUpperDensity P Q = b1 ∧ inverseUpperDensity Q P = b2

/-- All-alphabet upper comparison. Probability normalization is mandatory. -/
def UniversalBound (F G : ClassicalDivergenceFamily.{u}) (D : PairCondition.{u}) (c : ℝ≥0∞) : Prop :=
  ∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q], D P Q → F P Q ≤ c * G P Q

/-- Best universal multiplicative coefficient, including infinite constants. -/
def Sharp (F G : ClassicalDivergenceFamily.{u}) (D : PairCondition.{u}) (c : ℝ≥0∞) : Prop :=
  IsLeast {k | UniversalBound F G D k} c

/-- The ratio in (172), continuously extended at 1. -/
def entropyKernel (b : LogBase) (t : ℝ) : ℝ :=
  if t = 1 then 1 else r b t / ((t - 1) * logBaseE b - logB b t)

/-- Kernel (134), PDF p.20. Used away from 1. -/
def samsonKernel (b : LogBase) (t : ℝ) : ℝ :=
  (t - 1) ^ 2 / (r b t * max 1 t)

/-- Continuous kernel (176) with all four endpoint cases, PDF pp.26--27. -/
def entropyHellingerKernel (b : LogBase) (a : ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = 0 then ENNReal.ofReal (logBaseE b)
  else if t = 1 then ENNReal.ofReal (logBaseE b / a)
  else if t = ∞ then if a < 1 then ∞ else 0
  else ENNReal.ofReal ((1 - a) * r b t.toReal /
    (1 - Real.rpow t.toReal a + a * t.toReal - a))

/-- Kernel (187), including t=0,1,infinity, PDF p.28. -/
def jsTriangularKernel (b : LogBase) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = 0 ∨ t = ∞ then ENNReal.ofReal (logB b 2)
  else if t = 1 then ENNReal.ofReal (logBaseE b / 2)
  else ENNReal.ofReal ((t.toReal + 1) / (t.toReal - 1) ^ 2 * jsBaseGenerator b t.toReal)

/-- Kernel (188), including infinity, PDF p.28. -/
def triangularTVKernel (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = ∞ then 1 else ENNReal.ofReal (|t.toReal - 1| / (t.toReal + 1))

/-- Kernel (195); the maximum for alpha<1 ranges over the entire interval. -/
def jsHellingerKernel (b : LogBase) (a : ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = 0 then ENNReal.ofReal (logB b 2)
  else if t = 1 then ENNReal.ofReal (logBaseE b / (2 * a))
  else if t = ∞ then ENNReal.ofReal (max (1 / a - 1) 0 * logB b 2)
  else ENNReal.ofReal ((a - 1) * jsBaseGenerator b t.toReal /
    (Real.rpow t.toReal a + a - 1 - a * t.toReal))

/-- Phi of (333), PDF p.47. -/
def reversePinskerPhi (b : LogBase) (t : ℝ) : ℝ :=
  if t = 0 then 0 else if t = 1 then logBaseE b else t * logB b t / (t - 1)

/-- Smooth continuous extension in (539), PDF p.76. -/
def scalarLogSecant (t : ℝ) : ℝ := if t = 1 then 1 else Real.log t / (t - 1)

/-- Phi_alpha of (536),(537), PDF pp.75--76; its value at 1 is alpha/(alpha-1). -/
def phiAlpha (a t : ℝ) : ℝ :=
  if t = 1 then a / (a - 1)
  else (1 - Real.rpow t a) * Real.log t /
    ((t - 1) * (1 - Real.rpow t (a - 1)))

example (b : LogBase) : logB b 1 = 0 := by simp [logB]

example (b : LogBase) : r b 1 = 0 := by simp [r, logB]

example : triangularGenerator 1 = 0 := by norm_num [triangularGenerator]

example : scalarLogSecant 1 = 1 := by simp [scalarLogSecant]

example (b : LogBase) : reversePinskerPhi b 0 = 0 ∧ reversePinskerPhi b 1 = logBaseE b := by simp [reversePinskerPhi]

example (b : LogBase) (a : ℝ) : entropyHellingerKernel b a 0 = ENNReal.ofReal (logBaseE b) := by
  simp [entropyHellingerKernel]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) (h : ¬ P ≪ Q) : chiSquareDiv P Q = ∞ := by
  simp [chiSquareDiv, h]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) : probabilityMixture P Q 0 = P := by
  simp [probabilityMixture]

/-- Exact coefficients in Theorem 3, (117),(119)--(120), PDF p.18. -/
def triangularC1 (b : LogBase) : ℝ≥0∞ :=
  functionalConstant (fun t => triangularGenerator t * logBaseE b) (r b)

/-- Least scalar correction in (119), avoiding rounded decimal constants. -/
def triangularC2 (b : LogBase) : ℝ≥0∞ :=
  sInf {c | ∀ t : ℝ, 0 < t → t < 1 →
    ENNReal.ofReal (triangularGenerator t * logBaseE b) ≤
      ENNReal.ofReal (r b t) + ENNReal.ofReal (2 * (1 - t) * logBaseE b) * c}

/-- KL/TV/chiSquareDiv-square bound with both scalar coefficients, (97), PDF p.15. -/
def KLLinearBound (b : LogBase) (c1 c2 : ℝ≥0∞) : Prop :=
  ∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q], P ≪ Q →
      kl b P Q ≤ (c1 * fullVariation P Q + c2 * chiSquareDiv P Q) * ENNReal.ofReal (logBaseE b)

/-- Symmetric KL and chiSquareDiv-square divergences in (98). -/
def symmetricKL (b : LogBase) : ClassicalDivergenceFamily := fun P Q => kl b P Q + kl b Q P

/-- Symmetric chiSquareDiv-square sum in (98), PDF p.15. -/
def symmetricChi : ClassicalDivergenceFamily := fun P Q => chiSquareDiv P Q + chiSquareDiv Q P

/-- Binary law with mass p at false; valid for p in [0,1]. -/
def binary (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac false + ENNReal.ofReal (1 - p) • Measure.dirac true

/-- Two-sided binary relative shannonEntropyBase on its finite domain, (310), PDF p.43. -/
def binaryKL (b : LogBase) (x y : ℝ) : ℝ :=
  x * logB b (x / y) + (1 - x) * logB b ((1 - x) / (1 - y))

/-- Lower informationSpectrum envelope (277), PDF p.39. -/
def spectrumEnvelope (v t : ℝ) : ℝ :=
  if t ≤ 2 / (2 - v) then 0 else 1 - t * v / (2 * (t - 1))

/-- Absolute and negative information moments; extended, not default-zero. -/
def absInfo {A : Type*} [MeasurableSpace A] (b : LogBase) (P Q : Measure A) : ℝ≥0∞ :=
  ∫⁻ x, (max (relativeInfo b P Q x) (-relativeInfo b P Q x)).toENNReal ∂P

/-- Negative information moment in (288), PDF p.41. -/
def negativeInfo {A : Type*} [MeasurableSpace A] (b : LogBase) (P Q : Measure A) : ℝ≥0∞ :=
  ∫⁻ x, (-relativeInfo b P Q x).toENNReal ∂P

/-- Continuous limiting RHS of (292), PDF p.41; explicit infinite/zero cases. -/
def momentKLBound (b : LogBase) (c d : ℝ≥0∞) : EReal :=
  if c = ∞ then ⊤
  else if c = 0 ∧ d = 0 then 0
  else if d = ∞ then (logB b (1 + c.toReal) : EReal)
  else (logB b (1 + c.toReal) - (3 / 2 : ℝ) * c.toReal ^ 2 * logBaseE b /
    ((1 + d.toReal) * (1 + c.toReal) ^ 2 - 1) : ℝ)

example (b : LogBase) : momentKLBound b 0 0 = 0 := by simp [momentKLBound]

example (b : LogBase) (d : ℝ≥0∞) : momentKLBound b ∞ d = ⊤ := by simp [momentKLBound]

example : binary 0 = Measure.dirac true := by simp [binary]

/-- The conditional mean from one common Markov kernel, Lemma 1, PDF p.33. -/
def kernelMean {A : Type*} [MeasurableSpace A] (K : ProbabilityTheory.Kernel A ℝ) (x : A) : ℝ :=
  ∫ z, z ∂K x

/-- Jensen gap from that kernel, with extended outer expectation, (228). -/
def jensenGap {A : Type*} [MeasurableSpace A] (f : ℝ → ℝ)
    (P : Measure A) (K : ProbabilityTheory.Kernel A ℝ) : EReal :=
  eIntegral P (fun x => (f (kernelMean K x) : EReal)) - (f (∫ x, kernelMean K x ∂P) : EReal)

/-- Secondary-branch Lambert root, equivalently gamma ln t = t-1, (435), p.61.
Theorem 33 asserts existence and uniqueness on the stated gamma>1 domain. -/
def tGamma (g : ℝ) : ℝ := sInf {t : ℝ | g < t ∧ g * Real.log t = t - 1}

/-- Exact optimal coefficient (434), before the probability pair is chosen. -/
def hockeyKLConstant (b : LogBase) (g : ℝ) : ℝ := (tGamma g - g) / r b (tGamma g)

/-- Open-interval objective minimum (461); attainment is stated in Theorem 34. -/
def spectrumCoefficient (b : LogBase) (t : ℝ) : ℝ :=
  sInf ((fun g : ℝ => t * hockeyKLConstant b g / (t - g)) '' Ioo 1 t)

/-- Approximation (453)--(454) with the exact printed decimal 1.1791, p.63. -/
def cGammaApprox (b : LogBase) (g : ℝ) : ℝ :=
  let d := (11791 / 10000 : ℝ) * g * Real.log g
  d / ((d + g) * logB b ((d + g) / Real.exp 1) + logBaseE b)

/-- Tail moment zeta (470) expressed through its nonnegative rnDensityReal. -/
def tailMoment {A : Type*} [MeasurableSpace A] (b : LogBase) (a : ℝ) (P Q : Measure A)
    (lo hi : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | lo < ENNReal.ofReal t ∧ ENNReal.ofReal t < hi},
    (ENNReal.ofReal t) ^ (a - 2) * (1 - informationSpectrum b P Q (elogB b (ENNReal.ofReal t)))

/-- The nonnegative CDF rnDensityReal inverseUpperDensity^(alpha-2) F(log inverseUpperDensity), (471)--(472).
This is pointwise inverseUpperDensity^(alpha-2)-zeta, not a difference of infinite integrals. -/
def cdfMoment {A : Type*} [MeasurableSpace A] (b : LogBase) (a : ℝ) (P Q : Measure A)
    (lo hi : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | lo < ENNReal.ofReal t ∧ ENNReal.ofReal t < hi},
    (ENNReal.ofReal t) ^ (a - 2) * informationSpectrum b P Q (elogB b (ENNReal.ofReal t))

/-- Nonnegative truncated rnDensityReal moment in Remark 28, PDF p.48. -/
def truncatedSecond {A : Type*} [MeasurableSpace A] (P Q : Measure A) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (if 1 < rnDensityReal P Q x then rnDensityReal P Q x * (rnDensityReal P Q x - 1) else 0) ∂Q

example (b : LogBase) : cGammaApprox b 1 = 0 := by
  simp [cGammaApprox]

example {A : Type*} [MeasurableSpace A] (b : LogBase) (a : ℝ) (P Q : Measure A) (lo : ℝ≥0∞) :
    tailMoment b a P Q lo lo = 0 := by
  have he : {t : ℝ | lo < ENNReal.ofReal t ∧ ENNReal.ofReal t < lo} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => (lt_trans h.1 h.2).false
  simp [tailMoment, he]

/-- Nonnegative normalized probability vector on a finite alphabet. -/
def FiniteProbabilityLaw {n : ℕ} (p : Fin n → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Full L1 distance and unweighted squared l2 distance for finite laws. -/
def finiteTV {n : ℕ} (p q : Fin n → ℝ) : ℝ := ∑ i, |p i - q i|

/-- Unweighted squared Euclidean distance in (373), PDF p.51. -/
def finiteL2 {n : ℕ} (p q : Fin n → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2

/-- Finite KL on the strictly-positive-reference domain used below. -/
def finiteKL {n : ℕ} (b : LogBase) (p q : Fin n → ℝ) : ℝ :=
  ∑ i, p i * logB b (p i / q i)

/-- Finite chiSquareDiv-square on the strictly-positive-reference domain. -/
def finiteChi {n : ℕ} (p q : Fin n → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2 / q i

/-- Minimum and maximum symbol mass; n>1 in every theorem using them. -/
def minReferenceMass {n : ℕ} (q : Fin n → ℝ) : ℝ := sInf (Set.range q)

/-- Largest finite-alphabet mass, PDF p.56. -/
def qMax {n : ℕ} (q : Fin n → ℝ) : ℝ := sSup (Set.range q)

/-- Reverse essential rnDensityReal bound when Q is strictly positive. -/
def finiteBeta2 {n : ℕ} (p q : Fin n → ℝ) : ℝ := sInf (Set.range (fun i => p i / q i))

/-- Shannon shannonEntropyBase with continuous zero-mass convention, PDF p.52. -/
def shannonEntropyBase {n : ℕ} (b : LogBase) (p : Fin n → ℝ) : ℝ := -∑ i, p i * logB b (p i)

/-- Equiprobable vector. -/
def uniformLaw (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

/-- Binary shannonEntropyBase, PDF p.52. -/
def binaryEntropyBase (b : LogBase) (p : ℝ) : ℝ := -p * logB b p - (1 - p) * logB b (1 - p)

/-- The two-level attaining law (378), indexed from zero. -/
def entropyMaxLaw (n m : ℕ) (d : ℝ) : Fin n → ℝ := fun i =>
  if i.val < m then 1 / (n : ℝ) + d / (2 * m)
  else 1 / (n : ℝ) - d / (2 * ((n : ℝ) - m))

/-- Threshold sequence (379), PDF p.53. -/
def uniformEntropyThreshold (b : LogBase) (n k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = n - 1 then logB b n
  else binaryEntropyBase b ((k : ℝ) / n) + (k : ℝ) / n * logB b k

/-- The attaining law (381), indexed from zero, PDF p.53. -/
def entropyMinLaw (n k : ℕ) (t : ℝ) : Fin n → ℝ := fun i =>
  if i.val = 0 then 1 - ((k : ℝ) - 1 + t) / n
  else if i.val < k then 1 / (n : ℝ)
  else if i.val = k then t / (n : ℝ) else 0

/-- Balance coefficient (390), for the finite setting of Theorem 30. -/
def balance {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  sInf {z : ℝ | ∃ S : Finset (Fin n), (1 / 2 : ℝ) ≤ ∑ i ∈ S, q i ∧ z = ∑ i ∈ S, q i}

/-- Phi in (391), distinct from the rnDensityReal function (333). -/
def balancePhi (b : LogBase) (p : ℝ) : ℝ :=
  if p = 1 / 2 then logBaseE b / 2 else logB b ((1 - p) / p) / (4 * (1 - 2 * p))

/-- Strong typicality closed relative-coordinate ball, (389), PDF p.54. -/
def RelativeCoordinateTypical {n : ℕ} (q p : Fin n → ℝ) (d : ℝ) : Prop :=
  ∀ i, |p i - q i| ≤ d * q i

/-- Exponent (388) as an extended infimum over the open complement.
The proof (396) takes limits, so a minimum is not substituted for an infimum. -/
def typicalExponent {n : ℕ} (b : LogBase) (q : Fin n → ℝ) (d : ℝ) : ℝ≥0∞ :=
  sInf {z : ℝ≥0∞ | ∃ p : Fin n → ℝ, FiniteProbabilityLaw p ∧ ¬ RelativeCoordinateTypical q p d ∧
    z = ENNReal.ofReal (finiteKL b p q)}

/-- Extended scalar endpoint of f/g; no quotient of infinite limits. -/
def ratioEndpoint (f g : ℝ → ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = 0 then Filter.liminf (fun x : ℝ => ENNReal.ofReal (f x / g x)) (nhdsWithin 0 (Ioi 0))
  else if t = ∞ then Filter.liminf (fun x : ℝ => ENNReal.ofReal (f x / g x)) atTop
  else ENNReal.ofReal (f t.toReal / g t.toReal)

/-- Open scalar interval (163) at fixed betas, including zero betas. -/
def scalarInterval (b1 b2 : ℝ) : Set ℝ :=
  {t | 0 < t ∧ b2 < t ∧ (b1 = 0 ∨ t < b1⁻¹) ∧ t ≠ 1}

/-- Sharp lower-coefficient counterpart of Sharp. -/
def LowerSharp (F G : ClassicalDivergenceFamily.{u}) (D : PairCondition.{u}) (c : ℝ≥0∞) : Prop :=
  IsGreatest {k | ∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q], D P Q → k * G P Q ≤ F P Q} c

/-- Signed u_alpha in (511); the printed nonnegative codomain is a typo for alpha<1. -/
def uAlpha (b : LogBase) (a : ℝ) (t : ℝ≥0∞) : EReal :=
  ((a - 1 : ℝ) : EReal) * ((entropyHellingerKernel b a t)⁻¹ : EReal)

/-- Logarithmic KL transform (512)--(515); toENNReal is the positive part. -/
def renyiKLTransform (b : LogBase) (a : ℝ) (t D : ℝ≥0∞) : EReal :=
  ((1 / (a - 1) : ℝ) : EReal) * elogB b ((1 + uAlpha b a t * (D : EReal)).toENNReal)

/-- Complete lower expression in parts (a),(b) of Theorem 38. -/
def renyiLower {A : Type*} [MeasurableSpace A] (b : LogBase) (a : ℝ) (P Q : Measure A) : EReal :=
  if a < 1 then renyiKLTransform b a (upperDensity P Q) (kl b P Q)
  else max (kl b P Q : EReal) (renyiKLTransform b a (ENNReal.ofReal (inverseUpperDensity Q P)) (kl b P Q))

/-- Complete upper expression in parts (a),(b) of Theorem 38. -/
def renyiUpper {A : Type*} [MeasurableSpace A] (b : LogBase) (a : ℝ) (P Q : Measure A) : EReal :=
  if a < 1 then min (kl b P Q : EReal) (renyiKLTransform b a (ENNReal.ofReal (inverseUpperDensity Q P)) (kl b P Q))
  else min (elogB b (upperDensity P Q)) (renyiKLTransform b a (upperDensity P Q) (kl b P Q))

/-- exp_b(-D), with its zero endpoint at infinite D. -/
def expNeg (b : LogBase) (D : ℝ≥0∞) : ℝ≥0∞ :=
  if D = ∞ then 0 else ENNReal.ofReal (expB b (-D.toReal))

/-- Delta-bar of (517), with the square root covering the whole minimum. -/
def deltaBar (b : LogBase) (D : ℝ≥0∞) : ℝ≥0∞ :=
  (min (D / ENNReal.ofReal (2 * logBaseE b)) (1 - expNeg b D)) ^ (1 / 2 : ℝ)

/-- Scalar endpoint-safe TV transform (516). -/
def renyiDeltaBound (b : LogBase) (a : ℝ) (b1 : ℝ) (d : ℝ≥0∞) : EReal :=
  ((1 / (a - 1) : ℝ) : EReal) * elogB b ((1 + (d : EReal) *
    ((((ENNReal.ofReal b1) ^ (1 - a) : ℝ≥0∞) : EReal) - 1) /
      ((1 - b1 : ℝ) : EReal)).toENNReal)

example (n : ℕ) : finiteTV (uniformLaw n) (uniformLaw n) = 0 := by
  simp [finiteTV]

example (b : LogBase) : binaryEntropyBase b 0 = 0 := by simp [binaryEntropyBase, logB]

example (b : LogBase) (n : ℕ) : uniformEntropyThreshold b n 0 = 0 := by simp [uniformEntropyThreshold]

example {n : ℕ} (b : LogBase) (q : Fin n → ℝ) (d : ℝ)
    (h : ∀ p : Fin n → ℝ, FiniteProbabilityLaw p → RelativeCoordinateTypical q p d) : typicalExponent b q d = ∞ := by
  have he : {z : ℝ≥0∞ | ∃ p : Fin n → ℝ, FiniteProbabilityLaw p ∧ ¬ RelativeCoordinateTypical q p d ∧
      z = ENNReal.ofReal (finiteKL b p q)} = ∅ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, hn, _⟩
    exact hn (h p hp)
  simp [typicalExponent, he]

/-- Definition-family sanity checks: normalized and endpoint values, not target proofs. -/
example (f : ℝ → ℝ) : generatorConjugate f 1 = f 1 := by simp [generatorConjugate]

example (f : ℝ → ℝ) : generatorValue f 1 = (f 1 : EReal) := by simp [generatorValue]

example (b : LogBase) : elogB b 1 = 0 := by simp [elogB]

example {A : Type*} [MeasurableSpace A] (P : Measure A) : fullVariation P P = 0 := by simp [fullVariation]

example {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P] (b : LogBase) :
    kl b P P = 0 := by simp [kl]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) :
    hellinger 1 P Q = InformationTheory.klDiv P Q := by simp [hellinger]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) (b : LogBase) :
    renyiDiv b 1 P Q = (kl b P Q : EReal) := by simp [renyiDiv]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) : martonSum P Q = martonSum Q P := by
  simp [martonSum, add_comm]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) (h : ¬ P ≪ Q) : upperDensity P Q = ∞ := by
  simp [upperDensity, h]

example {A : Type*} [MeasurableSpace A] (P Q : Measure A) (h : ¬ P ≪ Q) : inverseUpperDensity P Q = 0 := by
  simp [inverseUpperDensity, upperDensity, h]

example (b : LogBase) : entropyKernel b 1 = 1 := by simp [entropyKernel]

example (b : LogBase) : jsTriangularKernel b 0 = ENNReal.ofReal (logB b 2) := by
  simp [jsTriangularKernel]

example : triangularTVKernel ∞ = 1 := by simp [triangularTVKernel]

example (b : LogBase) (a : ℝ) : jsHellingerKernel b a 0 = ENNReal.ofReal (logB b 2) := by
  simp [jsHellingerKernel]

example (a : ℝ) : phiAlpha a 1 = a / (a - 1) := by simp [phiAlpha]

example (b : LogBase) : balancePhi b (1 / 2) = logBaseE b / 2 := by simp [balancePhi]

example (b : LogBase) : expNeg b ∞ = 0 := by simp [expNeg]

example (n : ℕ) (p : Fin n → ℝ) : finiteTV p p = 0 ∧ finiteL2 p p = 0 := by
  simp [finiteTV, finiteL2]

example (b : LogBase) : shannonEntropyBase b (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [shannonEntropyBase, logB]

end QAlgorithms.Papers.Independent.Intakenext100.P28


