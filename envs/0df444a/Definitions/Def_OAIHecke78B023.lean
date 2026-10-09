-- Prove2me | Definitions.Def_OAIHecke78B023
-- name    : OAIHecke78B023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:15:19.136176+00:00
-- url     : https://prove2.me/theorems/126c109e-739c-41c1-ba89-64581e9023a7
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 24 of 29
-- statement:
--   Definitions bundle 24 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B021` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `CubicSieve.PairPrimes`, `CubicSieve.PairPoisson`, `Detector.CalibrationFourier`, `Detector.PhysicalCoefficient`, `Detector.PhysicalPoisson`, `Detector.FrequencySupport`, `Detector.Windows`, `Detector.CalibrationRemoval`, `Detector.ReciprocityCRT`, `Detector.CompletedCoefficient`, `PrimeRows.Continuation`, `PrimeRows.Agreement`, `Detector.HighAbsolute`, `Detector.CoefficientDirect`, `Detector.SpectralPoisson`, `Detector.RadialSpectral`, `Detector.Transformed`, `Detector.PhysicalRadial`, `Detector.NestedMellin`, `Detector.RawRadialJoin`, `Detector.SixthDecomposition`, `PrimeRows.Selected`, `PrimeRows.RestoreCorrection`, `PrimeRows.CentralSplit`, `Detector.CentralRepeatedChoices`, `Detector.PhysicalRows`, `Detector.GaussianCompensation`, `Detector.GaussianPhysicalTail`, `Detector.LowRowMellin`, `Detector.LowCauchy`, `Detector.LowColumnBounds`, `Detector.LowActualEnergies`, `Detector.GaussianPhysicalMass`, `Detector.GaussianSubset`, `Detector.GramLatticeWindow`, `Detector.GramSourceDivisors`, `Detector.LowSlotSplit`, `Detector.LowSlotPolynomial`, `Detector.LowSlotMarks`, `Detector.LowSlotWeights`, `Detector.LowTupleGram`, `Detector.LowNominalGeometry`, `Reflection.OriginalWeights`, `Detector.LowGaussianDyad`, `Detector.TupleKernel`, `Moments.AmplificationLocal`, `Moments.AmplificationShortening`, `Moments.ZeroMode`, `Moments.NaturalRowSourceFamily`, `Moments.SourceSecondZeroEnergy`, `Moments.SupportedTailAggregate`, `Moments.SecondSourceRetained`, `PrimeRows.SelectedAgreement`, `PrimeRows.NonprincipalBoundary`, `PrimeRows.XBoundary`, `PrimeRows.ZBoundary`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B021

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B023

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  CubicSieve.PairPrimes
  CubicSieve.PairPoisson
  Detector.CalibrationFourier
  Detector.PhysicalCoefficient
  Detector.PhysicalPoisson
  Detector.FrequencySupport
  Detector.Windows
  Detector.CalibrationRemoval
  Detector.ReciprocityCRT
  Detector.CompletedCoefficient
  PrimeRows.Continuation
  PrimeRows.Agreement
  Detector.HighAbsolute
  Detector.CoefficientDirect
  Detector.SpectralPoisson
  Detector.RadialSpectral
  Detector.Transformed
  Detector.PhysicalRadial
  Detector.NestedMellin
  Detector.RawRadialJoin
  Detector.SixthDecomposition
  PrimeRows.Selected
  PrimeRows.RestoreCorrection
  PrimeRows.CentralSplit
  Detector.CentralRepeatedChoices
  Detector.PhysicalRows
  Detector.GaussianCompensation
  Detector.GaussianPhysicalTail
  Detector.LowRowMellin
  Detector.LowCauchy
  Detector.LowColumnBounds
  Detector.LowActualEnergies
  Detector.GaussianPhysicalMass
  Detector.GaussianSubset
  Detector.GramLatticeWindow
  Detector.GramSourceDivisors
  Detector.LowSlotSplit
  Detector.LowSlotPolynomial
  Detector.LowSlotMarks
  Detector.LowSlotWeights
  Detector.LowTupleGram
  Detector.LowNominalGeometry
  Reflection.OriginalWeights
  Detector.LowGaussianDyad
  Detector.TupleKernel
  Moments.AmplificationLocal
  Moments.AmplificationShortening
  Moments.ZeroMode
  Moments.NaturalRowSourceFamily
  Moments.SourceSecondZeroEnergy
  Moments.SupportedTailAggregate
  Moments.SecondSourceRetained
  PrimeRows.SelectedAgreement
  PrimeRows.NonprincipalBoundary
  PrimeRows.XBoundary
  PrimeRows.ZBoundary
-/

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrime (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → Ideal O :=
  Sum.elim Subtype.val Subtype.val

instance pairPrime_maximal (I J : Ideal O) (P : PrimeIndex I ⊕ PrimeIndex J) :
    (pairPrime I J P).IsMaximal := by
  cases P <;> exact primeIndexMaximal _ _

lemma pairPrime_good (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) : goodLambda ∉ pairPrime I J P := by
  cases P with
  | inl P => exact primeIndex_good I hI.2 P
  | inr P => exact primeIndex_good J hJ.2 P

lemma pairPrime_coprime (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : Pairwise (Function.onFun IsCoprime (pairPrime I J)) := by
  have cross (P : PrimeIndex I) (Q : PrimeIndex J) : IsCoprime P.val Q.val := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI.2) P)
      (primeIndex_le J (primaryGenerator_ne_zero_ideal J hJ.2) Q)
  intro P Q hPQ
  cases P with
  | inl P => cases Q with
    | inl Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime I (fun he => hPQ (congrArg Sum.inl he))
    | inr Q => exact cross P Q
  | inr P => cases Q with
    | inl Q => exact (cross Q P).symm
    | inr Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime J (fun he => hPQ (congrArg Sum.inr he))

lemma pairPrime_product (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    (∏ P, pairPrime I J P) = I * J := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (primeIndex_product I hI) (primeIndex_product J hJ)

def pairExponent (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → ℕ :=
  Sum.elim (fun _ => 4) (fun _ => 2)

lemma pairPrime_modulus (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    Ideal.span {primaryGenerator I * primaryGenerator J} = ∏ P, pairPrime I J P := by
  rw [pairPrime_product I J hI hJ, ← Ideal.span_singleton_mul_span_singleton,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrincipalRow (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : O ⧸ Ideal.span {primaryGenerator I * primaryGenerator J} → ℂ :=
  principalSexticRow (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) (primaryGenerator I * primaryGenerator J)
    (pairPrime_modulus I J hI hJ)

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def calibrationGauss (C : CalibrationData) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero
      (Ideal.Quotient.mk (Ideal.span {C.generator}) h * d)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

def calibratedNumerator (C : CalibrationData) (A m : O) : ℂ :=
  C.residueMonoid m * idealRowHom m (Ideal.span {A})

def calibratedQuotient (C : CalibrationData) (A : O)
    (m : O ⧸ Ideal.span {C.generator*A}) : ℂ :=
  calibratedNumerator C A (representative (C.generator*A) m)

def outerQuotient (s : O) (d : O ⧸ Ideal.span {s}) : ℂ :=
  idealRowHom (representative s d) (Ideal.span {s})

def actualCongruenceCoefficient (C : CalibrationData) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA)
    (calibratedQuotient C A) (outerQuotient s) H

def actualPhysicalFourier (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {(C.generator*A)*s},
    calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m) *
    quotientTrace ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
      (Ideal.Quotient.mk _ H*m)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition ConcreteTraceCRT
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def physicalQuotient (C : CalibrationData) (A s : O) (hs : s≠0)
    (m : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def elementFourier (c : O) (hc : c≠0) (f : O → ℂ) (H : O) : ℂ :=
  ∑' x : Residue c, f (representative c x) * quotientTrace c hc (Ideal.Quotient.mk _ H*x)

def movingQuotient (A s : O) (hs : s≠0) (x : Residue (A*s)) : ℂ :=
  idealRowHom (representative (A*s) x) (Ideal.span {A}) *
    sexticGauss s hs (-representative (A*s) x)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def barePhysicalFourier (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  elementFourier (A*s) (mul_ne_zero hA hs)
    (fun m => idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H

def bareCongruenceCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient A s hA (outerQuotient A) (outerQuotient s) H

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

def reciprocityCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  reciprocitySign A s * bareCongruenceCoefficient A s hA H

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

lemma supported_completed (c n : O) (hc : Supported (Ideal.span {c}))
    (hn : Supported (Ideal.span {n})) : Supported (Ideal.span {c*n^3}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  apply (supported_mul_iff _ _).mpr
  refine ⟨hc,?_⟩
  have hn2 := (supported_mul_iff _ _).mpr ⟨hn,hn⟩
  have hn3 := (supported_mul_iff _ _).mpr ⟨hn2,hn⟩
  simpa only [pow_succ, pow_zero, one_mul] using hn3

def correctedFiniteCoefficient (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : A≠0) (H : O) : ℂ :=
  gaussTwo I hI * star (G A) * reciprocityCoefficient A s hA H

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow) : Finset {P : PrimeIdeal // P.val∉S} :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).subtype (fun P => P.val∉S)

def ramifiedFactor (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (P : {P : PrimeIdeal // P.val∉S}) (x w z : ℂ) : ℂ :=
  if P.val.val∣Ideal.span {u.val} then
    ramifiedCorrection η u P.val (outside_prime_supported S hS.bad P.val P.property) x w z else 1

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev NonzeroFrequency := {u : O // u≠0}

def frequencyWeight (z : ℂ) (u : NonzeroFrequency) : ℂ := (elementNorm u.val:ℂ)^(-z)

def highAbsoluteMajorant (x w z : ℂ) (p : (Id×Id)×(Id×Id)) : ℝ :=
  ‖fullIdealWeight (x-1/2) p.1.1‖ * ‖fullIdealWeight (3*x-2) p.1.2‖ *
  ‖fullIdealWeight (w-1) p.2.1‖ * ‖fullIdealWeight (6*z) p.2.2‖

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow ProbePhase
local notation "O" => ActualEisensteinCubic.O

def calibratedHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  actualCongruenceCoefficient C A s hA H * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * ProbePhase.G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def radialMellinSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def poissonPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y:ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p∈C.excluded, ¬p∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s/Y) * CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q_s*X):ℂ)) *
      verticalIntegral 4 (fun t => (Real.sqrt q_s:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D a has W₀
          (elementNorm C.generator*q_s*X) t p.1 p.2)
    else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def radialMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ) (X Y Z σ : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      W1 (qs/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ))*
      verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
        ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
          (elementNorm C.generator*qs*X) σ t p.1 p.2)
    else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def nestedMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      verticalIntegral υ (fun w=>(Y:ℂ)^(w-1)*(qs:ℂ)^(-w)*mellin W1 w*
        (CanonicalRowCompletion.idealRowHom C.generator s.val /
          (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ)))*
        verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
          ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
            (elementNorm C.generator*qs*X) ξ t p.1 p.2))
    else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion ProbeCompleted ProbeRow CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rawRadialOuterFactor (C : CalibrationData) (K : Ideal O)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w : ℂ) : ℂ :=
  (Y:ℂ)^(w-1)*fullIdealWeight w K*mellin W1 w*
    (idealRowHom C.generator K /
      (C.tau*C.residueMonoid (primaryGenerator K)*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)))*
    (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ActualEisensteinCubic HeckeInverseAmplification CenteredExceptionalCount ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sixthRow_surjective (H : NonzeroFrequency) :
    ∃p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,rowMap p=H.val := by
  let I : Id := Ideal.span {H.val}
  have hI : I≠0 := Ideal.span_singleton_eq_bot.not.mpr H.property
  let J : Id := sixthQuotient I
  have hJ : J≠0 := sixthQuotient_ne_zero I
  let a := idealGenerator J
  have ha : a≠0 := idealGenerator_ne_zero J hJ
  have hspan : Ideal.span {a}=J := span_idealGenerator J
  have hd : a^6∣H.val := by
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
    rw [←Ideal.span_singleton_pow,hspan]
    change J^6∣I
    rw [←sixth_normal_form I hI]
    exact dvd_mul_left _ _
  obtain ⟨u,hu⟩ := hd
  have hu0 : u≠0 := by
    intro hz
    rw [hz,mul_zero] at hu
    exact H.property hu
  have hsu : Ideal.span {u}=sixthRemainder I := by
    have hi : Ideal.span {u}*J^6=I := by
      rw [←hspan,Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton]
      exact congrArg (fun b : O=>Ideal.span {b}) (by simpa only [mul_comm] using hu.symm)
    apply mul_right_cancel₀ (pow_ne_zero 6 hJ)
    exact hi.trans (sixth_normal_form I hI).symm
  have hf : SixthFree (Ideal.span {u}) := by
    rw [hsu]
    intro P
    exact sixthRemainder_valuation_lt I P
  refine ⟨(⟨u,hu0,hf⟩,⟨J,hJ⟩),?_⟩
  change u*a^6=H.val
  simpa only [mul_comm] using hu.symm

def sixthFrequencyEquiv : FreeRow×HeckeInverseAmplification.NonzeroIdeal ≃ NonzeroFrequency :=
  Equiv.ofBijective (fun p=>⟨rowMap p,rowMap_ne_zero p⟩) ⟨
    fun p q h=>rowMap_injective (congrArg Subtype.val h),
    fun H=>by obtain ⟨p,hp⟩ := sixthRow_surjective H;exact ⟨p,Subtype.ext hp⟩⟩

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedCompensatedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z B q : ℂ) : ℂ :=
  ProbeLocal.compensatedReplacement (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z) B q

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def supportedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if hs : Supported P.val then
    if P.val∣Ideal.span {u.val} then ramifiedCorrection η u P hs x w z
    else idealUnramifiedCorrection η u P x w z
  else 1

def excludedCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∈S then 1 else supportedCorrection η u P x w z

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

def centralNormalizedSlot (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
    supportedCorrection η u P x w z

def repeatedRowPrime (u : FreeRow) (P : PrimeIdeal) : Prop :=
  P.val∣Ideal.span {u.val} ∧ 2≤ multiplicity (primaryGenerator P.val) u.val

def centralRegularError (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then 0 else
    centralNormalizedSlot η u P hs x w z+star (idealRowHom u.val P.val)

def centralRepeatedTerm (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then centralNormalizedSlot η u P hs x w z else 0

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedChoices
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => HeckeFamily.O

def activeChoices {k : ℕ} (u : FreeRow) (T : Fin k→Finset PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) : Finset (∀j,T j) :=
  Finset.univ.filter (fun P=>∀j,repeatedRowPrime u (P j).val ∧
    W j (((P j).val.val.absNorm:ℝ)/Y j)≠0)

end SevenEighths.ProbeCentralRepeatedChoices

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRowIndex := {I : Id // Supported I}×O

def physicalRowMonoid (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  rowCoefficient η C.Xi (primaryGenerator r.1.val)
    ((supported_span_primaryGenerator_iff r.1.val).mpr r.1.property) r.2

def physicalRowWeight (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (r : PhysicalRowIndex) : ℂ :=
  if ∀P∈C.excluded,¬P∣r.1.val then
    let a := primaryGenerator r.1.val
    let ha := supported_primaryGenerator_ne_zero r.1.val r.1.property
    let q : ℝ := Ideal.absNorm r.1.val
    (Y:ℂ)⁻¹*W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator r.1.val/
      (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
      C.residueMonoid r.2*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*q*X))
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalElementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

def compensationSubsetCoefficient {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalFamilyIntegral {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
      correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T)*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianPhysicalFamilyMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*∑'r : PhysicalRowIndex,‖physicalRowWeight C W0 W1 (X k) (Y k) r‖

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowAdditiveCoefficient (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    let a := primaryGenerator s.val
    let ha := supported_primaryGenerator_ne_zero s.val s.property
    let q : ℝ := Ideal.absNorm s.val
    (Y:ℂ)⁻¹*W1 (q/Y)*idealRowHom C.generator s.val/(C.tau*C.residueMonoid a)*
      ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)
  else 0

def lowPhysicalScale (C : CalibrationData) (X Y : ℝ) : ℝ := elementNorm C.generator*X*Y

def lowRowMellinIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2*
    ((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
      lowAdditiveCoefficient C W1 Y r.1 r.2 v

lemma calibration_elementNorm_pos (C : CalibrationData) : 0<elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma lowPhysicalScale_pos (C : CalibrationData) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    0<lowPhysicalScale C X Y := mul_pos (mul_pos (calibration_elementNorm_pos C) hX) hY

def lowArithmeticCoefficient (C : CalibrationData) (s : {I : Id // Supported I}) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    idealRowHom C.generator s.val/(C.tau*C.residueMonoid (primaryGenerator s.val))
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorWeight (C : CalibrationData) (Ω : ℝ→ℂ) (X Y : ℝ) (m : O) (v : ℝ) : ℂ :=
  Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
    ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumns (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    Finset {I : Id // Supported I} :=
  ((idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn).toFinset

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorRows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) : Finset O :=
  (elementWindow_finite_support (lowOuterCutoff a b) (lowOuterCutoff_compact a b ha hb) Q hQ).toFinset

def lowGaussMajorant (a b : ℝ) (ha : 0<a) (hb : 0<b) : SchwartzMap ℝ ℂ :=
  (lowOuterCutoff_compact (a/2) (2*b) (by positivity) (by positivity)).toSchwartzMap
    (lowOuterCutoff_smooth (a/2) (2*b))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalScaleMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*lowPhysicalScale C (X k) (Y k)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SelectedSlot {K : ℕ} (J : Finset (Fin K)) := ↥(Finset.univ\J)

def compensationSubsetWeight {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  compensationSubsetCoefficient η p J*(∏i∈J,W i (elementNorm (p i)/P i))

def selectedSlotFactor {K : ℕ} (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (p : Fin K→O) (J : Finset (Fin K)) (t : ℝ) : ℂ :=
  ∏i : SelectedSlot J,W i.val (elementNorm (p i.val)/P i.val)*
    logPhase (-t) (Real.log (elementNorm (p i.val)/P i.val))

def compensationRowTest {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y T t : ℝ) : ℂ :=
  ∑'r : PhysicalRowIndex,
    physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
      correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
        (physicalRowMonoid η C r) (CompletedHeight.normTwistedSource gaussianFixedWindow t) T

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) : Finset O :=
  (elementWindow_finite_support W hW N hN).toFinset

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceDivisors (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) : Finset SupportedIdeal :=
  (divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val).preimage
    Subtype.val Subtype.val_injective.injOn

def sourceDivisorUnion (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) : Finset SupportedIdeal :=
  F.biUnion (sourceDivisors W hW Y hY)

def sourceMobiusWeight (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) : ℂ :=
  if D∈sourceDivisors W hW Y hY C then (moebius D.val:ℂ) else 0

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

abbrev LowUnselectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : J,↥(slots i.val)
abbrev LowSelectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : SelectedSlot J,↥(slots i.val)

def lowSlotTupleEquiv {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :
    (∀i,↥(slots i)) ≃ LowUnselectedTuple slots J×LowSelectedTuple slots J where
  toFun p := (fun i=>p i.val,fun i=>p i.val)
  invFun p i := if hi : i∈J then p.1 ⟨i,hi⟩ else p.2 ⟨i,by simp [hi]⟩
  left_inv p := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext i
      have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
      simp only [dif_neg hi]

def lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) : Fin K→O :=
  fun i=>((lowSlotTupleEquiv slots J).symm (a,b) i).val

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedWeight {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (a : LowUnselectedTuple slots J) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ)):ℝ):ℂ)*
    ∏i : J,W i.val (elementNorm (a i).val/P i.val)

def lowSelectedWeight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) : ℂ :=
  star (HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val))*
    ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
      FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val))

def lowSelectedIdeal {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) : Id := Ideal.span {∏i : SelectedSlot J,(b i).val}

lemma lowUnselectedProduct_norm_pos {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    0<elementNorm (∏i : J,(a i).val) := by
  apply physicalElementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCanonicalSelectedPrime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) : PrimeIdeal :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).val

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

def lowSingleSlotWeight (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (HeckeFamily.elementCoeff η a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramFactor (C : CalibrationData) (X Y δ : ℝ) : ℝ :=
  Real.sqrt ((lowPhysicalScale C X Y/Y)*(1+(Y^2/lowPhysicalScale C X Y)^(1/6:ℝ)+
    (Y^2/lowPhysicalScale C X Y)^2/Y)*Y^δ)

def lowInverseMass (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) : ℝ :=
  ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
    (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i∈J,ell i

def lowSelectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i : SelectedSlot J,ell i.val

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def frozenInactiveWeight (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) : ℂ :=
  ∏ b∈(Finset.univ:Finset (FreeReflection.pool J Q Q₀))\A,
    if completedLocalExponent J F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCommonDyad {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) : ℂ :=
  ∫t : ℝ,(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
    compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
      selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tuplePhysicalScalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLocal
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def centralLocal (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  sexticGauss (p^(n+1)) (pow_ne_zero _ hp) h / (Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1)

end SevenEighths.CenteredMomentAmplificationLocal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationShortening
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentAmplificationLocal
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def residualCharacter (p : O) (k : ℕ) (u : O) : ℂ :=
  sexticReciprocityPhase p u ^ k * idealRowHom u (Ideal.span {p}) ^ (2*k)

def primeRoot (p : O) (k : ℕ) : ℂ :=
  (Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)

def errorScalar (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  centralLocal p hp n h - centralLocal p hp n (p^6*h)

end SevenEighths.CenteredMomentAmplificationShortening

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentZeroMode
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcreteTraceCRT CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O

@[simp] theorem pairResidue_mul (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x y : Residue (a * b)) :
    pairResidue a b ha hb (x * y) =
      pairResidue a b ha hb x * pairResidue a b ha hb y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, pairResidue_mk, pairResidue_mk, pairResidue_mk,
    idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

@[simp] theorem pairFourier_zero (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    pairFourier a b ha hb 0 = ∑' x : Residue (a * b), pairResidue a b ha hb x := by
  simp [pairFourier, quotientTrace]

def idealColumn (S : Finset (Ideal O)) (I : S) : O :=
  ConcretePrimeRowBridge.idealGenerator I.val

@[simp] theorem idealColumn_span (S : Finset (Ideal O)) (I : S) :
    Ideal.span {idealColumn S I} = I.val :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem idealColumn_supported (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {idealColumn S I}) := by
  rw [idealColumn_span]
  exact hS I.val I.property

def idealZeroEnergy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (K : ℝ) : ℂ :=
  ∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
    (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (idealColumn S I) (idealColumn S J)
        (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0)

end SevenEighths.CenteredMomentZeroMode

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

structure NaturalRow (η : Character) (z : O) where
  character : Character
  modulus_bound : character.modulus.absNorm≤ rowConductorBound η fixedBadMask 1 z
  element : ∀n,elementCoeff character n=rowTwist (elementHom η) fixedBadMask 1 z n

def naturalRow (η : Character) (z : O) (hz : z≠0) : NaturalRow η z := by
  let e:=exists_row_character_with_conductor η fixedBadMask 1 z
    fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨Classical.choose e,(Classical.choose_spec e).1,(Classical.choose_spec e).2⟩

def fixedConductorFactor : ℕ := (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSecondZeroEnergy
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def sourceSecondZero (S : Finset (Ideal O)) (β : Ideal O→ℂ) (η : Character) (t : ℝ) : ℂ :=
  secondZeroEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I => β I*heightCoeff η t I)

end SevenEighths.CenteredMomentSourceSecondZeroEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedTailAggregate
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondTail
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

def secondDiscardedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

end SevenEighths.CenteredMomentSupportedTailAggregate

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained
open CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then secondRetainedPair I J hI hJ W K Tsec Z ξ else 0 else 0

end SevenEighths.CenteredMomentSecondSourceRetained

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def finiteLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  ProbeLocal.continuedCorrection (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowKernelScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (x z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def xRowScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y : ℝ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Y:ℂ)^(w-1)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def zRowScalar {K : ℕ} (P : Fin K→PrimeIdeal) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


