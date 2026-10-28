-- Prove2me | Definitions.Def_OAIW2PG000
-- name    : OAIW2PG000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T04:52:02.091853+00:00
-- url     : https://prove2.me/theorems/c7f1a1a5-343c-4e33-bb82-1e6b9becf315
-- title:
--   Definitions bundle OAIW2PG000 of the split of OpenAI, Positive lower density of large prime gaps
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem344.large_gaps_and_ratio_density`, carved from OpenAI's openai/math development (OpenAI, *Positive lower density of large prime gaps*, OpenAI Math Release, September 25, 2026, result family 26, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 337 declarations of OpenAI's Lean: 252 definitions, 4 instances and 81 theorems. The definitions and types are `OAI.LargePrimeGaps.AdmissibleFamily`, `OAI.LargePrimeGaps.AllowedDivisorTuple`, `OAI.LargePrimeGaps.BombieriVinogradov`, `OAI.LargePrimeGaps.EulerChoices`, `OAI.LargePrimeGaps.HasBudget`, `OAI.LargePrimeGaps.PatternMaps`, `OAI.LargePrimeGaps.PrimePowerEq`, `OAI.LargePrimeGaps.SiegelWalfisz`, `OAI.LargePrimeGaps.SymmetricFunction`, `OAI.LargePrimeGaps.activeLevels`, `OAI.LargePrimeGaps.alpha`, `OAI.LargePrimeGaps.analyticDensity`, `OAI.LargePrimeGaps.appendMeasurableEquiv`, `OAI.LargePrimeGaps.arithmeticCharacterSum`, `OAI.LargePrimeGaps.arithmeticCutoff`, `OAI.LargePrimeGaps.arithmeticL1`, `OAI.LargePrimeGaps.average`, `OAI.LargePrimeGaps.biquadraticCoefficients`, `OAI.LargePrimeGaps.blockLength`, `OAI.LargePrimeGaps.boxDiameterBound`, `OAI.LargePrimeGaps.boxTruncationError`, `OAI.LargePrimeGaps.boxTuple`, `OAI.LargePrimeGaps.bvCentered`, `OAI.LargePrimeGaps.bvExp`, `OAI.LargePrimeGaps.bvExponentialVector`, `OAI.LargePrimeGaps.cancellationBracket`, `OAI.LargePrimeGaps.cancellationFamily`, `OAI.LargePrimeGaps.characterMain`, `OAI.LargePrimeGaps.characterMean`, `OAI.LargePrimeGaps.characterMeanError`, `OAI.LargePrimeGaps.characterRegular`, `OAI.LargePrimeGaps.characterUnitVector`, `OAI.LargePrimeGaps.choiceDivisors`, `OAI.LargePrimeGaps.choiceSubset`, `OAI.LargePrimeGaps.choiceTuple`, `OAI.LargePrimeGaps.complexCumulativeExtension`, `OAI.LargePrimeGaps.conductorHarmonicBound`, `OAI.LargePrimeGaps.contourKernel`, `OAI.LargePrimeGaps.coordinateDirectionList`, `OAI.LargePrimeGaps.coordinateSum` and 212 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PrimeGaps_AdditiveSieve`, `PrimeGaps_BoxMeans`, `PrimeGaps_CharacterErrors`, `PrimeGaps_ConductorBounds`, `PrimeGaps_ContourIntegrals`, `PrimeGaps_ContourSums`, `PrimeGaps_CumulativeProfiles`, `PrimeGaps_Density`, `PrimeGaps_Detectors`, `PrimeGaps_DirichletGrowth`, `PrimeGaps_DivisorBounds`, `PrimeGaps_DivisorSums`, `PrimeGaps_DyadicMeans`, `PrimeGaps_EqualityPatterns`, `PrimeGaps_EulerChoices`, `PrimeGaps_EulerFactors`, `PrimeGaps_EulerProducts`, `PrimeGaps_FourierDerivatives`, `PrimeGaps_FourierNormalization`, `PrimeGaps_Indices`, `PrimeGaps_LaplaceTransform`, `PrimeGaps_LevelMoments`, `PrimeGaps_LogParameters`, `PrimeGaps_MangoldtBounds`, `PrimeGaps_MarkedMoments`, `PrimeGaps_MellinSmoothing`, `PrimeGaps_MultiplicativeSieve`, `PrimeGaps_OrthantIntegrals`, `PrimeGaps_PairedDetectors`, `PrimeGaps_PatternMoments`, `PrimeGaps_ProfileSymmetry`, `PrimeGaps_ProfileVariance`, `PrimeGaps_Profiles`, `PrimeGaps_RestrictedWeights`, `PrimeGaps_RieszBounds`, `PrimeGaps_RieszDecay`, `PrimeGaps_SiegelBounds`, `PrimeGaps_SingularSeries`, `PrimeGaps_SingularTails`, `PrimeGaps_TaylorBounds`, `PrimeGaps_TensorProfiles`, `PrimeGaps_VaughanBounds`, `PrimeGaps_VaughanIdentity`, `PrimeGaps_WeightMoments`, `PrimeGaps_ZeroFreeBounds`, `PrimeGaps_ZetaKernel`.
--
--   **Imports.** It imports the published bundle `Def_PrimeGaps`.
--
--   **Imported by** (directly, in this split): the statements `OAI.LargePrimeGaps.bombieriVinogradov`, `OAI.LargePrimeGaps.extra_cumulative_pair_limit`, `OAI.LargePrimeGaps.marked_average_uniform_asymptotic`, `OAI.LargePrimeGaps.primeRiesz_mellinInv`, `OAI.LargePrimeGaps.primeWeighted_error_bound`, `OAI.LargePrimeGaps.unorderedWeight_detector_bound`, `OAI.LargePrimeGaps.unorderedWeight_external_marked_limit`, `OAI.LargePrimeGaps.unorderedWeight_fourth_bound` and `OAI.LargePrimeGaps.unorderedWeight_internal_marked_limit`; the proofs of `OAI.LargePrimeGaps.bombieriVinogradov`, `OAI.LargePrimeGaps.extra_cumulative_pair_limit`, `OAI.LargePrimeGaps.marked_average_uniform_asymptotic`, `OAI.LargePrimeGaps.primeRiesz_mellinInv`, `OAI.LargePrimeGaps.primeWeighted_error_bound`, `OAI.LargePrimeGaps.unorderedWeight_detector_bound`, `OAI.LargePrimeGaps.unorderedWeight_external_marked_limit`, `OAI.LargePrimeGaps.unorderedWeight_fourth_bound`, `OAI.LargePrimeGaps.unorderedWeight_internal_marked_limit` and `OAI.Problem344.large_gaps_and_ratio_density`.
-- source:
--   OpenAI, Positive lower density of large prime gaps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 26; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Mathlib
import Definitions.Def_PrimeGaps

section
-- module Solutions.OAIW2_P344.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

def primeIndex (p : ℕ) : ℕ := Nat.primeCounting' p + 1

noncomputable def successor (p : ℕ) : ℕ := prime (primeIndex p + 1)

noncomputable def goodStarts (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter fun m =>
    (∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h) ∧
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q

noncomputable def gapPrimes (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X + h)).filter fun p =>
    Nat.Prime p ∧ p + h < successor p

noncomputable def theta (n : ℕ) : ℝ := if Nat.Prime n then Real.log n else 0

noncomputable def average (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc X (2 * X), f m) / (X : ℝ)

noncomputable def detector (X : ℕ) (B : Finset ℕ) (m : ℕ) : ℝ :=
  (∑ b ∈ B, theta (m + b)) / Real.log (X : ℝ)

noncomputable def blockLength (lam : ℝ) (X : ℕ) : ℕ :=
  ⌊lam * Real.log (X : ℝ)⌋₊

open Filter

noncomputable def indexScale (N : ℕ) : ℕ := prime N / 3

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DivisorSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

noncomputable def logCoordinates {ι : Type*} (X : ℕ) (d : ι → ℕ) : ι → ℝ :=
  fun i => Real.log (d i : ℝ) / Real.log (X : ℝ)

noncomputable def divisorCoefficient {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) : ℝ :=
  (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) * F (logCoordinates X d)

noncomputable def divisorSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (m : ℕ) (b : ι → ℕ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => (m + b i).divisors), divisorCoefficient X F d

def HasBudget {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) (rho : ℝ) : Prop :=
  ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → rho < ∑ i, v i → F v = 0

def residueStarts (X q c : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun m => m % q = c

def tupleModulus {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ := Finset.univ.lcm d

def tupleCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) : Prop :=
  ∃ c < tupleModulus d, ∀ i, d i ∣ c + b i

def localCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) : Prop :=
  ∀ p, Nat.Prime p → p ∣ tupleModulus d →
    ∀ i j, p ∣ d i → p ∣ d j → Nat.ModEq p (b i) (b j)

noncomputable def tupleStarts {ι : Type*} [Fintype ι] (X : ℕ) (d b : ι → ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun m => ∀ i, d i ∣ m + b i

noncomputable def tupleDensity {ι : Type*} [Fintype ι] (d b : ι → ℕ) : ℝ := by
  classical
  exact if tupleCompatible d b then (tupleModulus d : ℝ)⁻¹ else 0

def positiveProductTuples (n Y : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)).filter fun d => ∏ i, d i ≤ Y

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DivisorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

noncomputable def unmarkedDensitySum {n : ℕ} (X : ℕ) (F : (Fin n → ℝ) → ℝ)
    (rho : ℝ) (b : Fin n → ℕ) : ℝ :=
  ∑ d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
    divisorCoefficient X F d * tupleDensity d b

def squarefreeModulusFiber (n Y q : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)).filter
    fun d => (∀ i, Squarefree (d i)) ∧ tupleModulus d = q

def markedTupleCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : Prop :=
  ∃ c < tupleModulus d, (∀ i, d i ∣ c + b i) ∧ Nat.Coprime (c + a) (tupleModulus d)

noncomputable def markedTupleDensity {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : ℝ := by
  classical
  exact if markedTupleCompatible d b a then ((tupleModulus d).totient : ℝ)⁻¹ else 0

noncomputable def markedError (X H q : ℕ) : NNReal :=
  ((Finset.range (H + 1)) ×ˢ (Finset.range q)).sup fun ac =>
    if Nat.Coprime (ac.2 + ac.1) q then
      NNReal.mk (|(∑ m ∈ residueStarts X q ac.2, theta (m + ac.1)) - (X : ℝ) / q.totient|)
        (abs_nonneg _) else 0

def markedLocalCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : Prop :=
  localCompatible d b ∧ ∀ p, Nat.Prime p → p ∣ tupleModulus d →
    ∀ i, p ∣ d i → ¬ Nat.ModEq p (b i) a

def squarefreeProductTuples (n Y : ℕ) : Finset (Fin n → ℕ) :=
  (positiveProductTuples n Y).filter fun d => ∀ i, Squarefree (d i)

noncomputable def markedDensitySum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ) (b : Fin n → ℕ) (a : ℕ) : ℝ :=
  ∑ d ∈ squarefreeProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
    divisorCoefficient X F d * markedTupleDensity d b a

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def reciprocalBump (R : ℝ) (hR : 2 ≤ R) :
    ContDiffBump ((R + 1) / 2) where
  rIn := (R - 1) / 2
  rOut := R / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

noncomputable def reciprocalProfile (R : ℝ) (hR : 2 ≤ R) (u : ℝ) : ℝ :=
  reciprocalBump R hR u / u

noncomputable def scaledProfileDensity (g : ℝ → ℝ) (k : ℝ) (u : ℝ) : ℝ :=
  k * g (k * u) ^ 2

noncomputable def productProfile (g : ℝ → ℝ) (k : ℝ) (j : ℕ) (t : Fin j → ℝ) : ℝ :=
  ∏ i, Real.sqrt k * g (k * t i)

noncomputable def productDensity (p : ℝ → ℝ) (j : ℕ) (t : Fin j → ℝ) : ℝ :=
  ∏ i, p (t i)

def coordinateSum {j : ℕ} (t : Fin j → ℝ) : ℝ := ∑ i, t i

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ProfileVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def simplexCutoff (beta gamma : ℝ) (s : ℝ) : ℝ :=
  1 - Real.smoothTransition ((s-beta)/(gamma-beta))

noncomputable def cutoffDeletion (g chi : ℝ → ℝ) (k s : ℝ) : ℝ :=
  ∫ u, g u * chi (s+u/k)

noncomputable def cancellationBracket (g chi : ℝ → ℝ) (lambda k : ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  chi s - (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s

noncomputable def alpha (lambda : ℝ) (j : ℕ) : ℝ := lambda^j / j.factorial

noncomputable def levelFunction (g chi : ℝ → ℝ) (lambda k r : ℝ)
    (j : ℕ) (t : Fin j → ℝ) : ℝ :=
  ((-1:ℝ)^j / (Real.sqrt r * Real.sqrt (alpha lambda j))) *
    productProfile g k j t * chi (coordinateSum t)

noncomputable def deleteCoordinate {j : ℕ} (f : (Fin (j+1) → ℝ) → ℝ)
    (t : Fin j → ℝ) : ℝ := ∫ u : ℝ, f (Fin.snoc t u)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LevelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def l2Mass {j : ℕ} (f : (Fin j → ℝ) → ℝ) : ℝ := ∫ t, f t^2

def activeLevels (k r : ℕ) : Finset ℕ := Finset.Icc (k-r+1) k

noncomputable def cancellationFamily (g chi : ℝ → ℝ) (lambda : ℝ) (k r j : ℕ) :
    (Fin j → ℝ) → ℝ :=
  if j ∈ activeLevels k r then levelFunction g chi lambda k r j else 0

noncomputable def familyW (lambda : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), alpha lambda j * l2Mass (f j)

noncomputable def familyV (lambda : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : ℝ :=
  lambda * ∑ j ∈ Finset.range (k+1), alpha lambda j *
    l2Mass (fun t => f j t + deleteCoordinate (f (j+1)) t)

@[simp] theorem l2Mass_zero (j : ℕ) : l2Mass (0 : (Fin j → ℝ) → ℝ) = 0 := by
  simp [l2Mass]

@[simp] theorem deleteCoordinate_zero (j : ℕ) :
    deleteCoordinate (0 : (Fin (j+1) → ℝ) → ℝ) = 0 := by
  funext t
  simp [deleteCoordinate]

def SymmetricFunction {j : ℕ} (f : (Fin j → ℝ) → ℝ) : Prop :=
  ∀ (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f (t ∘ e) = f t

def positiveSimplex (j : ℕ) (tau : ℝ) : Set (Fin j → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ coordinateSum t < tau}

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_OrthantIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

def squareDimension (m : ℕ) : ℕ := (m+1)^2

def AdmissibleFamily (tau : ℝ) (k : ℕ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : Prop :=
  0 < k ∧
  (∀ j, j ≤ k → ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j) ⊆ positiveSimplex j tau ∧ SymmetricFunction (f j)) ∧
  (∀ j, k < j → f j = 0)

def divisorMultiplicity (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n

noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MangoldtBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def endpointError (x : ℝ) (q : ℕ) : NNReal :=
  (Finset.range q).sup fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x/q.totient|)
      (abs_nonneg _) else 0

def BombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊,
        (endpointError x q : ℝ)) ≤ M*x*(Real.log x)^(-A)

noncomputable def powerModulus (rho : ℝ) (X : ℕ) : ℕ := ⌊(X:ℝ)^rho⌋₊

noncomputable def weightedErrorSum (K X H Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (K:ℝ)^q.primeFactors.card *
    (markedError X H q : ℝ) else 0

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SingularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

def residueCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image fun a => a % (p:ℤ)).card

noncomputable def singularLocal (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (residueCount H p : ℝ)/(p:ℝ)) / (1 - 1/(p:ℝ))^H.card

noncomputable def singularSeries (H : Finset ℤ) : ℝ :=
  ∏' p : Nat.Primes, singularLocal H p

noncomputable def singularTruncation (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, singularLocal H p

def differenceProduct (H : Finset ℤ) : ℕ :=
  ∏ a ∈ H, ∏ b ∈ H.erase a, (a-b).natAbs

noncomputable def singularTailBound (H : Finset ℤ) (y : ℕ) : ℝ :=
  2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(y:ℝ) +
    4*(H.card:ℝ)*Real.log (differenceProduct H)/((y:ℝ)*Real.log y)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SingularTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def singularTailFactor (H : Finset ℤ) (y p : ℕ) : ℝ :=
  if p.Prime ∧ y<p then singularLocal H p else 1

noncomputable def singularTail (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏' p : ℕ, singularTailFactor H y p

noncomputable def siftedCount {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) : ℝ :=
  ∑ x : ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0

noncomputable def normalizedSiftedCount {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) : ℝ :=
  ((q:ℝ)/q.totient)^s * siftedCount a / q

noncomputable def siftedTuple {s : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  if h : q=0 then 0 else
    let _ : NeZero q := ⟨h⟩
    normalizedSiftedCount (fun i => (a i : ZMod q))

def rangeResidue (h q c : ℕ) : Finset ℕ := (Finset.range h).filter fun n => n%q=c

noncomputable def cyclicFiber (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) : Finset (Fin h) :=
  Finset.univ.filter fun n => (a:ZMod q)+(n:ℕ)=r

noncomputable def residueTuple {s h q : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ZMod q :=
  fun i => (a i:ZMod q)+(n i:ℕ)

def boxTuple {s h : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ℤ :=
  fun i => a i + (n i:ℕ)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_BoxMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def distinctBox {s h : ℕ} (a : Fin s → ℤ) : Finset (Fin s → Fin h) :=
  Finset.univ.filter fun n => Function.Injective (boxTuple a n)

noncomputable def truncatedBoxMean {s h : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  (∑ n : Fin s → Fin h, siftedTuple (boxTuple a n) q)/(h:ℝ)^s

noncomputable def distinctTruncatedBoxMean {s h : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  (∑ n ∈ distinctBox (h:=h) a, siftedTuple (boxTuple a n) q)/(h:ℝ)^s

noncomputable def singularBoxMean {s h : ℕ} (a : Fin s → ℤ) : ℝ :=
  (∑ n ∈ distinctBox (h:=h) a, singularSeries (Finset.univ.image (boxTuple a n)))/(h:ℝ)^s

noncomputable def boxTruncationError (s h q : ℕ) : ℝ :=
  |(1-(q:ℝ)/h)^s-1| + |(1+(q:ℝ)/h)^s-1| + (s:ℝ)^2*(q:ℝ)^s/h

noncomputable def uniformSingularTailBound (s M y : ℕ) : ℝ :=
  2*((s:ℝ)^2*(2:ℝ)^s)/(y:ℝ) +
    4*(s:ℝ)*((s*(s-1):ℕ):ℝ)*Real.log M/((y:ℝ)*Real.log y)

def boxDiameterBound {s h : ℕ} (a : Fin s → ℤ) (M : ℕ) : Prop :=
  ∀ (n : Fin s → Fin h) i j, (boxTuple a n i-boxTuple a n j).natAbs ≤ M

noncomputable def singularCutoffScale (s : ℕ) : ℝ := 2*((s:ℝ)+1)*Real.log 4

noncomputable def singularCutoff (s h : ℕ) : ℕ := ⌊Real.log h/singularCutoffScale s⌋₊

noncomputable def singularBoxError (s K h : ℕ) : ℝ :=
  boxTruncationError s h (primorial (singularCutoff s h)) +
    2*uniformSingularTailBound s (K*h) (singularCutoff s h)*
      (1+(primorial (singularCutoff s h):ℝ)/h)^s

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ZetaKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

noncomputable def nonemptySubsets {ι : Type*} (s : Finset ι) : Finset (Finset ι) := by
  classical
  exact s.powerset.erase ∅

noncomputable def fiberKernel {ι : Type*} (s : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ S∈nonemptySubsets s, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))

noncomputable def frequencyW (u : ℝ) : ℂ := 1+Complex.I*(u:ℂ)

@[simp] theorem frequencyW_re (u : ℝ) : (frequencyW u).re=1 := by simp [frequencyW]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

noncomputable def genericLocalQuotient {ι : Type*} (s : Finset ι) (σ : ι → ℤ)
    (a : ι → ℂ) (ρ : ℝ) : ℂ :=
  (1+(ρ:ℂ)*(∑ i∈s, (σ i:ℂ)*a i))*(∏ i∈s, (1-a i)^(σ i))

noncomputable def primeMonomial {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) : ℂ :=
  Complex.exp (-(Real.log p : ℂ)*(∑ i∈S, z i))

@[simp] theorem primeMonomial_zero {ι : Type*} (p : ℕ) (S : Finset ι) :
    primeMonomial p (fun _ => (0:ℂ)) S = 1 := by simp [primeMonomial]

noncomputable def eulerP {ι : Type*} (p δ : ℕ) (A : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  1+((p:ℂ)-δ)⁻¹*(∑ S∈A, (-1:ℂ)^S.card*primeMonomial p z S)

noncomputable def eulerH {ι : Type*} (p δ : ℕ) (A B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  eulerP p δ A z * ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

noncomputable def fiberSubsetFamily {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) : Finset (Finset ι) := by
  classical
  exact R.biUnion fun r => nonemptySubsets (Finset.univ.filter fun i => b i=r)

noncomputable def shiftFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) : Finset (Finset ι) :=
  fiberSubsetFamily b (Finset.univ.image b)

noncomputable def residueFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) : Finset (Finset ι) :=
  fiberSubsetFamily (fun i => b i%(p:ℤ)) (Finset.univ.image fun i => b i%(p:ℤ))

noncomputable def markedResidueFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) : Finset (Finset ι) :=
  fiberSubsetFamily (fun i => b i%(p:ℤ)) ((Finset.univ.image fun i => b i%(p:ℤ)).erase (a%(p:ℤ)))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

section FourierNormalization

open scoped FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def frequencyDilation : V ≃L[ℝ] V :=
  Units.mk0 ((2*Real.pi)⁻¹) (inv_ne_zero (by positivity)) • ContinuousLinearEquiv.refl ℝ V

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem frequencyDilation_apply (u : V) :
    frequencyDilation u = (2*Real.pi)⁻¹ • u := rfl

noncomputable def radianFourier (G : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  (((2*Real.pi)^Module.finrank ℝ V)⁻¹ : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequencyDilation (𝓕⁻ G)

noncomputable def laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  (show HasCompactSupport (fun v => Complex.exp (ℓ v : ℂ)*F v) from hF.mul_left).toSchwartzMap
    (((Complex.ofRealCLM.contDiff.comp ℓ.contDiff).cexp).mul hFs)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceSchwartz_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    laplaceSchwartz ℓ F hF hFs v = Complex.exp (ℓ v : ℂ)*F v := rfl

noncomputable def sourceFourier (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  radianFourier (laplaceSchwartz ℓ F hF hFs)

end FourierNormalization

def primePrefix (y : ℕ) : Finset Nat.Primes := (Nat.primesLE y).subtype Nat.Prime

@[simp] theorem mem_primePrefix (y : ℕ) (p : Nat.Primes) :
    p∈primePrefix y ↔ (p:ℕ)≤y := by
  exact (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE y) (a := p)).trans
    (by rw [Nat.mem_primesLE]; exact and_iff_left p.property)

noncomputable def eulerGlobal {ι : Type*} (δ : ℕ) (A : ℕ → Finset (Finset ι))
    (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏' p : Nat.Primes, eulerH p δ (A p) B z

noncomputable def genericEulerConstant (m : ℕ) : ℝ :=
  (1+m)*(4*(m:ℝ)^2*2^m+2*m)+2*m+2*(m:ℝ)^2

noncomputable def primeReciprocalPrefix (y : ℕ) : ℝ :=
  ∑ p∈primePrefix y, (p:ℝ)⁻¹

noncomputable def eulerZetaProduct {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, riemannZeta (1+∑ i∈S, z i)^((-1:ℤ)^S.card)

abbrev EulerChoices {κ : Type*} (A : κ → Type*) :=
  Σ P : Finset κ, (p : P) → A p

noncomputable def eulerChoiceTerm {κ : Type*} {A : κ → Type*}
    (w : (p : κ) → A p → ℂ) (c : EulerChoices A) : ℂ :=
  ∏ p : c.1, w p (c.2 p)

noncomputable def eulerChoiceNorm {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (p : κ) : ℝ := ∑ a, ‖w p a‖

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

noncomputable def primeChoiceWeight {ι : Type*} (δ : ℕ) (z : ι → ℂ)
    (p : Nat.Primes) (S : Finset ι) : ℂ :=
  ((p:ℂ)-δ)⁻¹*((-1:ℂ)^S.card*primeMonomial p z S)

noncomputable def primeAllowedWeight {ι : Type*} (δ : ℕ) (A : ℕ → Finset (Finset ι))
    (z : ι → ℂ) (p : Nat.Primes) (S : {S // S∈A p}) : ℂ := primeChoiceWeight δ z p S

noncomputable def choiceSubset {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) : Finset ι := by
  classical
  exact if hp : p∈c.1 then (c.2 ⟨p,hp⟩).val else ∅

@[simp] theorem choiceSubset_of_mem {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∈c.1) :
    choiceSubset c p = (c.2 ⟨p,hp⟩).val := by simp [choiceSubset, hp]

@[simp] theorem choiceSubset_of_not_mem {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∉c.1) :
    choiceSubset c p = ∅ := by simp [choiceSubset, hp]

noncomputable def choiceDivisors {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) : ℕ := by
  classical
  exact ∏ p∈c.1.filter (fun p => i∈choiceSubset c p), (p:ℕ)

theorem choiceDivisors_squarefree {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    Squarefree (choiceDivisors c i) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p _ q _ hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes p.property q.property).mpr
      (fun he => hpq (Subtype.ext he)))
  · intro p _
    exact p.property.prime.squarefree

theorem prime_dvd_choiceDivisors {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) (i : ι) :
    (p:ℕ) ∣ choiceDivisors c i ↔ i∈choiceSubset c p := by
  classical
  rw [choiceDivisors, p.property.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q,hq,hpq⟩
    have he : p=q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hpq)
    simpa [he] using (Finset.mem_filter.mp hq).2
  · intro hi
    have hp : p∈c.1 := by
      by_contra hn
      simp [choiceSubset_of_not_mem c hn] at hi
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,hi⟩,dvd_refl _⟩

noncomputable def tuplePrimeSupport {ι : Type*} [Fintype ι] (d : ι → ℕ) : Finset Nat.Primes := by
  classical
  exact (Finset.univ.biUnion fun i => (d i).primeFactors).subtype Nat.Prime

theorem mem_tuplePrimeSupport {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i≠0) (p : Nat.Primes) : p∈tuplePrimeSupport d ↔ ∃ i, (p:ℕ)∣d i := by
  classical
  refine (Finset.mem_subtype (a := (⟨p.val,p.property⟩ : {n : ℕ // Nat.Prime n}))).trans ?_
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Nat.mem_primeFactors,
    p.property, true_and]
  constructor
  · rintro ⟨i,hi,_⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,hi,hd i⟩

noncomputable def tuplePrimeSubset {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (p:ℕ)∣d i

@[simp] theorem mem_tuplePrimeSubset {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) (i : ι) : i∈tuplePrimeSubset d p ↔ (p:ℕ)∣d i := by
  classical
  simp [tuplePrimeSubset]

theorem tuplePrimeSubset_nonempty_iff {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : ∀ i, d i≠0) (p : Nat.Primes) :
    (tuplePrimeSubset d p).Nonempty ↔ p∈tuplePrimeSupport d := by
  rw [mem_tuplePrimeSupport hd]
  simp [Finset.Nonempty]

theorem choiceSubset_mem_of_nonempty {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes)
    (h : (choiceSubset c p).Nonempty) : choiceSubset c p∈A p := by
  classical
  by_cases hp : p∈c.1
  · rw [choiceSubset_of_mem c hp]
    exact (c.2 ⟨p,hp⟩).property
  · simp [choiceSubset_of_not_mem c hp] at h

theorem choice_primeSubset {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) :
    tuplePrimeSubset (choiceDivisors c) p = choiceSubset c p := by
  ext i
  simp [prime_dvd_choiceDivisors]

theorem eulerChoices_ext {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    {c e : EulerChoices (fun p : Nat.Primes => {S // S∈A p})}
    (h : ∀ p, choiceSubset c p = choiceSubset e p) : c=e := by
  classical
  have hc (p : Nat.Primes) : p∈c.1 ↔ (choiceSubset c p).Nonempty := by
    by_cases hp : p∈c.1
    · simp only [hp, true_iff, choiceSubset_of_mem c hp]
      exact hA p _ (c.2 ⟨p,hp⟩).property
    · simp [hp]
  have he (p : Nat.Primes) : p∈e.1 ↔ (choiceSubset e p).Nonempty := by
    by_cases hp : p∈e.1
    · simp only [hp, true_iff, choiceSubset_of_mem e hp]
      exact hA p _ (e.2 ⟨p,hp⟩).property
    · simp [hp]
  have hce : c.1=e.1 := Finset.ext fun p => by rw [hc,he,h]
  rcases c with ⟨P,c⟩
  rcases e with ⟨Q,e⟩
  dsimp only at hce
  subst Q
  congr 1
  funext p
  apply Subtype.ext
  simpa only [choiceSubset_of_mem ⟨P,c⟩ p.property,
    choiceSubset_of_mem ⟨P,e⟩ p.property] using h p

def AllowedDivisorTuple {ι : Type*} [Fintype ι] (A : ℕ → Finset (Finset ι)) :=
  {d : ι → ℕ // (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty → tuplePrimeSubset d p∈A p}

noncomputable def tupleChoices {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : AllowedDivisorTuple A) : EulerChoices (fun p : Nat.Primes => {S // S∈A p}) :=
  ⟨tuplePrimeSupport d.val, fun p => ⟨tuplePrimeSubset d.val p,
    d.property.2 p ((tuplePrimeSubset_nonempty_iff d.val
      (fun i => (d.property.1 i).ne_zero) p).mpr p.property)⟩⟩

theorem tupleChoices_subset {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : AllowedDivisorTuple A) (p : Nat.Primes) :
    choiceSubset (tupleChoices d) p = tuplePrimeSubset d.val p := by
  classical
  by_cases hp : p∈tuplePrimeSupport d.val
  · exact choiceSubset_of_mem (tupleChoices d) hp
  · rw [choiceSubset_of_not_mem (tupleChoices d) hp]
    apply Eq.symm
    exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hp
      ((tuplePrimeSubset_nonempty_iff d.val (fun i => (d.property.1 i).ne_zero) p).mp h))

theorem choiceDivisors_tupleChoices {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : AllowedDivisorTuple A) : choiceDivisors (tupleChoices d) = d.val := by
  funext i
  apply (Nat.Squarefree.ext_iff (choiceDivisors_squarefree _ i) (d.property.1 i)).mpr
  intro p hp
  let p' : Nat.Primes := ⟨p,hp⟩
  exact (prime_dvd_choiceDivisors (tupleChoices d) p' i).trans
    ((Iff.of_eq (congrArg (fun S : Finset ι => i∈S) (tupleChoices_subset d p'))).trans
      (mem_tuplePrimeSubset d.val p' i))

noncomputable def choiceTuple {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) : AllowedDivisorTuple A :=
  ⟨choiceDivisors c, choiceDivisors_squarefree c, fun p h => by
    rw [choice_primeSubset] at h ⊢
    exact choiceSubset_mem_of_nonempty c p h⟩

noncomputable def primeChoicesEquivTuple {ι : Type*} [Fintype ι]
    (A : ℕ → Finset (Finset ι)) (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) :
    EulerChoices (fun p : Nat.Primes => {S // S∈A p}) ≃ AllowedDivisorTuple A where
  toFun := choiceTuple
  invFun := tupleChoices
  left_inv c := by
    apply eulerChoices_ext hA
    intro p
    rw [tupleChoices_subset]
    exact choice_primeSubset c p
  right_inv d := Subtype.ext (choiceDivisors_tupleChoices d)

noncomputable def tuplePrimeDensity {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ) : ℂ :=
  ∏ p∈tuplePrimeSupport d, ((p:ℂ)-δ)⁻¹

noncomputable def tupleFourierCoefficient {ι : Type*} [Fintype ι] (δ : ℕ)
    (d : ι → ℕ) (z : ι → ℂ) : ℂ :=
  tuplePrimeDensity δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
    Complex.exp (-∑ i, (Real.log (d i):ℂ)*z i)

open scoped ContDiff

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ContourSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

noncomputable def fourierCoordinateSum (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, EuclideanSpace.proj i

@[simp] theorem fourierCoordinateSum_apply {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    fourierCoordinateSum ι v = ∑ i, v i := by simp [fourierCoordinateSum]

noncomputable def divisorLogVector {ι : Type*} (L : ℝ) (d : ι → ℕ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.log (d i)/L)

@[simp] theorem divisorLogVector_apply {ι : Type*} (L : ℝ) (d : ι → ℕ) (i : ι) :
    divisorLogVector L d i = Real.log (d i)/L := rfl

noncomputable def fourierContour {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (1+Complex.I*(u i : ℂ))/(L:ℂ)

@[simp] theorem fourierContour_re {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) :
    (fourierContour L u i).re = L⁻¹ := by
  simp [fourierContour, Complex.div_ofReal_re]

noncomputable def analyticDensity {ι : Type*} [Fintype ι] (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : ℂ :=
  ∑' d : AllowedDivisorTuple A,
    tuplePrimeDensity δ d.val * (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      F (divisorLogVector L d.val)

@[simp] theorem primeReciprocalPrefix_eq (y : ℕ) :
    primeReciprocalPrefix y = ∑ p∈Nat.primesLE y, (1:ℝ)/p := by
  simp only [primeReciprocalPrefix,primePrefix,one_div]
  exact Finset.sum_subtype_of_mem (fun p : ℕ => (p:ℝ)⁻¹) (fun p hp => (Nat.mem_primesLE.mp hp).2)

noncomputable def uniformEulerError (R : ℕ) (s : ℝ) (y : ℕ) : ℝ :=
  Real.exp (4*R*primeReciprocalPrefix y)*
    (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*primeReciprocalPrefix y+
      2*(Real.exp (genericEulerConstant R/(y:ℝ))-1))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierDerivative

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open LineDeriv

noncomputable def laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V) (G : SchwartzMap V ℂ) :
    SchwartzMap V ℂ := (ℓ m : ℂ) • G + (-1:ℂ) • (∂_{m} G)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_signedLineDeriv (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) (m : V) :
    ContDiff ℝ ∞ (fun v => -fderiv ℝ F v m) := by
  exact (hFs.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

noncomputable def signedDirections (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem signedDirections_compact (ms : List V) (F : V → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (signedDirections ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem signedDirections_smooth (ms : List V) (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (signedDirections ms F) := by
  induction ms with
  | nil => exact hFs
  | cons m ms ih => exact contDiff_signedLineDeriv _ ih m

end FourierDerivative

noncomputable def familyKernel {ι : Type*} (B : Finset (Finset ι)) (w : ι → ℂ) : ℂ :=
  ∏ S∈B, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))

noncomputable def normalizedZetaProduct {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, ((∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i))^((-1:ℤ)^S.card)

noncomputable def eulerGlobalMajorant (R y : ℕ) : ℝ :=
  Real.exp (4*R*primeReciprocalPrefix y+genericEulerConstant R/(y:ℝ))

noncomputable def contourKernel {ι : Type*} (B : Finset (Finset ι))
    (u : EuclideanSpace ℝ ι) : ℂ := familyKernel B (fun i => frequencyW (u i))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ContourIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

noncomputable def kernelConstant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℂ :=
  ∫ u, Φ u*contourKernel B u

noncomputable def kernelAbsoluteConstant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℝ :=
  ∫ u, ‖Φ u*contourKernel B u‖

noncomputable def uniformCoreError (R : ℕ) (c s : ℝ) (y : ℕ) : ℝ :=
  uniformEulerError R s y*(1+(2^R*(R*(2*c)))*(y:ℝ)^(-s))+
    eulerGlobalMajorant R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)

noncomputable def densityCutoff (b : ℕ) (L : ℝ) : ℕ := ⌊L^b⌋₊

noncomputable def densityCoreExponent (b : ℕ) : ℝ := (4*(b:ℝ))⁻¹

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LaplaceTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierLaplace

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def laplaceFrequency (ℓ : V →L[ℝ] ℝ) (m u : V) : ℂ :=
  (ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceFrequency_re (ℓ : V →L[ℝ] ℝ) (m u : V) :
    (laplaceFrequency ℓ m u).re = ℓ m := by simp [laplaceFrequency]

noncomputable def rayVector {α : Type*} [Fintype α] (m : α → V) (y : α → ℝ) : V :=
  ∑ i, y i • m i

noncomputable def positiveOrthantMeasure (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α => volume.restrict (Ioi 0))

instance instSigmaFiniteForallRealPositiveOrthantMeasure {α : Type*} [Fintype α] : SigmaFinite (positiveOrthantMeasure α) := by
  unfold positiveOrthantMeasure
  infer_instance

end FourierLaplace

section SmallFiberCoefficient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def coordinateDirectionList (ι : Type*) [Fintype ι] :
    List (EuclideanSpace ℝ ι) := by
  classical
  exact Finset.univ.toList.map (fun i => EuclideanSpace.single i (1:ℝ))

noncomputable def doubleFibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) : Finset α := by
  classical
  exact R.filter (fun r => (Finset.univ.filter (fun i => b i=r)).card=2)

noncomputable def fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) : EuclideanSpace ℝ ι := by
  classical
  exact ∑ i∈Finset.univ.filter (fun i => b i=r), EuclideanSpace.single i (1:ℝ)

@[simp] theorem laplaceFrequency_coordinate {ι : Type*} [Fintype ι]
    (i : ι) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (EuclideanSpace.single i (1:ℝ)) u =
      frequencyW (u i) := by
  classical
  simp [laplaceFrequency,frequencyW,fourierCoordinateSum_apply,EuclideanSpace.inner_single_right]

@[simp] theorem coordinateDirectionList_multiplier {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) :
    ((coordinateDirectionList ι).map (fun m => laplaceFrequency (fourierCoordinateSum ι) m u)).prod =
      ∏ i, frequencyW (u i) := by
  classical
  simp [coordinateDirectionList,List.map_map,Function.comp_def]

end SmallFiberCoefficient

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def negativeCube {ι : Type*} [Fintype ι] (T : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, -T≤x i ∧ x i≤0}

theorem negativeCube_compact {ι : Type*} [Fintype ι] (T : ℝ) :
    IsCompact (negativeCube (ι:=ι) T) := by
  have h := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := -T) (b := (0:ℝ)))).image
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨x.ofLp, ?_, ?_⟩
    · simpa only [negativeCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hx
    · rfl
  · rintro ⟨y, hy, rfl⟩
    change ∀ i, -T≤y i ∧ y i≤0
    simpa only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hy

noncomputable def cubeIndicator {ι : Type*} [Fintype ι] (T : ℝ) : EuclideanSpace ℝ ι → ℝ :=
  (negativeCube T).indicator (fun _ => 1)

theorem cubeIndicator_compact {ι : Type*} [Fintype ι] (T : ℝ) :
    HasCompactSupport (cubeIndicator (ι:=ι) T) := by
  apply (negativeCube_compact T).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (negativeCube_compact T).isClosed
  exact Set.support_indicator_subset

theorem cubeIndicator_integrable {ι : Type*} [Fintype ι] (T : ℝ) :
    Integrable (cubeIndicator (ι:=ι) T) := by
  apply (integrable_indicator_iff (negativeCube_compact T).measurableSet).mpr
  exact continuous_const.continuousOn.integrableOn_compact (negativeCube_compact T)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CumulativeProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def cumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) : EuclideanSpace ℝ ι → ℝ :=
  cubeIndicator T ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f

theorem cumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (cumulativeExtension T f) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) (cubeIndicator_compact T) hf

theorem cumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cumulativeExtension T f) :=
  hf.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hfs

noncomputable def cumulativeTail {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y in {y | ∀ i, v i≤y i}, f y

section GeneralDirections

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def signedDirectionalList (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F

end GeneralDirections

noncomputable def finTailEmbed (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
    { toFun := fun x => Fin.cons 0 x
      map_add' := by intros; ext i; cases i using Fin.cases <;> simp
      map_smul' := by intros; ext i; cases i using Fin.cases <;> simp }
  A.toContinuousLinearMap

@[simp] theorem finTailEmbed_apply (n : ℕ) (x : Fin n → ℝ) :
    finTailEmbed n x = Fin.cons 0 x := rfl

noncomputable def finDirections (n : ℕ) : List (Fin n → ℝ) :=
  (List.finRange n).map (fun i => Pi.single i 1)

noncomputable def piTailMeasure {n : ℕ} (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => volume.restrict (Ioi (v i)))

instance instSigmaFiniteForallFinRealPiTailMeasure {n : ℕ} (v : Fin n → ℝ) : SigmaFinite (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

instance instIsFiniteMeasureOnCompactsForallFinRealPiTailMeasure {n : ℕ} (v : Fin n → ℝ) : IsFiniteMeasureOnCompacts (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

noncomputable def complexCumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : EuclideanSpace ℝ ι → ℂ :=
  cubeIndicator T ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] F

noncomputable def euclideanFinDirections (n : ℕ) : List (EuclideanSpace ℝ (Fin n)) :=
  (finDirections n).map (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp] theorem euclideanFinDirections_multiplier (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ((euclideanFinDirections n).map
      (fun m => laplaceFrequency (fourierCoordinateSum (Fin n)) m u)).prod =
      ∏ i, frequencyW (u i) := by
  simp only [euclideanFinDirections,finDirections,List.map_map]
  change ((List.finRange n).map (fun i =>
    laplaceFrequency (fourierCoordinateSum (Fin n)) (EuclideanSpace.single i (1:ℝ)) u)).prod = _
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  convert laplaceFrequency_coordinate i u using 1
  congr 2
  exact Subsingleton.elim _ _

noncomputable def cumulativeProfile {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun v => cumulativeExtension tau (fun y => f y.ofLp) (WithLp.toLp 2 v)

theorem cumulativeProfile_compact {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (cumulativeProfile tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  exact (cumulativeExtension_compact tau _ hfc).comp_isClosedEmbedding
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isClosedEmbedding

theorem cumulativeProfile_smooth {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cumulativeProfile tau f) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp) :=
    hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  exact (cumulativeExtension_smooth tau _ hfc hF).comp
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_TensorProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def appendMeasurableEquiv (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n+m) → ℝ) :=
  (Fin.appendHomeomorph n m).toMeasurableEquiv

@[simp] theorem appendMeasurableEquiv_apply (n m : ℕ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    appendMeasurableEquiv n m p = Fin.append p.1 p.2 := rfl

noncomputable def tensorProfile {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin (n+m) → ℝ) : ℝ :=
  f (fun i => v (i.castAdd m)) * g (fun i => v (i.natAdd n))

@[simp] theorem tensorProfile_append {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    tensorProfile f g (Fin.append v w)=f v*g w := by
  simp [tensorProfile]

theorem tensorProfile_compact {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (tensorProfile f g) := by
  have hk : IsCompact ((tsupport f) ×ˢ (tsupport g)) := hf.isCompact.prod hg.isCompact
  have hh : HasCompactSupport (fun p : (Fin n → ℝ) × (Fin m → ℝ) => f p.1*g p.2) := by
    apply hk.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hk.isClosed
    intro p hp
    have hm := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport f hm.1,subset_tsupport g hm.2⟩
  exact hh.comp_isClosedEmbedding (Fin.appendHomeomorph n m).symm.isClosedEmbedding

theorem tensorProfile_smooth {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (tensorProfile f g) := by
  unfold tensorProfile
  exact (hf.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.castAdd m)))).mul
    (hg.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.natAdd n))))

@[simp] theorem logCoordinates_append (X : ℕ) {n m : ℕ}
    (d : Fin n → ℕ) (e : Fin m → ℕ) :
    logCoordinates X (Fin.append d e)=Fin.append (logCoordinates X d) (logCoordinates X e) := by
  ext i
  cases i using Fin.addCases <;> simp [logCoordinates]

@[simp] theorem divisorCoefficient_tensor (X : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (d : Fin n → ℕ) (e : Fin m → ℕ) :
    divisorCoefficient X (tensorProfile F G) (Fin.append d e)=
      divisorCoefficient X F d*divisorCoefficient X G e := by
  simp only [divisorCoefficient,logCoordinates_append,tensorProfile_append,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]
  ring

@[simp] theorem logCoordinates_snoc (X : ℕ) {n : ℕ} (d : Fin n → ℕ) (e : ℕ) :
    logCoordinates X (Fin.snoc d e) = Fin.snoc (logCoordinates X d) (Real.log e/Real.log X) := by
  ext i
  cases i using Fin.lastCases <;> simp [logCoordinates]

@[simp] theorem fiberRay_apply {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (i : ι) : fiberRay b r i=if b i=r then 1 else 0 := by
  classical
  simp [fiberRay,WithLp.ofLp_sum,Finset.sum_apply]

@[simp] theorem append_self_addNat {n : ℕ} {α : Type*} (y z : Fin n → α) (i : Fin n) :
    Fin.append y z (i.addNat n)=z i := by
  rw [←Fin.natAdd_eq_addNat,Fin.append_right]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

def PatternMaps {ι : Type*} (r : Setoid ι) (α : Type*) :=
  {b : ι → α // Setoid.ker b = r}

noncomputable def patternLift {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r → α :=
  Quotient.lift b.val (by
    intro i j hij
    rw [←b.property] at hij
    exact hij)

@[simp] theorem patternLift_mk {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) (i : ι) :
    patternLift b (Quotient.mk r i)=b.val i := rfl

theorem patternLift_injective {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Function.Injective (patternLift b) := by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j =>
      intro h
      apply Quotient.sound
      rw [←b.property]
      exact h

noncomputable def patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) : Finset (ι → α) := Finset.univ.filter (fun b => Setoid.ker b=r)

@[simp] theorem mem_patternClass {ι α : Type*} [Fintype ι] [Fintype α]
    (r : Setoid ι) (b : ι → α) : b∈patternClass r ↔ Setoid.ker b=r := by
  simp [patternClass]

noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))

noncomputable def patternEmbedding {ι α : Type*} {r : Setoid ι} (b : PatternMaps r α) :
    Quotient r ↪ α := ⟨patternLift b,patternLift_injective b⟩

noncomputable def embeddingPattern {ι α : Type*} (r : Setoid ι) (e : Quotient r ↪ α) :
    PatternMaps r α := ⟨fun i => e (Quotient.mk r i),by
  apply Setoid.ext
  intro i j
  change e (Quotient.mk r i)=e (Quotient.mk r j) ↔ r i j
  rw [e.injective.eq_iff,Quotient.eq]⟩

noncomputable def patternEquivEmbedding {ι α : Type*} (r : Setoid ι) :
    PatternMaps r α ≃ (Quotient r ↪ α) where
  toFun := patternEmbedding
  invFun := embeddingPattern r
  left_inv b := by apply Subtype.ext; rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro x
    induction x using Quotient.inductionOn with | h i => rfl

noncomputable def patternClassEquiv {ι α : Type*} [Fintype ι] [Fintype α] (r : Setoid ι) :
    {b // b∈patternClass (α:=α) r} ≃ (Quotient r ↪ α) :=
  (Equiv.subtypeEquivRight (fun b => mem_patternClass r b)).trans (patternEquivEmbedding r)

noncomputable def numericPattern {ι : Type*} [Fintype ι] (r : Setoid ι) : ι → ℕ :=
  fun i => (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val

theorem constant_boxTuple_injective_iff {s h : ℕ} (a : ℤ) (n : Fin s → Fin h) :
    Function.Injective (boxTuple (fun _ => a) n) ↔ Function.Injective n := by
  constructor
  · intro hn i j he
    apply hn
    simp [boxTuple,he]
  · intro hn i j he
    apply hn
    have hv : (n i:ℕ)=(n j:ℕ) := by
      exact_mod_cast (add_left_cancel he : (n i:ℤ)=(n j:ℤ))
    exact Fin.ext hv

noncomputable def patternTupleEquiv {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ) :
    {b // b∈patternClass (α:=Fin h) r} ≃
    {n // n∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => a)} :=
  (patternClassEquiv r).trans
    ((Equiv.embeddingCongr (Fintype.equivFin (Quotient r)) (Equiv.refl (Fin h))).trans
      ((Equiv.subtypeInjectiveEquivEmbedding _ _).symm.trans
        (Equiv.subtypeEquivRight (fun n => by
          simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and,
            constant_boxTuple_injective_iff]))))

@[simp] theorem patternTupleEquiv_apply {ι : Type*} [Fintype ι] (r : Setoid ι) (h : ℕ) (a : ℤ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (j : Fin (Fintype.card (Quotient r))) :
    (patternTupleEquiv r h a b).val j=
      patternLift ⟨b.val,(mem_patternClass r b.val).mp b.property⟩
        ((Fintype.equivFin (Quotient r)).symm j) := rfl

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Detectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def equalityPatternFamily {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Finset (Finset ι) := shiftFamily (fun i => (numericPattern r i:ℤ))

noncomputable def patternBoxShifts {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h) : Fin n → ℕ :=
  fun i => a (p i)+(u (p i):ℕ)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def patternLabels {ι : Type*} [Fintype ι] (r : Setoid ι) :
    ι → Fin (Fintype.card (Quotient r)) :=
  fun i => Fintype.equivFin (Quotient r) (Quotient.mk r i)

def permutedLabels {n : ℕ} (e : Equiv.Perm (Fin n)) : Fin (n+n) → Fin n := Fin.append id e

noncomputable def permutedRay {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) : EuclideanSpace ℝ (Fin (n+n)) :=
  EuclideanSpace.single (i.castAdd n) 1+EuclideanSpace.single ((e.symm i).natAdd n) 1

def functionPerm {ι α : Type*} (e : Equiv.Perm ι) : (ι → α) ≃ (ι → α) where
  toFun f := f ∘ e
  invFun f := f ∘ e.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

noncomputable def weightedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h, k (Setoid.ker b)*divisorSum X F m (fun i => a+(b i:ℕ))

noncomputable def tensorCoefficient {n p : ℕ}
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) : Setoid (Fin (n+p)) → ℝ :=
  fun r => k (Setoid.comap (Fin.castAdd p) r)*l (Setoid.comap (Fin.natAdd n) r)

@[simp] theorem append_ker_left {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]

@[simp] theorem append_ker_right {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_WeightMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def subsetCoefficient (n : ℕ) (r : Setoid (Fin n)) : ℝ :=
  if r=⊥ then (n.factorial:ℝ)⁻¹ else 0

noncomputable def orderedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), weightedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) (subsetCoefficient j) m

noncomputable def matchedPattern {n : ℕ} (e : Equiv.Perm (Fin n)) : Setoid (Fin (n+n)) :=
  Setoid.ker (permutedLabels e)

@[simp] theorem matchedPattern_left {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.castAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.castAdd n)=permutedLabels e (j.castAdd n) ↔ i=j
  simp [permutedLabels]

@[simp] theorem matchedPattern_right {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.natAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.natAdd n)=permutedLabels e (j.natAdd n) ↔ i=j
  simp [permutedLabels]

theorem realEuclidean_compact {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
    Complex.ofReal_zero

theorem realEuclidean_smooth {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hF.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)

noncomputable def cumulativePatternKernel {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (r : Setoid (Fin n)) : ℂ :=
  kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
    (fun v => (cumulativeProfile tau f v.ofLp:ℂ))
    (realEuclidean_compact _ (cumulativeProfile_compact tau f hf))
    (realEuclidean_smooth _ (cumulativeProfile_smooth tau f hf hs))) (equalityPatternFamily r)

@[simp] theorem l2Mass_fin_zero (f : (Fin 0 → ℝ) → ℝ) : l2Mass f=f 0^2 := by
  unfold l2Mass
  have he : (fun x => f x^2)=(fun _ : Fin 0 → ℝ => f 0^2) := by
    funext x
    rw [Subsingleton.elim x 0]
  rw [he,Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ProfileSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def subsetEnumeration {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) : Fin n ↪ Fin h :=
  S.1.orderEmbOfFin S.2 |>.toEmbedding

noncomputable def enumeratePerm {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    {b : Fin n → Fin h // Function.Injective b} :=
  ⟨subsetEnumeration t.1 ∘ t.2,(subsetEnumeration t.1).injective.comp t.2.injective⟩

noncomputable def unorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ))

noncomputable def unorderedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), unorderedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) m

noncomputable def separatedOffsets (s h : ℕ) : Fin (s+1) → ℕ :=
  Fin.snoc (fun _ => h+1) 1

theorem separatedBox_mem {s h : ℕ} (u : Fin s → Fin h) (c : Fin h) :
    Fin.snoc u c∈distinctBox (fun j => (separatedOffsets s h j:ℤ)) ↔
      u∈distinctBox (fun _ : Fin s => ((h+1:ℕ):ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu i j hij
    have he : boxTuple (fun j => (separatedOffsets s h j:ℤ)) (Fin.snoc u c) i.castSucc=
        boxTuple (fun j => (separatedOffsets s h j:ℤ)) (Fin.snoc u c) j.castSucc := by
      simpa [boxTuple,separatedOffsets] using hij
    exact Fin.castSucc_injective s (hu he)
  · intro hu i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
        have hj := (u j).isLt
        have hc := c.isLt
        simp only [boxTuple,separatedOffsets,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        have hi := (u i).isLt
        have hc := c.isLt
        simp only [boxTuple,separatedOffsets,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
      | cast j =>
        congr 1
        apply hu
        simpa [boxTuple,separatedOffsets] using hij

noncomputable def separatedBoxEquiv (s h : ℕ) :
    ({u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h) ≃
    {u // u∈distinctBox (s:=s+1) (h:=h) (fun j => (separatedOffsets s h j:ℤ))} where
  toFun t := ⟨Fin.snoc t.1.1 t.2,(separatedBox_mem t.1.1 t.2).mpr t.1.2⟩
  invFun v := (⟨Fin.init v.1,by
      have hv : Fin.snoc (Fin.init v.1) (v.1 (Fin.last s))=v.1 := Fin.snoc_init_self v.1
      exact (separatedBox_mem _ _).mp (hv.symm ▸ v.2)⟩,v.1 (Fin.last s))
  left_inv t := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [Fin.init]
    · simp
  right_inv v := by
    apply Subtype.ext
    exact Fin.snoc_init_self v.1

noncomputable def orderedDetector (X h m : ℕ) : ℝ :=
  (∑ c : Fin h,theta (m+(1+(c:ℕ))))/Real.log X

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MarkedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def fixLastPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] theorem fixLastPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    fixLastPerm e i.castSucc=(e i).castSucc := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)))=Fin.castAdd 1 (e i)
  simp

@[simp] theorem fixLastPerm_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    fixLastPerm e (Fin.last n)=Fin.last n := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))))=Fin.natAdd n (0 : Fin 1)
  simp

noncomputable def deletedFamily (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (j : ℕ) (t : Fin j → ℝ) : ℝ := f j t+deleteCoordinate (f (j+1)) t

noncomputable def setDivisor (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (S : Finset (Fin h)) : ℝ :=
  divisorSum X (F S.card) M (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ))

noncomputable def finiteSubsetWeight (tau : ℝ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (B : Finset (Fin h)) : ℝ :=
  ∑ S∈B.powerset,setDivisor (fun j => cumulativeProfile tau (f j)) X M h a S

@[simp] theorem cumulativeProfile_zero (tau : ℝ) (n : ℕ) :
    cumulativeProfile tau (0 : (Fin n → ℝ) → ℝ)=0 := by
  ext v
  simp [cumulativeProfile,cumulativeExtension,convolution_def]

@[simp] theorem divisorSum_zero (X M : ℕ) {n : ℕ} (b : Fin n → ℕ) :
    divisorSum X (0 : (Fin n → ℝ) → ℝ) M b=0 := by
  simp [divisorSum,divisorCoefficient]

@[simp] theorem unorderedBlock_zero (X h a M n : ℕ) :
    unorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) M=0 := by
  simp [unorderedBlock]

noncomputable def restrictedUnorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    if S.val⊆B then divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) else 0

noncomputable def restrictedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (A : Setoid (Fin n) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h,A (Setoid.ker b)*
    (if ∀ i,b i∈B then divisorSum X F m (fun i => a+(b i:ℕ)) else 0)

@[simp] theorem restrictedUnorderedBlock_zero (X h a M n : ℕ) (B : Finset (Fin h)) :
    restrictedUnorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) B M=0 := by
  simp [restrictedUnorderedBlock]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RestrictedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def restrictedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) (c : Fin (blockLength lam X)) : ℝ :=
  ∑ j : Fin (k+1),restrictedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) (subsetCoefficient j) (Finset.univ.erase c) m

noncomputable def internalMarked (X h : ℕ) (H : ℕ → Fin h → ℝ) : ℝ :=
  average X (fun m => ∑ c : Fin h,H m c*theta (m+(h+1+(c:ℕ)))/Real.log X)

noncomputable def extendPerm {n : ℕ} (e : Equiv.Perm (Fin n)) (d : ℕ) : Equiv.Perm (Fin (n+d)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin d))).trans finSumFinEquiv)

@[simp] theorem extendPerm_left {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm e d (i.castAdd d)=(e i).castAdd d := by
  simp [extendPerm]

@[simp] theorem extendPerm_right {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin d) :
    extendPerm e d (i.natAdd n)=i.natAdd n := by
  simp [extendPerm]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PairedDetectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def extendLabels {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ) :
    Fin (n+d) → α ⊕ Fin d := Fin.append (Sum.inl ∘ a) Sum.inr

@[simp] theorem extendLabels_left {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin n) :
    extendLabels a d (i.castAdd d)=Sum.inl (a i) := by simp [extendLabels]

@[simp] theorem extendLabels_right {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin d) :
    extendLabels a d (i.natAdd n)=Sum.inr i := by simp [extendLabels]

noncomputable def extraPairLabels {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → ℕ ⊕ Fin d :=
  Fin.append (extendLabels (fun i : Fin n => numericPattern r (i.castAdd p)) d)
    (extendLabels (fun i : Fin p => numericPattern r (i.natAdd n)) d)

noncomputable def extraPairFamily {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Finset (Finset (Fin ((n+d)+(p+d)))) := by
  classical
  exact fiberSubsetFamily (extraPairLabels r d) (Finset.univ.image (extraPairLabels r d))

noncomputable def extraPairProfile {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ) :
    (Fin ((n+d)+(p+d)) → ℝ) → ℝ := tensorProfile (tensorProfile f w) (tensorProfile g w)

theorem extraPairProfile_compact {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w) :
    HasCompactSupport (extraPairProfile f g w) :=
  tensorProfile_compact _ _ (tensorProfile_compact f w hf hw) (tensorProfile_compact g w hg hw)

theorem extraPairProfile_smooth {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (extraPairProfile f g w) :=
  tensorProfile_smooth _ _ (tensorProfile_smooth f w hf hw) (tensorProfile_smooth g w hg hw)

noncomputable def extraPairKernel {n p d : ℕ} (tau sigma : ℝ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (r : Setoid (Fin (n+p))) : ℂ :=
  kernelConstant (sourceFourier (fourierCoordinateSum (Fin ((n+d)+(p+d))))
    (fun v => (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w) v.ofLp:ℂ))
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f g w hf hg hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _
      (extraPairProfile_compact f g w hf hg hw) (extraPairProfile_smooth f g w hfs hgs hws))))
      (extraPairFamily r d)

noncomputable def splitOffsets (s d h : ℕ) : Fin (s+d) → ℕ :=
  Fin.append (fun _ => h+1) (fun _ => 1)

theorem splitBox_mem {s d h : ℕ} (u : Fin s → Fin h) (v : Fin d → Fin h) :
    Fin.append u v∈distinctBox (fun j => (splitOffsets s d h j:ℤ)) ↔
      u∈distinctBox (fun _ => ((h+1:ℕ):ℤ)) ∧ v∈distinctBox (fun _ => (1:ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu
    constructor
    · intro i j hij
      have he : boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (i.castAdd d)=
          boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (j.castAdd d) := by
        simpa [boxTuple,splitOffsets] using hij
      exact Fin.castAdd_inj.mp (hu he)
    · intro i j hij
      have he : boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (i.natAdd s)=
          boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (j.natAdd s) := by
        simpa [boxTuple,splitOffsets] using hij
      have he' := congrArg Fin.val (hu he)
      simp only [Fin.val_natAdd] at he'
      exact Fin.ext (Nat.add_left_cancel he')
  · rintro ⟨hu,hv⟩ i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        congr 1
        apply hu
        simpa [boxTuple,splitOffsets] using hij
      | right j =>
        have hi := (u i).isLt
        have hj := (v j).isLt
        simp only [boxTuple,splitOffsets,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have hi := (v i).isLt
        have hj := (u j).isLt
        simp only [boxTuple,splitOffsets,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
      | right j =>
        congr 1
        apply hv
        simpa [boxTuple,splitOffsets] using hij

noncomputable def splitBoxEquiv (s d h : ℕ) :
    ({u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ))}) ≃
    {u // u∈distinctBox (s:=s+d) (h:=h) (fun j => (splitOffsets s d h j:ℤ))} where
  toFun t := ⟨Fin.append t.1.1 t.2.1,(splitBox_mem t.1.1 t.2.1).mpr ⟨t.1.2,t.2.2⟩⟩
  invFun v := by
    let v1 := fun i : Fin s => v.1 (i.castAdd d)
    let v2 := fun i : Fin d => v.1 (i.natAdd s)
    have he : Fin.append v1 v2=v.1 := by
      funext i
      cases i using Fin.addCases <;> simp [v1,v2]
    have hv : v1∈distinctBox (fun _ => ((h+1:ℕ):ℤ)) ∧ v2∈distinctBox (fun _ => (1:ℤ)) :=
      (splitBox_mem v1 v2).mp (he.symm ▸ v.2)
    exact (⟨v1,hv.1⟩,⟨v2,hv.2⟩)
  left_inv t := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i using Fin.addCases <;> simp

noncomputable def extraBoxLabels {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → Fin (Fintype.card (Quotient r)+d) :=
  Fin.append
    (Fin.append (fun i : Fin n => (patternLabels r (i.castAdd p)).castAdd d) (Fin.natAdd _))
    (Fin.append (fun i : Fin p => (patternLabels r (i.natAdd n)).castAdd d) (Fin.natAdd _))

noncomputable def extraShifts {n p d h : ℕ} (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    Fin ((n+d)+(p+d)) → ℕ :=
  Fin.append
    (Fin.append (fun i : Fin n => h+1+(b (i.castAdd p):ℕ)) (fun i => 1+(c i:ℕ)))
    (Fin.append (fun i : Fin p => h+1+(b (i.natAdd n):ℕ)) (fun i => 1+(c i:ℕ)))

noncomputable def extraAverage {d : ℕ} (X h : ℕ) (H : ℕ → ℝ)
    (W : (Fin d → ℝ) → ℝ) : ℝ :=
  average X (fun m => ∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
    H m * divisorSum X W m (fun i => 1+(c i:ℕ))^2)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CharacterErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

noncomputable def characterMeanError (x : ℝ) (q : ℕ) : ℝ :=
  (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ)

noncomputable def primitiveErrorMass (x : ℝ) (d : ℕ) : ℝ :=
  ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive,
    ‖primeCharacterError x χ‖

noncomputable def arithmeticCutoff (T : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤T then f n else 0,by simp⟩

@[simp] theorem arithmeticCutoff_apply (T n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticCutoff T f n=if n≤T then f n else 0 := rfl

noncomputable def vaughanSecondCoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.vonMangoldt-arithmeticCutoff U ArithmeticFunction.vonMangoldt)*
    (ArithmeticFunction.zeta:ArithmeticFunction ℝ)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_AdditiveSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

noncomputable def bvExp (x : ℝ) : ℂ := Complex.exp (Complex.I*(2*Real.pi*x:ℝ))

@[simp] theorem bvExp_zero : bvExp 0=1 := by simp [bvExp]

@[simp] theorem norm_bvExp (x : ℝ) : ‖bvExp x‖=1 := by simp [bvExp,Complex.norm_exp]

@[simp] theorem bvExp_int (m : ℤ) : bvExp m=1 := by
  unfold bvExp
  have he : Complex.I * ((2*Real.pi*(m:ℝ):ℝ):ℂ)=(m:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]

noncomputable def bvCentered (x : ℝ) : ℝ := x-(⌊x+1/2⌋:ℤ)

noncomputable def bvExponentialVector (N : ℕ) (θ : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n => bvExp (-((n:ℕ):ℝ)*θ))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MultiplicativeSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

noncomputable def characterUnitVector {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    EuclideanSpace ℂ (DirichletCharacter ℂ q) := WithLp.toLp 2 (fun χ => χ u)

noncomputable def sequenceCharacterSum {q N : ℕ} (a : Fin N→ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n:Fin N,a n*χ ((n:ℕ):ZMod q)

noncomputable def modularFourierSum {q N : ℕ} [NeZero q] (a : Fin N→ℂ) (u : ZMod q) : ℂ :=
  ∑ n:Fin N,a n*ZMod.stdAddChar (((n:ℕ):ZMod q)*u)

noncomputable def unitFrequency {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : ℚ := (u.val.val:ℚ)/q

noncomputable def fareyFrequency {Q : ℕ} (x : Σ q:Fin Q,(ZMod (q.val+1))ˣ) : ℚ := unitFrequency x.2

noncomputable def primitiveCharacterMean (Q : ℕ)
    (f : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) : ℝ :=
  ∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
    ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ=>χ.IsPrimitive),f q χ

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_VaughanIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

noncomputable def sequenceSize {N : ℕ} (a : Fin N→ℂ) : ℝ :=
  Real.sqrt (∑ n:Fin N,‖a n‖^2)

noncomputable def sequenceMask {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) : Fin N→ℂ :=
  fun n=>if p n then a n else 0

noncomputable def sieveBilinearConstant (Q M N : ℕ) : ℝ :=
  Real.sqrt ((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*
    Real.sqrt ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))

noncomputable def triangularCharacterSum {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m:Fin M,∑ n:Fin N,if n.val<t m then a m*b n*χ (m.val:ZMod q)*χ (n.val:ZMod q) else 0

noncomputable def arithmeticCharacterSum {q : ℕ} (X : ℕ) (f : ArithmeticFunction ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Icc 1 X,(f n:ℂ)*χ (n:ZMod q)

@[simp] theorem arithmeticCharacterSum_add {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f+g) χ=arithmeticCharacterSum X f χ+arithmeticCharacterSum X g χ := by
  simp [arithmeticCharacterSum,ArithmeticFunction.add_apply,add_mul,Finset.sum_add_distrib]

@[simp] theorem arithmeticCharacterSum_sub {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f-g) χ=arithmeticCharacterSum X f χ-arithmeticCharacterSum X g χ := by
  unfold arithmeticCharacterSum
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change ((f n-g n:ℝ):ℂ)*χ (n:ZMod q)=_
  push_cast
  ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_VaughanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

noncomputable def vaughanFirstSequence (V M : ℕ) : Fin M→ℂ :=
  fun m=>if V < m.val then (ArithmeticFunction.moebius m.val:ℂ) else 0

noncomputable def vaughanSecondSequence (U N : ℕ) : Fin N→ℂ :=
  fun n=>(vaughanSecondCoefficient U n.val:ℂ)

noncomputable def arithmeticL1 (X : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ n∈Finset.Icc 1 X,|f n|

noncomputable def hyperbolaBlock {q : ℕ} (X D E : ℕ)
    (a b : ℕ→ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m∈Finset.Ico D E,a m*χ (m:ZMod q)*
    (∑ n∈Finset.range (X/m+1),b n*χ (n:ZMod q))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DyadicMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

noncomputable def vaughanBilinearBound (Q X T : ℕ) : ℝ :=
  let z:ℝ:=(Q:ℝ)^2*(harmonic (Q^2):ℝ)
  4*(X:ℝ)+Real.sqrt z*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+z*(2*Real.sqrt X)

noncomputable def vaughanShortBound (Q X T : ℕ) : ℝ :=
  let K:=Real.sqrt Q*(1+Real.log Q)
  (T:ℝ)*Real.log T+(T:ℝ)*(2*Real.log (X+1:ℕ)*K)+
    ((T*T:ℕ)*Real.log (T*T:ℕ))*K

noncomputable def conductorHarmonicBound (Q : ℕ) : ℝ := 1+Real.log (Q^2:ℕ)

noncomputable def highConductorBlockBound (Q X T R k : ℕ) : ℝ :=
  2*(Q:ℝ)*vaughanShortBound Q X T+
    ((k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ))*
      (4*(X:ℝ)/(R:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ConductorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

noncomputable def dyadicExponent (x : ℝ) : ℕ := Nat.log 2 ⌊x⌋₊+1

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Density
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem344

def largeGapIndices (C : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧
    C * Real.log (primeAt n : ℝ) <
      (primeAt (n + 1) : ℝ) - (primeAt n : ℝ)}

end Problem344

end

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LogParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DirichletGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

open Finset

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_TaylorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

open Finset

open Complex Filter Topology Finset

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

open Complex Filter Topology Finset Set MeasureTheory

noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

open Complex Finset ArithmeticFunction

open scoped ComplexOrder

def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SiegelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Finset ArithmeticFunction

noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

end

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ZeroFreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Filter Topology Set MeasureTheory Finset

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

end

open Complex Filter Topology Finset

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RieszBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Filter Topology

noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MellinSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

open Complex Real Set MeasureTheory Filter Topology

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

open Complex Real Set MeasureTheory Filter Topology

noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RieszDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

open Complex Real Set MeasureTheory Filter Topology

noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

open Complex Real Set MeasureTheory Filter Topology

noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

open Complex Real Set MeasureTheory Filter Topology

end LargePrimeGaps

end OAI
end


