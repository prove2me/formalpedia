-- Prove2me | Definitions.Def_OAIHecke78B027
-- name    : OAIHecke78B027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:31.680662+00:00
-- url     : https://prove2.me/theorems/18207d42-90e3-460b-bdf2-d018ec2220e7
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 28 of 29
-- statement:
--   Definitions bundle 28 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B023`, `OAIHecke78B024` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Detector.SourceCoefficient`, `Detector.HighSeries`, `Detector.HighValuations`, `Detector.IdealLocalEuler`, `Detector.HighDeletion`, `Detector.MarkedEuler`, `Detector.MarkedLocal`, `Detector.SpectralCompensation`, `Detector.MellinGuarded`, `Detector.InitialMajorant`, `Detector.InitialIntegral`, `Detector.InitialSubseries`, `Detector.RawMellinTerm`, `Detector.RawPhysicalIntegral`, `Detector.RawIndexGrouping`, `Detector.OuterIndex`, `Detector.RawNestedJoin`, `Detector.RawNesting`, `Detector.PhysicalRawIntegral`, `Detector.RawArithmetic`, `Detector.RawSourceIntegral`, `Detector.SixthSeries`, `Detector.SourceTriple`, `Detector.SourceIntegrable`, `Detector.TupleMellin`, `Detector.TupleRows`, `Detector.CompensatedTriple`, `Detector.InitialRows`, `Detector.CompensatedRows`, `Detector.HighRowsLocal`, `PrimeRows.Euler`, `PrimeRows.MarkedEuler`, `PrimeRows.MarkedLocal`, `PrimeRows.MarkedNormalization`, `PrimeRows.FiniteNormalization`, `PrimeRows.MarkedSubset`, `PrimeRows.MarkedCompensation`, `PrimeRows.MarkedContinuation`, `PrimeRows.MarkedHolomorphic`, `PrimeRows.NonprincipalContour`, `PrimeRows.BufferedBin`, `PrimeRows.WeightedTuple`, `PrimeRows.DyadIntegral`, `PrimeRows.SmallDyad`, `Detector.PrincipalSplit`, `PrimeRows.IteratedShift`, `PrimeRows.WZTransport`, `PrimeRows.PhysicalDyad`, `PrimeRows.PhysicalPartition`, `PrimeRows.CanonicalReduction`, `PrimeRows.FirstIntegral`, `PrimeRows.CentralError`, `PrimeRows.CentralRectangle`, `PrimeRows.CentralCube`, `PrimeRows.CubeFiniteIntegral`, `PrimeRows.Moments`, `Detector.DetectorMomentData`, `Hecke.DetectorBatch`, `Detector.DetectorBatch`, `Detector.DetectorMomentGates`, `PrimeRows.CubeCommonProfile`, `Hecke.DetectorAmplitudeFirst`, `Detector.FinalAssemblyCountParameters`, `Moments.DetectorPlainFiberSource`, `Moments.DetectorEnergyInitialState`, `Moments.DetectorPlainExceptional`, `Moments.DetectorPlainUnmarkedState`, `Detector.DetectorPlainUnmarkedField`, `PrimeRows.CentralProduct`, `PrimeRows.CentralCosts`, `PrimeRows.NonfloorMoments`, `Detector.FinalAssemblyMomentInput`, `Detector.FinalAssemblyChosenData`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B027

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Detector.SourceCoefficient
  Detector.HighSeries
  Detector.HighValuations
  Detector.IdealLocalEuler
  Detector.HighDeletion
  Detector.MarkedEuler
  Detector.MarkedLocal
  Detector.SpectralCompensation
  Detector.MellinGuarded
  Detector.InitialMajorant
  Detector.InitialIntegral
  Detector.InitialSubseries
  Detector.RawMellinTerm
  Detector.RawPhysicalIntegral
  Detector.RawIndexGrouping
  Detector.OuterIndex
  Detector.RawNestedJoin
  Detector.RawNesting
  Detector.PhysicalRawIntegral
  Detector.RawArithmetic
  Detector.RawSourceIntegral
  Detector.SixthSeries
  Detector.SourceTriple
  Detector.SourceIntegrable
  Detector.TupleMellin
  Detector.TupleRows
  Detector.CompensatedTriple
  Detector.InitialRows
  Detector.CompensatedRows
  Detector.HighRowsLocal
  PrimeRows.Euler
  PrimeRows.MarkedEuler
  PrimeRows.MarkedLocal
  PrimeRows.MarkedNormalization
  PrimeRows.FiniteNormalization
  PrimeRows.MarkedSubset
  PrimeRows.MarkedCompensation
  PrimeRows.MarkedContinuation
  PrimeRows.MarkedHolomorphic
  PrimeRows.NonprincipalContour
  PrimeRows.BufferedBin
  PrimeRows.WeightedTuple
  PrimeRows.DyadIntegral
  PrimeRows.SmallDyad
  Detector.PrincipalSplit
  PrimeRows.IteratedShift
  PrimeRows.WZTransport
  PrimeRows.PhysicalDyad
  PrimeRows.PhysicalPartition
  PrimeRows.CanonicalReduction
  PrimeRows.FirstIntegral
  PrimeRows.CentralError
  PrimeRows.CentralRectangle
  PrimeRows.CentralCube
  PrimeRows.CubeFiniteIntegral
  PrimeRows.Moments
  Detector.DetectorMomentData
  Hecke.DetectorBatch
  Detector.DetectorBatch
  Detector.DetectorMomentGates
  PrimeRows.CubeCommonProfile
  Hecke.DetectorAmplitudeFirst
  Detector.FinalAssemblyCountParameters
  Moments.DetectorPlainFiberSource
  Moments.DetectorEnergyInitialState
  Moments.DetectorPlainExceptional
  Moments.DetectorPlainUnmarkedState
  Detector.DetectorPlainUnmarkedField
  PrimeRows.CentralProduct
  PrimeRows.CentralCosts
  PrimeRows.NonfloorMoments
  Detector.FinalAssemblyMomentInput
  Detector.FinalAssemblyChosenData
-/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbePhase ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sourceHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (u a : O) : ℂ :=
  actualCongruenceCoefficient C A s hA (u*a^6) * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid u)) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

def bareSourceCoefficient (η : HeckeFamily.Character) (I : Ideal O)
    (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
    correctedFiniteCoefficient I hI A s hA H

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def bareIdealHighCoefficient (η : HeckeFamily.Character) (u : O) (I J K L : Id) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L then
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
      (primaryGenerator I * primaryGenerator J^3) (primaryGenerator K)
      (mul_ne_zero (supported_primaryGenerator_ne_zero I h.2.1)
        (pow_ne_zero _ (supported_primaryGenerator_ne_zero J h.2.2.1)))
      (u*primaryGenerator L^6)
  else 0

def bareIdealHighSummand (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  bareIdealHighCoefficient η u I J K L * fullIdealWeight (x+1/2) I *
    fullIdealWeight (1+3*x) J * fullIdealWeight w K * fullIdealWeight (6*z) L

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev HighIdeal := (Id×Id)×(Id×Id)

def highIdeals (v : PrimeIdeal→₀HighValuation) : HighIdeal :=
  ((idealFromValuations (v.mapRange (fun b=>b.1.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.1.2) rfl)),
   (idealFromValuations (v.mapRange (fun b=>b.2.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.2.2) rfl)))

def highValuationTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (highIdeals v).1.1 (highIdeals v).1.2
    (highIdeals v).2.1 (highIdeals v).2.2

def highPrimeTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

lemma primaryGenerator_prime_power (p : O) (hp : p≠0) (hprimary : goodLambda^2∣p-1) (e : ℕ) :
    primaryGenerator ((Ideal.span {p})^e)=p^e := by
  rw [primaryGenerator_pow,primaryGenerator_span p hp hprimary]

def idealHighLocalFactor (η : HeckeFamily.Character) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highIdealMask (S : Finset Id) (D I J K L : Id) : ℂ :=
  completedMask S D I J *
    (if ∀ P∈S,¬P∣K then 1 else 0) * (if ∀ P∈S,¬P∣L then 1 else 0)

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedHighArray (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2

def excludedHighPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedHighArray S η x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealMarkedLocalFactor (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*highPrimeTerm η x w z P ((e.val,l),(k,m))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def spectralCompensatedHigh (S : Finset Id) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η 1 x w z

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def physicalMellinCoefficientTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (X : ℝ) (H : O) (t z : ℂ) : ℂ :=
  if hA : completedIndex I J≠0 then
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ)*
      actualCongruenceCoefficient C (completedIndex I J) s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)
  else 0

def guardedHighMellinCoefficient (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (X : ℝ) (H : O) (x z : ℂ) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J then
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
        (completedIndex I J) s (supportedElement_ne_zero _ (supported_completed _ _
          ((supported_span_primaryGenerator_iff I).mpr h.2.1)
          ((supported_span_primaryGenerator_iff J).mpr h.2.2))) H *
      (fullIdealWeight (x+1/2) I*fullIdealWeight (1+3*x) J)
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
open ActualEisensteinCubic CubicEisenstein ProbeRow
attribute [local fun_prop] fullIdealWeight_continuous
local notation "O" => ActualEisensteinCubic.O
abbrev FullHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×(Ideal O×Ideal O))

def initialHighMajorant (σ υ ξ : ℝ) (p : FullHighIndex) : ℝ :=
  ‖frequencyWeight (ξ:ℂ) p.1‖*highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) p.2

def fullHighCoefficient (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : FullHighIndex) : ℂ :=
  mask p.1*frequencyWeight z p.1*
    markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

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
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

local instance instCountableO_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_rafa68a_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
def initialHighOnLines (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) (p : HeightSpace) : ℂ :=
  fullHighCoefficient S D η mask ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) i

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

abbrev RawHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×Ideal O)

def rawHighEmbedding (p : RawHighIndex) : FullHighIndex := (p.1,(p.2.1,(p.2.2,1)))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rawPhysicalMellinTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (H : O) (t w z : ℂ) : ℂ :=
  physicalMellinCoefficientTerm η C S D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) X H t z *fullIdealWeight w K*
    (Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*mellin (paperRadialFourier W0) z*mellin W1 w

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
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def SourceRawIndex (S : Finset (Ideal O)) :=
  {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}

instance instCountableSourceRawIndex (S : Finset (Ideal O)) : Countable (SourceRawIndex S) := inferInstanceAs (Countable {_p : RawHighIndex // _})

def sourceRawEmbedding (S : Finset (Ideal O)) (i : SourceRawIndex S) : FullHighIndex :=
  rawHighEmbedding i.val

def originalRawOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  rawPhysicalMellinTerm η (calibrationForSet S hS) S D i.val.2.1.1 i.val.2.1.2 i.val.2.2 i.property.1
    W0 W1 X Y Z i.val.1.val ((4:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_2 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_2 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

abbrev SourceOuter (S : Finset (Ideal O)) := {K : Ideal O // Supported K ∧ ∀P∈S,¬P∣K}
abbrev CompletedPair := Ideal O×Ideal O

def sourceRawGrouping (S : Finset (Ideal O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl

def sourceRawGroupingMeasurable (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

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

def sourceOuterEquiv (S : Finset (Ideal O)) : SourceOuter S ≃
    {K : {I : Ideal O // Supported I} // ∀P∈S,¬P∣K.val} where
  toFun K := ⟨⟨K.val,K.property.1⟩,K.property.2⟩
  invFun K := ⟨K.val.val,K.val.property,K.property⟩
  left_inv _K := rfl
  right_inv _K := rfl

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
open CompletedGauss CanonicalQuadraticSieve ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def rawNestedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'K : SourceOuter C.excluded,verticalIntegral υ (fun w=>verticalIntegral 4 (fun t=>
    ∑'IJ : CompletedPair,verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C C.excluded D IJ.1 IJ.2 K.val K.property.1 W0 W1 X Y Z H.val t w z)))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_3_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_3_rafa68a_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance instMeasurableSpaceO : MeasurableSpace O := ⊤
local instance instMeasurableSingletonClassO : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance instMeasurableSpaceIdealO : MeasurableSpace (Ideal O) := ⊤
local instance instMeasurableSingletonClassIdealO : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩

local instance instMeasurableSpaceSourceRawIndex (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance instMeasurableSingletonClassSourceRawIndex (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

abbrev PhysicalNestedSpace (S : Finset (Ideal O)) := SourceOuter S×(ℝ×(ℝ×(CompletedPair×(ℝ×NonzeroFrequency))))

def physicalRawNesting (S : Finset (Ideal O)) : SourceRawIndex S×HeightSpace ≃ᵐ PhysicalNestedSpace S :=
  ((sourceRawGroupingMeasurable S).prodCongr (MeasurableEquiv.refl HeightSpace)).trans physicalNestingEquiv

def originalNestedOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (p : PhysicalNestedSpace S) : ℂ :=
  originalRawOnLines η S hS D W0 W1 X Y Z
    ⟨(p.2.2.2.2.2,(p.2.2.2.1,p.1.val)),p.1.property⟩ ((p.2.2.1,p.2.2.2.2.1),p.2.1)

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
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_4_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_4_rafa68a_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance instMeasurableSpaceO_1_rafa68a_1 : MeasurableSpace O := ⊤
local instance instMeasurableSingletonClassO_1_rafa68a_1 : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance instMeasurableSpaceIdealO_1_rafa68a_1 : MeasurableSpace (Ideal O) := ⊤
local instance instMeasurableSingletonClassIdealO_1_rafa68a_1 : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩
local instance instMeasurableSpaceSourceRawIndex_1 (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤

local instance instMeasurableSingletonClassSourceRawIndex_1_rafa68a_1 (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩
def rawPhysicalTotalIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def rawArithmeticSeries (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) : ℂ :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

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
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_5_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_5_rafa68a_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance instMeasurableSpaceSourceRawIndex_2 (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤

local instance instMeasurableSingletonClassSourceRawIndex_2_rafa68a_1 (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩
def rawSourceOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  initialHighOnLines S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val))
    3 3 2 (sourceRawEmbedding S i) p *sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

def rawSourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    rawArithmeticSeries S D η (calibrationForSet S hS) ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve HeckeInverseAmplification ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SixthInnerIndex := HeckeInverseAmplification.NonzeroIdeal×((Id×Id)×Id)

def sixthRawEquiv : FreeRow×SixthInnerIndex ≃ RawHighIndex :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr sixthFrequencyEquiv (Equiv.refl _))

def nonzeroLastEquiv : SixthInnerIndex ≃ {p : (Id×Id)×(Id×Id) // p.2.2≠0} where
  toFun p := ⟨(p.2.1,(p.2.2,p.1.val)),p.1.property⟩
  invFun p := (⟨p.val.2.2,p.property⟩,(p.val.1,p.val.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

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
open ProbeMellinBoundary ProbeCompleted HeckeInverseAmplification CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceRowSeries (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (C : CalibrationData) (D : Ideal O) (x w z : ℂ) : ℂ :=
  ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
    markedIdealHighSeries S D η u.val x w z

def sourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

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
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_6_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_6_rafa68a_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance instMeasurableSpaceSourceRawIndex_3 (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤

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
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tupleSourceSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,
    (-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)*
      sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

def tupleSourceTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    tupleSourceSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tupleIndexedCoefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) (x w : ℂ) : ℂ :=
  (-1:ℂ)^J.card*(∏i∈J,(elementNorm (p i):ℂ)^(-w))*
    (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x)

def indexedCompensatedHigh {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (u : O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
    markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z

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
open ProbeMellinBoundary CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def compensatedRowSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  (∏i,(elementNorm (p i):ℂ)^(z-1))*
    ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      indexedCompensatedHigh η S p u.val x w z

def compensatedRowTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    compensatedRowSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

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
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highRowOnLines (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u*
    markedIdealHighSeries S D η u.val ((σ:ℂ)+t.1.1*Complex.I)
      ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)

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
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance instCountableO_7_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instMeasurableSpaceFreeRow : MeasurableSpace FreeRow := ⊤

local instance instMeasurableSingletonClassFreeRow_rafa68a_1 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
def compensatedRowOnLines {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
    ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
  (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
    (star (C.residueMonoid u.val)*frequencyWeight ((2:ℂ)+t.1.2*Complex.I) u*
      indexedCompensatedHigh η S p u.val ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def rowHighPrimeTerm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

def idealRowHighLocalFactor (η : HeckeFamily.Character) (u : O) (P : Id) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, ∑' k : ℕ, ∑' m : ℕ,
    bareIdealHighSummand η u x w z (P^e.val) (P^l) (P^k) (P^m)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def targetRow (η : Character) (u : FreeRow) : Character := η.product (rawRow u).inverse

def localCorrection (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open ActualEisensteinCubic ProbeEulerFinsupp ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedRowArray (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2

def excludedRowPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedRowArray S η u x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealRowMarkedLocalFactor (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*rowHighPrimeTerm η u x w z P ((e.val,l),(k,m))

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def localNormalization (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def globalNormalization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
    (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

def spectralCompensatedRow (S : Finset (Ideal O)) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (η : Character) (u : O) (x w z : ℂ) (B q : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def compensatedLocalCorrection (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  B*markedLocalCorrection η u P x w z-q*localCorrection η u P x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
  (continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
    ∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z (B P.val) (q P.val))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def physicalCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) : ℂ :=
  continuedCompensatedRow S hS T hT η u x w z
    (fun P=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x)
    (fun P=>(P.val.absNorm:ℂ)^(-w))

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
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem contourTupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def continuedPhysicalRowKernel {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z x w z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z)

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
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def sourceDetectorFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) : Sum Bool ι→Character :=
  Sum.elim (fun b=>if b then rowCharacter S hS u else (targetRow η u).excludePrimes S hS) ψ

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_denominator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl false)=(targetRow η u).excludePrimes S hS := rfl

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_numerator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl true)=rowCharacter S hS u := rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def physicalDyadNorm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℝ :=
  ∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i (P i).val (P i).property) W Y x w z‖

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def absolutePhysicalDyadIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) : ℝ :=
  ∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
      physicalDyadNorm S hS hmax η R T hT W Yp ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance instCountableO_8_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instMeasurableSpaceFreeRow_1 : MeasurableSpace FreeRow := ⊤

local instance instMeasurableSingletonClassFreeRow_1_rafa68a_1 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
def principalFreeRow : FreeRow := ⟨1,one_ne_zero,by
  intro P
  simp [Ideal.span_singleton_one,←Ideal.one_eq_top]⟩

def rowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure

def principalRowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
      indexedCompensatedHigh η S p 1 ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
local instance instCountableO_solutions_rafa68a_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instMeasurableSpaceFreeRow : MeasurableSpace FreeRow := ⊤

local instance instMeasurableSingletonClassFreeRow_rafa68a_2 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
def shiftedRowInner {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z l : ℝ) (q : ℝ×ℝ) : ℂ :=
  ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((3:ℂ)+q.1*I) ((l:ℂ)+t*I) ((2:ℂ)+q.2*I)

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

def continuedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

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

def finitePhysicalRows {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val.val) W0 W1 X Y Z u

def weightedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u P hPS W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def physicalRowValue {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

def principalPhysicalPool {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z

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

def rowAmplitudeOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1))*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u
        ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I))

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
variable {ι : Type*} [Fintype ι]

def centralRowIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

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
variable {ι : Type*} [Fintype ι]

def centralRectangleIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ |t.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

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
variable {ι : Type*} [Fintype ι]

def centralCubeIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

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
variable {ι : Type*} [Fintype ι]

def cubeWeightedRow {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
    (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open ProbePhysical

def momentData (η : Character) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

def momentElement (u : FreeRow) : NonzeroElement := ⟨u.val,u.property.1⟩

theorem momentData_coeff (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I=
      idealCoeff η I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    idealCoeff_eq_row η ((momentData η).character (momentElement u)) rowMaskElement 1 u.val
      ((momentData η).character_spec (momentElement u)) I

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val∉S) :
    idealCoeff ((momentData η).character (momentElement u)) P.val=
      idealCoeff η P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,if_pos hc,one_mul]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) I := by
  have he : idealCoeff (rowCharacter S hS u)=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=_
    rw [excludedTarget_prime]
    by_cases hP : P.val∈S
    · rw [if_pos hP,momentData_coeff,fixedSourcePrincipal_prime,if_pos hP,zero_mul]
    · rw [if_neg hP,rawRow_prime_outside S hS hbad u P hP,
        momentData_prime_outside S hS hbad _ u P hP,
        fixedSourcePrincipal_prime,if_neg hP,one_mul]
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((targetRow η u).excludePrimes S hS) I=
      conj (idealCoeff ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) I) := by
  have he : idealCoeff ((targetRow η u).excludePrimes S hS)=
      idealCoeff (((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)).inverse) := by
    apply hom_eq_of_primes
    intro P
    rw [idealCoeff_inverse_conj]
    change idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=_
    rw [target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [if_pos hP,momentData_coeff,excludedTarget_prime,if_pos hP,zero_mul,map_zero]
    · rw [if_neg hP,momentData_prime_outside S hS hbad _ u P hP,
        excludedTarget_prime,if_neg hP,idealCoeff_inverse_conj,map_mul]
      simp only [starRingEnd_self_apply]
  simpa only [idealCoeff_inverse_conj] using congrArg (fun F : Ideal O→*₀ℂ => F I) he

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

theorem momentData_product_raw (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData χ).character (momentElement u)) I=
      idealCoeff (χ.product (rawRow u)) I := by
  have he : idealCoeff ((momentData χ).character (momentElement u))=
      idealCoeff (χ.product (rawRow u)) := by
    apply hom_eq_of_primes
    intro P
    rw [momentData_coeff,idealCoeff_product,rawRow_coeff,fixedSourcePrincipal_prime]
    simp
  exact congrArg (fun f : Ideal O→*₀ℂ=>f I) he

theorem inverse_row_twist_moment_coeff (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((rawRow u).inverse.product χ) I=
      conj (idealCoeff ((momentData χ.inverse).character (momentElement u)) I) := by
  rw [momentData_product_raw,idealCoeff_product,idealCoeff_product,
    idealCoeff_inverse_conj,idealCoeff_inverse_conj,map_mul]
  simp only [starRingEnd_self_apply]
  ring

variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions_1 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→RowData :=
  Sum.elim (fun b=>if b then momentData (fixedSourcePrincipal S hS)
    else momentData (η.inverse.excludePrimes S hS))
    (fun θ=>momentData (HeckeRayQuotient.character M H hH θ).inverse)

def sourceMomentReverse : Sum Bool (RayQuotient.Characters M H)→Bool :=
  Sum.elim (fun b=>!b) (fun _=>true)

theorem source_family_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) I=
      if sourceMomentReverse M H j then
        conj (idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I)
      else idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I := by
  rcases j with b|θ
  · cases b
    · simpa [sourceMomentReverse,sourceMomentData] using denominator_moment_coeff S hS hbad η u I
    · simpa [sourceMomentReverse,sourceMomentData] using numerator_moment_coeff S hS hbad u I
  · exact inverse_row_twist_moment_coeff (HeckeRayQuotient.character M H hH θ) u I
end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

structure Batch (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  data : Label→RowData
  reverse : Label→Bool
  row_coeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (family u j) I=
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤ mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤ mesh
  supply : 7/37≤∑ s∈slots,widths s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

abbrev Batch.Bin (B : Batch M H Label Slot U a ε tstar T allowance i) :=
  BinLabel B.slots ((2*a-1)/2) B.binWidth

def Batch.fiberRows (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  fiber B.rows B.family U a ε tstar T allowance i B.witness B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) bin j J K

def Batch.fiber (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : Fiber M H Label Slot U a ε tstar T allowance i :=
  toFiber M H B.rows B.family U a ε tstar T allowance i B.witness B.row_norm B.data B.reverse
    B.row_coeff B.slots B.profile B.upper B.widths B.external B.mesh B.binWidth B.mesh_nonneg
    B.binWidth_pos B.widths_pos B.widths_mesh B.supply bin j J K hne

end SevenEighths.HeckeDetectorBatch

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => HeckeFamily.O

def retainedProjection (R : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) : FreeRow :=
  if u∈R then u else u0

@[simp] theorem retainedProjection_of_mem (R : Finset FreeRow) (u0 u : FreeRow) (hu : u∈R) :
    retainedProjection R u0 u=u := by simp [retainedProjection,hu]

theorem retainedProjection_mem (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R) (u : FreeRow) :
    retainedProjection R u0 u∈R := by
  unfold retainedProjection
  split_ifs with hu
  · exact hu
  · exact h0

variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions_2 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def retainedSourceBatch {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (hw : ∀u∈R,SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) U a ε tstar T allowance i)
    (hrow : ∀u∈R,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0≤ mesh) (hb : 0<binWidth)
    (hwpos : ∀s∈slots,0<widths s) (hwmesh : ∀s∈slots,widths s≤ mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i where
  rows := R
  family := fun u=>sourceDetectorFamily S hS.prime η (retainedProjection R u0 u)
    (rayCubeFamily M H hH (retainedProjection R u0 u))
  witness := fun u=>hw (retainedProjection R u0 u) (retainedProjection_mem R u0 h0 u)
  row_norm := hrow
  data := sourceMomentData M H hH S hS.prime η
  reverse := sourceMomentReverse M H
  row_coeff := by
    intro u hu j I
    rw [retainedProjection_of_mem R u0 u hu]
    exact source_family_moment_coeff M H hH S hS.prime hS.bad η u j I
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hm
  binWidth_pos := hb
  widths_pos := hwpos
  widths_mesh := hwmesh
  supply := hsupply

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve
open InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance instFintypeSumBoolSubtypeMulCharQuotientOIdealComplexMemSubgroupCharacters:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

def sourceMomentConductorBound (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℝ:=
  1+∑j:Sum Bool (RayQuotient.Characters M H),
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeArithmeticSum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace) : ℂ :=
  ∑u∈R,frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorAmplitudeFirst
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorFiberPartition
open HeckeDetectorPhysicalSelection HeckeDetectorAdaptiveCutoff

def amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U cap mesh hm widths physical u=bin)

def rowMean {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : ℝ :=
  weightedMean slots widths (fun s => HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s))

def classMean {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (widths : Slot→ℝ) (bin : BinLabel slots cap mesh) : ℝ :=
  weightedMean slots widths (binValue slots cap mesh bin)

end SevenEighths.HeckeDetectorAmplitudeFirst

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0<cB
  cB_one : cB≤1
  kB_pos : 0<kB
  cH_pos : 0<cH
  cH_one : cH≤1
  kH_pos : 0<kH
  balanced : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν)
  high : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm)

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def plainProfile (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (j:ℕ)(σ t:ℝ):ℝ→ℂ:=
  twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
    (orientedFrequency F.reverse t)

def slotWindow (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)(x:ℝ):ℂ:=
  conj (F.profile s x*(x:ℂ)^(F.external s-1))

def fiberPool (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot):
    Finset (CenteredMomentAddedZeroUniform.Tuple selected):=
  completePool (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (9/4) (9/4) (U^F.m) (U^F.m)

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ):Ideal O→ℂ:=
  finiteColumnCoefficient (fiberPool F selected)
    (uncenteredProfileCoefficient 1 (fun _:selected=>idealCoeff η.inverse)
      (fun s:selected=>slotWindow F s.val) (fun s:selected=>U^(F.widths s.val))
      (plainProfile F j σ t) (plainProfile F k σ t) (U^F.m) (U^F.m) 1 1 1)

def radialMajorant : 𝓢(ℝ,ℂ):=
  Classical.choose DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant

lemma radialMajorant_compact : HasCompactSupport (radialMajorant:ℝ→ℂ):=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).1

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=>h.1
  nonexceptional:=fun _ h=>h.2

def detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=>detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem radialMajorant_support_bound:
    ∃bΦ:ℝ,0<bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {Δ:ℝ}{D:Parameters.HighData Δ}

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def retainedSourceEnergy (keep:O→Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

variable {Δ:ℝ}{D:Parameters.HighData Δ}

end SevenEighths.CenteredMomentDetectorPlainExceptional

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open HeckeFamily HeckeDetectorRawFiber CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O

def allowance (δ m:ℝ):ℝ:=δ+max 0 (2*m-1)

lemma allowance_nonneg (δ m:ℝ)(hδ:0≤δ):0≤allowance δ m:=
  add_nonneg hδ (le_max_left _ _)

lemma padded_modulus (η:Character)(U δ m:ℝ)(hU:1≤U)
    (hη:(η.modulus.absNorm:ℝ)≤U^δ):
    (η.modulus.absNorm:ℝ)≤U^(allowance δ m):=
  hη.trans (Real.rpow_le_rpow_of_exponent_le hU (le_add_of_nonneg_right (le_max_left _ _)))

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T heightAllowance:ℝ}{i:ℕ}

def state (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState U 0 bΦ:=
  initialState η Q Φ bΦ U (allowance δ F.m) hU (allowance_nonneg _ _ hδ) hs hp
    (padded_modulus η U δ F.m hU hη)

end SevenEighths.CenteredMomentDetectorPlainUnmarkedState

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.ProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainMomentParameters
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def radialSupportUpper : ℝ := Classical.choose radialMajorant_support_bound

variable {Δ:ℝ}

end SevenEighths.ProbeDetectorPlainUnmarkedField

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

def centralRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
    continuedCorrection S hS η u x w z

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def centralRemainingScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions_5 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Moments (B.fiber bin j J K hne) Δ c κ C height εm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ)≤d → d≤7/8 → 51/100<a → a≤1 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im|≤height →
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z Δ
      (if 2*a-1≤5/6 then counts.cB else counts.cH)
      (if 2*a-1≤5/6 then counts.kB else counts.kH) C height D.t

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

def ChosenMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
    ∃D:HighData (HeckeZeroSupremum.beta-7/8),∃F:SourceData D,
    ∃counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
    ∃mesh:ℝ→ℝ,(∀t:ℝ,0<t→0< mesh t) ∧
    ∀D:HighData (HeckeZeroSupremum.beta-7/8),(∀j,D.ell j≤ mesh D.t/200)→
    ∀F:SourceData D,∀counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

end SevenEighths.ProbeFinalAssembly

end

end OAI
end


