-- Prove2me | Definitions.Def_CritWinSpin_SamplerNumericalData
-- name    : CritWinSpin_SamplerNumericalData
-- status  : Definition
-- author  : @Maxliu
-- created : 2026-11-17T18:15:47.189291+00:00
-- url     : https://prove2.me/theorems/998c2ca8-3817-46b2-9b9b-ab085f84cf30
-- title:
--   Numerical data and finite laws of the sampler in Theorem 4.4
-- statement:
--   This interface fixes the numerical construction used by the sampler in Theorem 4.4: encoded rational inputs, preprocessing and precision schedules, finite Gaussian and spin draws, rounded drift and Euler updates, and the two sampling branches.
--
--   The trajectory, kernel, and trial laws are the finite pushforwards of explicit random-bit blocks. The same functions are used by the machine compilation and by the separate approximation and running-time proofs. These common definitions make those proofs refer to one concrete sampler.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 4.4, p.17, equation (24), and its finite-precision sampler construction.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_Wpot
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_SamplerAnalyticData

set_option linter.all false

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.DensityAnalysis

namespace EulerDensity
open ProbabilityTheory MeasureTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace

end EulerDensity

namespace EulerDensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

end EulerDensity

end CritWinSpin.Implementation.DensityAnalysis

end

end

section

set_option autoImplicit false
open MeasureTheory

namespace CritWinSpin.Implementation.MetropolisFlux

variable {E : Type*} [MeasurableSpace E]

end CritWinSpin.Implementation.MetropolisFlux

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.LangevinAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end CritWinSpin.Implementation.LangevinAlgebra

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.DensityIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

end CritWinSpin.Implementation.DensityIntegrals

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.LangevinJointDensity

open DensityAnalysis LangevinAlgebra

end CritWinSpin.Implementation.LangevinJointDensity

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CritWinSpin.Implementation.GaussianMoments

end CritWinSpin.Implementation.GaussianMoments

end

end

section

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CritWinSpin.Implementation.ContractiveOperator

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

variable (P : (E → ℝ) → E → ℝ) (q : ℝ)

end CritWinSpin.Implementation.ContractiveOperator

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.NoiseOperator

open ContractiveOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

end CritWinSpin.Implementation.NoiseOperator

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.LangevinDefect

open DensityAnalysis LangevinAlgebra LangevinJointDensity

end CritWinSpin.Implementation.LangevinDefect

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.LangevinConvergence

open DensityAnalysis LangevinAlgebra ContractiveOperator

end CritWinSpin.Implementation.LangevinConvergence

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin.Implementation.KernelTests

variable {A X : Type*} [Fintype A]

end CritWinSpin.Implementation.KernelTests

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace CritWinSpin.Implementation.LangevinBudget
open DensityAnalysis LangevinAlgebra ContractiveOperator LangevinConvergence

end CritWinSpin.Implementation.LangevinBudget
end

end

section

open MeasureTheory IsingLTL.BeliefProp

set_option autoImplicit false
set_option maxHeartbeats 2400000

open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeAnalysis

section SpinAndPhi

end SpinAndPhi

section LinearAlgebraAndHessian

end LinearAlgebraAndHessian

end CritWinSpin.Implementation.EnvelopeAnalysis

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.SmoothGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end CritWinSpin.Implementation.SmoothGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeGeometry

open EnvelopeAnalysis

end CritWinSpin.Implementation.EnvelopeGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.PiVolumeTransfer

open DensityAnalysis

end CritWinSpin.Implementation.PiVolumeTransfer

end

end

section

set_option autoImplicit false
open MeasureTheory

namespace CritWinSpin.Implementation.Regularization

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f R : Ω → ℝ)

end CritWinSpin.Implementation.Regularization

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RegularizedGibbsMoments

open DensityAnalysis

end CritWinSpin.Implementation.RegularizedGibbsMoments

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeMoments

open DensityAnalysis EnvelopeGeometry

end CritWinSpin.Implementation.EnvelopeMoments

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin
open scoped NNReal

namespace CritWinSpin.Implementation.EnvelopeCertificate
open DensityAnalysis LangevinBudget EnvelopeGeometry

end CritWinSpin.Implementation.EnvelopeCertificate
end

end

section
set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.MomentBudget

end CritWinSpin.Implementation.MomentBudget
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeParameters
open DensityAnalysis EnvelopeGeometry LangevinBudget

end CritWinSpin.Implementation.EnvelopeParameters
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open Turing StateTransition QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def binaryWords : List Bool → List Bool × List Bool
  | true :: b :: xs => let r := binaryWords xs; (b :: r.1, r.2)
  | false :: _ :: xs => ([], xs)
  | _ => ([], [])

def binaryTotal (xs : List Bool) : ℕ × List Bool :=
  (Word.value (binaryWords xs).1, (binaryWords xs).2)

def integerTotal (xs : List Bool) : ℤ × List Bool :=
  let n := binaryTotal xs.tail
  (Signed.value (xs.head?.getD false) n.1, n.2)

def rationalTotal (xs : List Bool) : ℚ × List Bool :=
  let n := integerTotal xs
  let d := binaryTotal n.2
  (mkRat n.1 d.1, d.2)

def tupleWords : List Bool → List Bool × List Bool
  | a :: b :: xs => if a = b then
      let r := tupleWords xs; (a :: r.1, r.2)
    else ([], xs)
  | _ => ([], [])

def requestPair (xs : List Bool) : List Bool × List Bool :=
  let a := tupleWords xs
  (a.1, (tupleWords a.2).1)

end CritWinSpin.LocalTM2

end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2.Compiled

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def dot (x : List ℚ × List ℚ) : ℚ :=
  ((x.1.zip x.2).map (fun p => p.1 * p.2)).sum

def matrixVector (x : List (List ℚ) × List ℚ) : List ℚ :=
  x.1.map (fun row => dot (row, x.2))

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

namespace DyadicRounding

end DyadicRounding

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
namespace FiniteTicket

end FiniteTicket
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def rationalFloor (q : ℚ) : ℕ := if q < 0 then 0 else q.num.natAbs / q.den

def naturalSum (xs : List ℕ) : ℕ := rationalFloor ((xs.map (fun n : ℕ => (n : ℚ))).sum)

def normalizedRationals (xs : List ℚ) : List ℚ := xs.map (fun x => x / xs.sum)

def quantizedCounts (x : List ℚ × ℕ) : List ℕ :=
  let p := normalizedRationals x.1
  let cs := p.map (fun q => rationalFloor ((x.2 : ℚ) * q))
  if cs.isEmpty then [] else (cs.head?.getD 0 + (x.2 - naturalSum cs)) :: cs.tail

abbrev BucketState := ℕ × ℕ × Bool

def bucketStep (x : BucketState × ℕ) : BucketState :=
  let s := x.1
  if s.2.2 then s else
    if s.2.1 < x.2 then (s.1, s.2.1, true) else (s.1 + 1, s.2.1 - x.2, false)

def bucketScan (x : List ℕ × ℕ) : ℕ :=
  (x.1.foldl (fun s c => bucketStep (s, c)) (0, x.2, false)).1

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def roundTowardZero (u : ℚ × ℚ) : ℚ :=
  if u.1 < 0 then -u.2 * (rationalFloor (-u.1 / u.2) : ℚ)
    else u.2 * (rationalFloor (u.1 / u.2) : ℚ)

def clampTwo (x : ℚ) : ℚ := if 2 < x then 2 else if x < -2 then -2 else x

def clampedRound (u : ℚ × ℚ) : ℚ := clampTwo (roundTowardZero u)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

def reciprocalExp (x : ℚ) (n : ℕ) : ℚ := ((1 + x / (n : ℚ)) ^ n)⁻¹

def reciprocalTerms (x d : ℚ) : ℕ := ⌊2 * x ^ 2 / d⌋₊ + 2

def expNegativeApprox (x d : ℚ) : ℚ :=
  if 1 / d ≤ x then 0 else reciprocalExp x (reciprocalTerms x d)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def exponentialTerms (x : ℚ × ℚ) : ℕ := rationalFloor (2 * x.1 ^ 2 / x.2) + 2

def expWithFuel (u : (ℚ × ℚ) × List Unit) : ℚ :=
  let x := u.1.1
  let d := u.1.2
  let n := exponentialTerms (x, d)
  if 1 / d ≤ x then 0 else
    1 / ((u.2.take n).map (fun _ => 1 + x / (n : ℚ))).prod

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

def weightDenominatorBound (S : SpinLaw) : ℕ := 1 + ∑ a ∈ S.A, (S.ρ a).den

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

def naturalProduct (xs : List ℕ) : ℕ :=
  rationalFloor ((xs.map (fun n : ℕ => (n : ℚ))).prod)

def baseDigits (u : (ℕ × ℕ) × List Unit) : List ℕ :=
  (List.range u.2.length).map (fun i =>
    (u.1.2 / naturalProduct ((u.2.take i).map (fun _ => u.1.1))) % u.1.1)

def alphabet (S : SpinLaw) : List ℚ := S.A.toList

def configurationValues (S : SpinLaw) (u : List Unit × ℕ) : List ℚ :=
  (baseDigits (((alphabet S).length, u.2), u.1)).map
    (fun i => ((alphabet S)[i]?).getD 0)

def enumerationValues (S : SpinLaw) (u : List Unit × List Bool) : List (List ℚ) :=
  let count := naturalProduct (u.1.map (fun _ => (alphabet S).length))
  (List.range (u.2.take count).length).map (fun k => configurationValues S (u.1, k))

def energyFromLists (u : (List (List ℚ) × List ℚ) × List ℚ) : ℚ :=
  (1 / 2) * dot (u.2, matrixVector (u.1.1, u.2)) + dot (u.1.2, u.2)

def spinTable (S : SpinLaw) : List (ℚ × ℚ) := (alphabet S).map (fun a => (a, S.ρ a))

def lookupWeight (S : SpinLaw) (a : ℚ) : ℚ :=
  (((spinTable S)[(spinTable S).findIdx (fun r => decide (r.1 = a))]?).getD (0, 0)).2

def baseWeightFromValues (S : SpinLaw) (xs : List ℚ) : ℚ :=
  (xs.map (lookupWeight S)).prod

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def maximumQ (xs : List ℚ) : ℚ := xs.foldl max (xs.head?.getD 0)

def tableBits (u : ℕ × ℕ) : ℕ := (4 * u.1 * u.2).size + 1
def tableCapacity (u : ℕ × ℕ) : ℕ := 2 ^ tableBits u

def sampleFiniteTable (u : (List (List ℚ) × List ℕ) × List Bool) : List ℚ :=
  (u.1.1[bucketScan (u.1.2, Word.value u.2)]?).getD []

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section

def realRound (d x : ℝ) : ℝ :=
  if x < 0 then -d * (⌊-x / d⌋₊ : ℝ) else d * (⌊x / d⌋₊ : ℝ)

def roundPoint {N : ℕ} (d : ℝ) (z : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => realRound d (z i))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp
open CritWinSpin.Implementation.EnvelopeAnalysis

def tiltApproxWeight (S : SpinLaw) (t d : ℚ) (a : {a : ℚ // a ∈ S.A}) : ℚ :=
  S.ρ a.1 * expNegativeApprox (t - t * a.1) d

def phiDerivativeApprox (S : SpinLaw) (t d : ℚ) : ℚ :=
  (∑ a : {a : ℚ // a ∈ S.A}, a.1 * tiltApproxWeight S t d a) /
    ∑ a : {a : ℚ // a ∈ S.A}, tiltApproxWeight S t d a

def positiveModifiedDerivativeApprox (S : SpinLaw) (s t d : ℚ) : ℚ :=
  min (t / s) (phiDerivativeApprox S t d)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

abbrev TiltInput := (ℚ × ℚ) × List Unit

def tiltRecords (S : SpinLaw) (u : TiltInput) : List (ℚ × ℚ) :=
  (spinTable S).map fun r =>
    (r.1, r.2 * expWithFuel ((u.1.1 - u.1.1 * r.1, u.1.2), u.2))

def phiMeanWithFuel (S : SpinLaw) (u : TiltInput) : ℚ :=
  ((tiltRecords S u).map (fun r => r.1 * r.2)).sum /
    ((tiltRecords S u).map Prod.snd).sum

def rationalMin (u : ℚ × ℚ) : ℚ := if u.1 ≤ u.2 then u.1 else u.2

def positiveModifiedWithFuel (S : SpinLaw) (u : ℚ × TiltInput) : ℚ :=
  rationalMin (u.2.1.1 / u.1, phiMeanWithFuel S u.2)

def modifiedDerivativeApprox (S : SpinLaw) (s t d : ℚ) : ℚ :=
  if t < 0 then -positiveModifiedDerivativeApprox S s (-t) d
  else positiveModifiedDerivativeApprox S s t d

def modifiedWithFuel (S : SpinLaw) (u : ℚ × TiltInput) : ℚ :=
  if u.2.1.1 < 0 then -positiveModifiedWithFuel S (u.1, ((-u.2.1.1, u.2.1.2), u.2.2))
  else positiveModifiedWithFuel S u

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

noncomputable def sqrtIter (a : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => sqrtIter a n + (a - (sqrtIter a n) ^ 2) / 2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Matrix

def sqrtStepQ {N : ℕ} (A X : Matrix (Fin N) (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  X + (1 / 2 : ℚ) • (A - X ^ 2)

def roundedMatrixSqrt {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (d : ℚ) :
    ℕ → Matrix (Fin N) (Fin N) ℚ
  | 0 => 0
  | n + 1 => Matrix.of fun i j => Compiled.clampedRound ((sqrtStepQ A (roundedMatrixSqrt A d n)) i j, d)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

abbrev MatrixCode := List (List ℚ)
abbrev RootContext := (MatrixCode × List Unit) × ℚ
abbrev RootState := RootContext × MatrixCode

def siteNumbers (xs : List Unit) : List ℕ := List.range xs.length

def matrixEntry (u : MatrixCode × (ℕ × ℕ)) : ℚ :=
  (((u.1[u.2.1]?).getD [])[u.2.2]?).getD 0

def matrixProductEntry (u : (MatrixCode × List Unit) × (ℕ × ℕ)) : ℚ :=
  ((siteNumbers u.1.2).map (fun k =>
    matrixEntry (u.1.1, (u.2.1, k)) * matrixEntry (u.1.1, (k, u.2.2)))).sum

def roundedRootRows (st : RootState) : MatrixCode :=
  (siteNumbers st.1.1.2).map fun i =>
    (siteNumbers st.1.1.2).map fun j => clampedRound
      (matrixEntry (st.2, (i, j)) +
        (matrixEntry (st.1.1.1, (i, j)) - matrixProductEntry ((st.2, st.1.1.2), (i, j))) / 2,
        st.1.2)

def roundedRootStep (st : RootState) : RootState := (st.1, roundedRootRows st)

def rootZeroRows (sites : List Unit) : MatrixCode :=
  sites.map (fun _ => sites.map (fun _ => (0 : ℚ)))

def rootCompute (u : RootContext × List Unit) : MatrixCode :=
  (u.2.foldl (fun st _ => roundedRootStep st) (u.1, rootZeroRows u.1.1.2)).2

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

abbrev DriftContext := (MatrixCode × List ℚ) × (List Unit × (ℚ × ℚ × ℚ))
abbrev DriftInput := DriftContext × (List ℚ × List Unit)

def driftArguments (u : DriftInput) : List ℚ :=
  ((matrixVector (u.1.1.1, u.2.1)).zip u.1.1.2).map (fun p => p.1 + p.2)

def driftCoefficients (S : SpinLaw) (u : DriftInput) : List ℚ :=
  (driftArguments u).map (fun t => modifiedWithFuel S
    (u.1.2.2.1, ((t, u.1.2.2.2.2), u.2.2)))

def driftTransposeProduct (S : SpinLaw) (u : DriftInput × ℕ) : ℚ :=
  ((siteNumbers u.1.1.2.1).map (fun j =>
    matrixEntry (u.1.1.1.1, (j, u.2)) * ((driftCoefficients S u.1)[j]?).getD 0)).sum

def driftWithFuel (S : SpinLaw) (u : DriftInput) : List ℚ :=
  (siteNumbers u.1.2.1).map (fun i =>
    (1 + u.1.2.2.2.1) * ((u.2.1[i]?).getD 0) - driftTransposeProduct S (u, i))

def approximateGradient {N : ℕ} (S : SpinLaw) (L : Matrix (Fin N) (Fin N) ℚ)
    (h z : Fin N → ℚ) (s a d : ℚ) : Fin N → ℚ := fun i =>
  (1 + a) * z i - ∑ j, L j i * modifiedDerivativeApprox S s (L.mulVec z j + h j) d

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section

def rationalRound (d : ℚ) (x : ℝ) : ℚ :=
  if x < 0 then -d * (⌊-x / (d : ℝ)⌋₊ : ℚ) else d * (⌊x / (d : ℝ)⌋₊ : ℚ)

def rationalProject {N : ℕ} (d : ℚ) (z : Point N) : Fin N → ℚ := fun i => rationalRound d (z i)

def rationalDrift {N : ℕ} (S : SpinLaw) (L : Matrix (Fin N) (Fin N) ℚ)
    (h : Fin N → ℚ) (s a d snap : ℚ) (z : Point N) : Point N :=
  WithLp.toLp 2 (castV (approximateGradient S L h (rationalProject snap z) s a d))

def snappedDriftWithFuel (S : SpinLaw) (u : ℚ × DriftInput) : List ℚ :=
  driftWithFuel S (u.2.1, ((u.2.2.1.map (fun x => roundTowardZero (x, u.1))), u.2.2.2))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory ProbabilityTheory

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGrid

end CritWinSpin.Implementation.GaussianGrid

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def gaussianRadius (k : ℕ) : ℕ := 16 * (k + 1)
def gaussianMeshDen (k : ℕ) : ℕ := 16384 * (k + 1) ^ 4
def gaussianGridSize (k : ℕ) : ℕ := 2 * gaussianRadius k * gaussianMeshDen k
def gaussianAccuracy (k : ℕ) : ℕ := 64 * gaussianRadius k * (k + 1)
def gaussianBits (k : ℕ) : ℕ := tableBits (gaussianGridSize k, gaussianAccuracy k)
def gaussianMesh (k : ℕ) : ℚ := 1 / (gaussianMeshDen k : ℚ)

def gaussianNode (u : ℕ × ℕ) : ℚ := -(gaussianRadius u.1 : ℚ) + (u.2 : ℚ) * gaussianMesh u.1

def unitize (xs : List Bool) : List Unit := xs.map (fun _ => ())

def boolIndices (xs : List Bool) : List ℕ := List.range xs.length

def gaussianNodes (u : ℕ × List Bool) : List ℚ :=
  (boolIndices (u.2.take (gaussianGridSize u.1))).map (fun i => gaussianNode (u.1, i))

def gaussianWeights (u : ℕ × List Bool) : List ℚ :=
  (gaussianNodes u).map (fun x => expWithFuel ((x * x / 4, gaussianMesh u.1), unitize u.2))

def gaussianCounts (u : ℕ × List Bool) : List ℕ :=
  quantizedCounts (gaussianWeights u, tableCapacity (gaussianGridSize u.1, gaussianAccuracy u.1))

def gaussianDraw (u : ℕ × List Bool) : ℚ :=
  ((gaussianNodes u)[bucketScan (gaussianCounts u, Word.value (u.2.take (gaussianBits u.1)))]?).getD 0

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic IsingLTL.BeliefProp

def sampleScalarTable (u : (List ℚ × List ℕ) × List Bool) : ℚ :=
  (u.1.1[bucketScan (u.1.2, Word.value u.2)]?).getD 0

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGridLaw

open GaussianGrid

end CritWinSpin.Implementation.GaussianGridLaw

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp ProbabilityTheory MeasureTheory
open CritWinSpin.Implementation.GaussianGrid

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory
noncomputable section

def uniformBits (bits : ℕ) : Measure (Fin bits → Bool) :=
  (PMF.uniformOfFintype (Fin bits → Bool)).toMeasure

instance uniformBits_probability (bits : ℕ) : IsProbabilityMeasure (uniformBits bits) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype (Fin bits → Bool)).toMeasure)

def bitLaw (bits : ℕ) (draw : (Fin bits → Bool) → ℝ) : Measure ℝ :=
  (uniformBits bits).map draw

instance bitLaw_probability (bits : ℕ) (draw : (Fin bits → Bool) → ℝ) :
    IsProbabilityMeasure (bitLaw bits draw) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite draw).aemeasurable

end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory ProbabilityTheory

def gaussianNoiseTail (k : ℕ) : ℕ := gaussianGridSize k + 2 * (gaussianMeshDen k) ^ 3 + 2
def gaussianNoiseBits (k : ℕ) : ℕ := gaussianBits k + gaussianNoiseTail k

noncomputable def gaussianNoiseLaw (k : ℕ) : Measure ℝ :=
  bitLaw (gaussianNoiseBits k) (fun ω => gaussianDraw (k, List.ofFn ω))

instance gaussianNoiseLaw_probability (k : ℕ) : IsProbabilityMeasure (gaussianNoiseLaw k) :=
  inferInstanceAs (IsProbabilityMeasure (bitLaw (gaussianNoiseBits k)
    (fun ω => (gaussianDraw (k, List.ofFn ω) : ℝ))))

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def bitBlock (u : (List Bool × ℕ) × ℕ) : List Bool :=
  (u.1.1.drop (u.2 * u.1.2)).take u.1.2

theorem blockIndex_lt {N B : ℕ} (i : Fin N) (j : Fin B) : i.val * B + j.val < N * B := by
  have h1 : i.val * B + j.val < (i.val + 1) * B := by nlinarith [j.isLt]
  have h2 := Nat.mul_le_mul_right B (Nat.succ_le_of_lt i.isLt)
  exact h1.trans_le h2

def blockIndex {N B : ℕ} (i : Fin N) (j : Fin B) : Fin (N * B) :=
  ⟨i.val * B + j.val, blockIndex_lt i j⟩

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def boundedRound (u : (ℚ × ℚ) × ℚ) : ℚ :=
  u.2 * clampedRound (u.1.1 / u.2, u.1.2 / u.2)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

/-- Drift data; step/noise scale and output mesh; input mesh and Gaussian precision;
    state bound and the common deterministic fuel. -/
abbrev EulerContext := DriftContext × ((ℚ × ℚ) × ((ℚ × ℕ) × (ℚ × List Unit)))
abbrev EulerState := EulerContext × (List ℚ × List Bool)

def eulerDrift (S : SpinLaw) (st : EulerState) : List ℚ :=
  snappedDriftWithFuel S (st.1.2.2.1.1,
    (st.1.1, (st.2.1, st.1.2.2.2.2)))

def eulerNoise (u : EulerState × ℕ) : ℚ :=
  gaussianDraw (u.1.1.2.2.1.2,
    bitBlock ((u.1.2.2, gaussianNoiseBits u.1.1.2.2.1.2), u.2))

def eulerRaw (S : SpinLaw) (u : EulerState × ℕ) : ℚ :=
  ((u.1.2.1[u.2]?).getD 0) - u.1.1.2.1.1 * u.1.1.2.1.1 *
    (((eulerDrift S u.1)[u.2]?).getD 0) + u.1.1.2.1.1 * eulerNoise u

def eulerRows (S : SpinLaw) (st : EulerState) : List ℚ :=
  (siteNumbers st.1.1.2.1).map (fun i =>
    boundedRound ((eulerRaw S (st, i), st.1.2.1.2), st.1.2.2.2.1))

def eulerStep (S : SpinLaw) (st : EulerState) : EulerState :=
  (st.1, (eulerRows S st,
    st.2.2.drop (st.1.1.2.1.length * gaussianNoiseBits st.1.2.2.1.2)))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation.EnvelopeAnalysis

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

structure EulerData (N : ℕ) where
  L : Matrix (Fin N) (Fin N) ℚ
  h : Fin N → ℚ
  sCap : ℚ
  a : ℚ
  dPhi : ℚ
  sigma : ℚ
  dRound : ℚ
  snap : ℚ
  bound : ℚ
  k : ℕ
  fuel : List Unit

def EulerData.context {N : ℕ} (D : EulerData N) : EulerContext :=
  (((List.ofFn (fun i => List.ofFn (D.L i)), List.ofFn D.h),
    (List.replicate N (), (D.sCap, D.a, D.dPhi))),
      ((D.sigma, D.dRound), ((D.snap, D.k), (D.bound, D.fuel))))

def EulerData.raw {N : ℕ} (D : EulerData N) (S : SpinLaw) (z : Fin N → ℚ)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (i : Fin N) : ℚ :=
  z i - D.sigma ^ 2 * approximateGradient S D.L D.h
    (fun j => roundTowardZero (z j, D.snap)) D.sCap D.a D.dPhi i +
      D.sigma * gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j)))

def EulerData.cappedNext {N : ℕ} (D : EulerData N) (S : SpinLaw) (z : Fin N → ℚ)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) : Fin N → ℚ := fun i =>
  boundedRound ((D.raw S z ω i, D.dRound), D.bound)

def EulerData.next {N : ℕ} (D : EulerData N) (S : SpinLaw) (z : Fin N → ℚ)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) : Fin N → ℚ := fun i =>
  roundTowardZero (D.raw S z ω i, D.dRound)

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
noncomputable section

def finiteOperator {X W : Type} [Fintype W] (step : X → W → X) (f : X → ℝ) (x : X) : ℝ :=
  (1 / (Fintype.card W : ℝ)) * ∑ w, f (step x w)

def finitePath {X W : Type} (step : X → W → X) (x : X) {T : ℕ} (ω : Fin T → W) : X :=
  (List.ofFn ω).foldl step x

end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section

def EulerData.realNoise {N : ℕ} (D : EulerData N)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) : Point N :=
  WithLp.toLp 2 (fun i => (gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j))) : ℝ))

def EulerData.realStep {N : ℕ} (D : EulerData N) (S : SpinLaw) (z : Point N)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) : Point N :=
  roundPoint (D.dRound : ℝ)
    (z - (D.sigma : ℝ) ^ 2 • rationalDrift S D.L D.h D.sCap D.a D.dPhi D.snap z +
      (D.sigma : ℝ) • D.realNoise ω)

def EulerData.operator {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (f : Point N → ℝ) (z : Point N) : ℝ := finiteOperator (D.realStep S) f z

def EulerData.trajectoryLaw {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (T : ℕ) (z : Fin N → ℚ) : Measure (Point N) :=
  (PMF.uniformOfFintype (Fin T → (Fin (N * gaussianNoiseBits D.k) → Bool))).toMeasure.map
    (fun ω => WithLp.toLp 2 (castV (finitePath (D.next S) z ω)))

instance EulerData.trajectoryLaw_probability {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (T : ℕ) (z : Fin N → ℚ) : IsProbabilityMeasure (D.trajectoryLaw S T z) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.ProductWeak

end CritWinSpin.Implementation.ProductWeak

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RoundedEuler

open ContractiveOperator NoiseOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

end CritWinSpin.Implementation.RoundedEuler
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.EulerNoiseOperator
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open EnvelopeGeometry ContractiveOperator

end CritWinSpin.Implementation.EulerNoiseOperator
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace CritWinSpin.Implementation.EulerAnalyticStep
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open EnvelopeGeometry ContractiveOperator LangevinBudget EulerNoiseOperator

end CritWinSpin.Implementation.EulerAnalyticStep
end

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerPrecisionArithmetic

end CritWinSpin.Implementation.EulerPrecisionArithmetic
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

open Matrix

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

abbrev ResidualInput := (MatrixCode × MatrixCode) × (List Unit × ℚ)

def rootResidualTest (u : ResidualInput) : Bool :=
  (siteNumbers u.2.1).all (fun i => (siteNumbers u.2.1).all (fun j =>
    decide (|matrixEntry (u.1.1, (i, j)) - matrixProductEntry ((u.1.2, u.2.1), (i, j))| ≤ u.2.2)))

abbrev RootTestInput := (RootContext × List Unit) × ℚ

def approximatePSDTest (u : RootTestInput) : Bool :=
  rootResidualTest ((u.1.1.1.1, rootCompute u.1), (u.1.1.1.2, u.2))

def rootTolerance (u : (List Unit × List Unit) × ℚ) : ℚ :=
  u.2 / (8 * ((u.1.1.length : ℚ) + 1) * ((u.1.2.length : ℚ) + 1) *
    (naturalProduct (u.1.2.map (fun _ => 1 + 2 * u.1.1.length)) : ℚ))

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeIntegral

open EnvelopeAnalysis

end CritWinSpin.Implementation.EnvelopeIntegral

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MeasureTheory
open CritWinSpin.Implementation.EnvelopeIntegral
noncomputable section

abbrev EnvelopeInput := ((ℚ × ℚ × ℚ) × List Unit) × List Unit

def envelopeLeft (u : ℚ × ℚ) : ℚ :=
  rationalMin ((if u.2 < 0 then -u.2 else u.2), u.1)

def envelopeMesh (u : EnvelopeInput) : ℚ :=
  (u.1.1.1 - envelopeLeft (u.1.1.1, u.1.1.2.1)) / (u.1.2.length : ℚ)

def envelopeNode (u : EnvelopeInput × ℕ) : ℚ :=
  envelopeLeft (u.1.1.1.1, u.1.1.1.2.1) + (u.2 : ℚ) * envelopeMesh u.1

def envelopeValue (S : SpinLaw) (u : EnvelopeInput × ℕ) : ℚ :=
  let v := phiMeanWithFuel S ((envelopeNode u, u.1.1.1.2.2), u.1.2) -
    envelopeNode u / u.1.1.1.1
  if 0 ≤ v then v else 0

def envelopeWithFuel (S : SpinLaw) (u : EnvelopeInput) : ℚ :=
  envelopeMesh u * ((siteNumbers u.1.2).map (fun i => envelopeValue S (u, i))).sum

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def unitProduct (u : List Unit × List Unit) : List Unit := u.1.flatMap (fun _ => u.2)

def unitPower (n : ℕ) (xs : List Unit) : List Unit :=
  match n with
  | 0 => [()]
  | k + 1 => unitProduct (unitPower k xs, xs)

def polynomialFuel (C n : ℕ) (sites : List Unit) : List Unit :=
  unitProduct (List.replicate C (), unitPower n (() :: sites))

def boundedPower (b : ℕ) (u : List Unit × ℕ) : ℕ :=
  naturalProduct ((u.1.take u.2).map (fun _ => b))

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

abbrev PreInput := MatrixCode × List Unit

def fixedScale (S : SpinLaw) : ℚ := 2 * tauQ S + 1

def preTolerance (C : ℕ) (sites : List Unit) : ℚ :=
  1 / ((C : ℚ) * ((sites.length : ℚ) + 1) ^ 3)

def preBuffer (sites : List Unit) : ℚ := 1 / (1000 * ((sites.length : ℚ) + 1))

def candidateLevel (S : SpinLaw) (C : ℕ) (u : List Unit × ℕ) : ℚ :=
  tauQ S * (1 + (u.2 : ℚ) / ((polynomialFuel C 1 u.1).length : ℚ))

def normalizedShift (S : SpinLaw) (u : PreInput × ℚ) : MatrixCode :=
  (siteNumbers u.1.2).map (fun i => (siteNumbers u.1.2).map (fun j =>
    ((if i = j then u.2 else 0) - matrixEntry (u.1.1, (i, j))) / fixedScale S))

def candidatePSD (S : SpinLaw) (C : ℕ) (u : PreInput × ℕ) : Bool :=
  let A := normalizedShift S (u.1, candidateLevel S C (u.1.2, u.2))
  let fuel := polynomialFuel (C * C) 3 u.1.2
  let e := preTolerance C u.1.2
  let d := rootTolerance ((u.1.2, fuel), e)
  approximatePSDTest ((((A, u.1.2), d), fuel), e)

def preInside (S : SpinLaw) (C : ℕ) (u : PreInput) : Bool :=
  candidatePSD S C (u, (polynomialFuel C 1 u.2).length)

def preTests (S : SpinLaw) (C : ℕ) (u : PreInput) : List Bool :=
  (siteNumbers (() :: polynomialFuel C 1 u.2)).map (fun j => candidatePSD S C (u, j))

def preSelectedLevel (S : SpinLaw) (C : ℕ) (u : PreInput) : ℚ :=
  candidateLevel S C (u.2, (preTests S C u).findIdx id) + 2 * preBuffer u.2

def preIntegralPrecision (C : ℕ) (sites : List Unit) : ℚ :=
  1 / ((C : ℚ) * ((sites.length : ℚ) + 1))

def preIntegral (S : SpinLaw) (C : ℕ) (u : PreInput) : ℚ :=
  envelopeWithFuel S (((preSelectedLevel S C u, 0, preIntegralPrecision C u.2),
    polynomialFuel C 1 u.2), polynomialFuel (C ^ 4) 3 u.2)

def preCap (S : SpinLaw) (C : ℕ) (u : PreInput) : ℕ :=
  1 + rationalFloor ((u.2.length : ℚ) * (preIntegral S C u + preBuffer u.2))

def retryCount (S : SpinLaw) (C : ℕ) (u : PreInput × ℕ) : ℕ :=
  16 * u.2 * boundedPower 4 (polynomialFuel C 1 u.1.2, preCap S C u.1)

def baseBudget (S : SpinLaw) (C : ℕ) (u : PreInput × ℕ) : ℕ :=
  C * (u.1.2.length + 1) * (u.2 * retryCount S C u + 1)

def uniformBudget (S : SpinLaw) (C : ℕ) (u : PreInput × ℕ) : ℕ := (baseBudget S C u) ^ 100

def criticalCoins (S : SpinLaw) (C : ℕ) (u : PreInput × ℕ) : ℕ := (uniformBudget S C u) ^ 10000

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Matrix

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessPSD
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled

abbrev encodedInput {N : ℕ} (J : Matrix (Fin N) (Fin N) ℚ) : PreInput :=
  (List.ofFn (fun i => List.ofFn (J i)), List.replicate N ())

end CritWinSpin.Implementation.PreprocessPSD
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessSelection
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD

end CritWinSpin.Implementation.PreprocessSelection
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessBranches
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD PreprocessSelection

end CritWinSpin.Implementation.PreprocessBranches
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessIntegral
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches

def spinErrorCoefficient (S : SpinLaw) : ℝ :=
  2 * (Fintype.card {x : ℚ // x ∈ S.A} : ℝ) / (S.ρ 1 : ℝ)

def integrationConstant (S : SpinLaw) : ℝ :=
  (fixedScale S : ℝ) ^ 2 + (fixedScale S : ℝ) + (fixedScale S : ℝ) * spinErrorCoefficient S

end CritWinSpin.Implementation.PreprocessIntegral
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerFiniteBudget
open CritWinSpin.LocalTM2.Compiled EulerAnalyticStep PreprocessIntegral

end CritWinSpin.Implementation.EulerFiniteBudget
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open scoped BigOperators NNReal
open CritWinSpin

namespace CritWinSpin.Implementation.SpinKernel

open EnvelopeAnalysis

def pointKernel {N : ℕ} (S : SpinLaw) (s : ℝ) (L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (z : EnvelopeGeometry.Point N) : Option (Config S (Fin N)) → ℝ :=
  kernelK S s L h (fun i => z i)

end CritWinSpin.Implementation.SpinKernel

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp

namespace CritWinSpin.Implementation.DensityKernelTV

variable {X A : Type*} [MeasurableSpace X] [Fintype A]

end CritWinSpin.Implementation.DensityKernelTV
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteRetry
open IsingLTL.BeliefProp

variable {A : Type} [Fintype A]

def next (r p : Option A → ℝ) : Option A → ℝ
  | none => r none * p none
  | some x => r (some x) + r none * p (some x)

def retry (r : Option A → ℝ) : ℕ → Option A → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | q + 1, z => next r (retry r q) z

def lift (p : A → ℝ) : Option A → ℝ
  | none => 0
  | some x => p x

def trial (p : A → ℝ) (a : ℝ) : Option A → ℝ
  | none => 1 - a
  | some x => a * p x

end CritWinSpin.Implementation.FiniteRetry
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeKernelTransfer
open DensityAnalysis EnvelopeGeometry ContractiveOperator

end CritWinSpin.Implementation.EnvelopeKernelTransfer
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.HubbardTrialLaw
open Matrix IsingLTL.BeliefProp

def law {N : ℕ} (S : SpinLaw) (s : ℝ) (L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (v : Option (Config S (Fin N))) : ℝ :=
  ∫ z : Fin N → ℝ, normDens (Wpot S s L h) z * kernelK S s L h z v

end CritWinSpin.Implementation.HubbardTrialLaw
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

abbrev SpinDrawInput := ((ℚ × ℕ) × List Bool) × List Unit

def spinBits (S : SpinLaw) (k : ℕ) : ℕ := tableBits ((alphabet S).length, k + 1)

def spinPrecision (C k : ℕ) : ℚ := 1 / ((C : ℚ) ^ 4 * ((k : ℚ) + 1))

def spinDrawWeights (S : SpinLaw) (C : ℕ) (u : SpinDrawInput) : List ℚ :=
  (spinTable S).map (fun r => r.2 * expWithFuel
    (((if u.1.1.1 < 0 then -u.1.1.1 else u.1.1.1) - u.1.1.1 * r.1,
      spinPrecision C u.1.1.2), u.2))

def spinDraw (S : SpinLaw) (C : ℕ) (u : SpinDrawInput) : ℚ :=
  sampleScalarTable ((alphabet S,
    quantizedCounts (spinDrawWeights S C u, tableCapacity ((alphabet S).length, u.1.1.2 + 1))),
      u.1.2.take (spinBits S u.1.1.2))

def acceptanceBits (k : ℕ) : ℕ := tableBits (2, k + 1)

def clipProbability (p : ℚ) : ℚ := if p < 0 then 0 else if 1 < p then 1 else p

def bernoulliDraw (u : (ℚ × ℕ) × List Bool) : Bool :=
  let p := clipProbability u.1.1
  decide (sampleScalarTable (([1, 0], quantizedCounts ([p, 1 - p], tableCapacity (2, u.1.2 + 1))),
    u.2.take (acceptanceBits u.1.2)) = 1)

abbrev KernelInput := ((DriftContext × ℕ) × (List ℚ × List Bool)) × List Unit

def kernelFields (u : KernelInput) : List ℚ :=
  driftArguments (u.1.1.1, (u.1.2.1, u.2))

def kernelIntegralSum (S : SpinLaw) (u : KernelInput) : ℚ :=
  ((kernelFields u).map (fun t => envelopeWithFuel S
    (((u.1.1.1.2.2.1, t, 1 / ((u.1.1.2 : ℚ) + 1)), u.2.take (u.1.1.2 + 1)), u.2))).sum

def kernelAcceptance (S : SpinLaw) (u : KernelInput) : ℚ :=
  expWithFuel ((kernelIntegralSum S u, 1 / ((u.1.1.2 : ℚ) + 1)), u.2)

def kernelSpinValues (S : SpinLaw) (C : ℕ) (u : KernelInput) : List ℚ :=
  (siteNumbers u.1.1.1.2.1).map (fun i => spinDraw S C
    (((((kernelFields u)[i]?).getD 0, u.1.1.2),
      bitBlock ((u.1.2.2.drop (acceptanceBits u.1.1.2), spinBits S u.1.1.2), i)), u.2))

def kernelOutput (S : SpinLaw) (C : ℕ) (u : KernelInput) : List Bool :=
  if bernoulliDraw ((kernelAcceptance S u, u.1.1.2), u.1.2.2.take (acceptanceBits u.1.1.2)) then
    (kernelSpinValues S C u).flatMap QAlgorithms.LocalHamiltonian.encRat else []

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

abbrev EnumerationInput := ((List (List ℚ) × List ℚ) × List Unit) × (ℕ × List Bool)
abbrev EnergyRecord := List ℚ × ℚ × ℚ

def enumerationRecords (S : SpinLaw) (u : EnumerationInput) : List EnergyRecord :=
  (enumerationValues S (u.1.2, u.2.2)).map fun xs =>
    (xs, energyFromLists (u.1.1, xs), baseWeightFromValues S xs)

def enumerationMaximum (S : SpinLaw) (u : EnumerationInput) : ℚ :=
  maximumQ ((enumerationRecords S u).map (fun r => r.2.1))

def enumerationPivotWeight (S : SpinLaw) (u : EnumerationInput) : ℚ :=
  let rs := enumerationRecords S u
  let U := enumerationMaximum S u
  ((rs[rs.findIdx (fun r => decide (r.2.1 = U))]?).getD ([], 0, 0)).2.2

def enumerationTolerance (S : SpinLaw) (u : EnumerationInput) : ℚ :=
  enumerationPivotWeight S u / (16 * (u.2.1 : ℚ) * ((enumerationRecords S u).length : ℚ))

def enumerationWeights (S : SpinLaw) (u : EnumerationInput) : List ℚ :=
  (enumerationRecords S u).map fun r =>
    r.2.2 * expWithFuel ((enumerationMaximum S u - r.2.1, enumerationTolerance S u),
      u.2.2.map (fun _ => ()))

def enumerationCounts (S : SpinLaw) (u : EnumerationInput) : List ℕ :=
  quantizedCounts (enumerationWeights S u,
    tableCapacity ((enumerationRecords S u).length, u.2.1))

def enumerationSelected (S : SpinLaw) (u : EnumerationInput) : List ℚ :=
  sampleFiniteTable (((enumerationRecords S u).map Prod.fst, enumerationCounts S u),
    u.2.2.take (tableBits ((enumerationRecords S u).length, u.2.1)))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

abbrev RationalReaderState := List Bool × List ℚ

def rationalReadStep (x : RationalReaderState × Unit) : RationalReaderState :=
  let r := rationalTotal x.1.1
  (r.2, r.1 :: x.1.2)

def readRationals (x : List Unit × List Bool) : List ℚ :=
  (x.1.foldl (fun s u => rationalReadStep (s, u)) (x.2, [])).2.reverse

def siteTokens (xs : List Bool) : List Unit :=
  (xs.take (QMCNumericRuntime.inputWidth xs)).map (fun _ => ())

def rationalSlots (xs : List Bool) : List Unit :=
  (siteTokens xs).flatMap (fun _ => siteTokens xs) ++ siteTokens xs

def parseInstTotal (xs : List Bool) : ℕ × List ℚ :=
  (QMCNumericRuntime.inputWidth xs,
    readRationals (rationalSlots xs, xs.drop (QMCNumericRuntime.inputWidth xs + 1)))

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def instanceListModel {N : ℕ} (I : Inst N) : List (List ℚ) × List ℚ :=
  (List.ofFn (fun i => List.ofFn (I.1 i)), List.ofFn I.2)

def modelFromFlat (u : List Unit × List ℚ) : List (List ℚ) × List ℚ :=
  let n := u.1.length
  ((List.range n).map (fun i => (u.2.drop (i * n)).take n), u.2.drop (n * n))

def parseModel (xs : List Bool) : (List (List ℚ) × List ℚ) × List Unit :=
  (modelFromFlat (siteTokens xs, (parseInstTotal xs).2), siteTokens xs)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

abbrev ParsedInput := ((List (List ℚ) × List ℚ) × List Unit) × ℕ

def requestParams (xs : List Bool) : ParsedInput :=
  (parseModel (requestPair xs).1, (binaryTotal (requestPair xs).2).1)

def budgetFromPowers (u : ℕ × ℕ × ℕ) : ℕ :=
  tableBits (u.1, u.2.2) + u.1 + 2 * (16 * u.2.2 * u.2.1) ^ 3 + 2

def enumerationBudget (S : SpinLaw) (p : ParsedInput) : ℕ :=
  budgetFromPowers
    (naturalProduct (p.1.2.map (fun _ => (alphabet S).length)),
      naturalProduct (p.1.2.map (fun _ => (alphabet S).length * weightDenominatorBound S)), p.2)

def rawEnumerationSelected (S : SpinLaw) (xs : List Bool) : List ℚ :=
  let r := requestPair xs
  let p := requestParams r.2
  enumerationSelected S (p.1, (p.2, r.1))

attribute [irreducible] rawEnumerationSelected

def rawEnumerationOutput (S : SpinLaw) (xs : List Bool) : List Bool :=
  (rawEnumerationSelected S xs).flatMap encRat

section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] List.flatMap
noncomputable section

end
end

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
noncomputable section

abbrev SamplerInput := ParsedInput × List Bool

def samplerPre (u : SamplerInput) : PreInput := (u.1.1.1.1, u.1.1.2)

def samplerR (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℕ :=
  uniformBudget S C (samplerPre u, u.1.2)

def samplerQuality (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℕ := (samplerR S C u) ^ 100

def samplerMesh (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℚ := 1 / (samplerQuality S C u : ℚ)

def samplerStepScale (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℚ :=
  1 / (2048 * ((samplerR S C u : ℚ) * samplerR S C u * samplerR S C u * samplerR S C u))

def samplerStepCount (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℕ :=
  16 * 2048 ^ 2 * (samplerR S C u) ^ 12

def samplerRootTarget (C : ℕ) (u : SamplerInput) : ℚ :=
  1 / ((C : ℚ) ^ 4 * (u.1.2 : ℚ) * ((u.1.1.2.length : ℚ) + 1) ^ 3)

def samplerNormalizedMatrix (C : ℕ) (u : SamplerInput) : MatrixCode :=
  u.1.1.1.1.map (fun row => row.map (fun x => x / ((C : ℚ) * C)))

def samplerRoot (C : ℕ) (u : SamplerInput) : MatrixCode :=
  let fuel := unitize u.2
  let d := rootTolerance ((u.1.1.2, fuel), samplerRootTarget C u)
  (rootCompute (((samplerNormalizedMatrix C u, u.1.1.2), d), fuel)).map
    (fun row => row.map (fun x => (C : ℚ) * x))

def samplerDriftContext (S : SpinLaw) (C : ℕ) (u : SamplerInput) : DriftContext :=
  ((samplerRoot C u, u.1.1.1.2),
    (u.1.1.2, (preSelectedLevel S C (samplerPre u),
      1 / (baseBudget S C (samplerPre u, u.1.2) : ℚ), samplerMesh S C u)))

def samplerStateBound (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℚ :=
  1 + (u.2.length : ℚ) * (2 * (C : ℚ) * C * u.1.1.2.length +
    gaussianRadius (samplerQuality S C u) + 3)

def samplerEulerContext (S : SpinLaw) (C : ℕ) (u : SamplerInput) : EulerContext :=
  (samplerDriftContext S C u,
    ((samplerStepScale S C u, samplerMesh S C u),
      ((samplerMesh S C u, samplerQuality S C u), (samplerStateBound S C u, unitize u.2))))

def samplerTrialBits (S : SpinLaw) (C : ℕ) (u : SamplerInput) : ℕ :=
  samplerStepCount S C u * u.1.1.2.length * gaussianNoiseBits (samplerQuality S C u) +
    acceptanceBits (samplerQuality S C u) + u.1.1.2.length * spinBits S (samplerQuality S C u)

def samplerTrialState (S : SpinLaw) (C : ℕ) (u : SamplerInput × ℕ) : EulerState :=
  ((unitize u.1.2).take (samplerStepCount S C u.1)).foldl (fun st _ => eulerStep S st)
    (samplerEulerContext S C u.1,
      (u.1.1.1.2.map (fun _ => (0 : ℚ)),
        bitBlock ((u.1.2, samplerTrialBits S C u.1), u.2)))

def samplerTrialOutput (S : SpinLaw) (C : ℕ) (u : SamplerInput × ℕ) : List Bool :=
  let st := samplerTrialState S C u
  kernelOutput S C (((samplerDriftContext S C u.1, samplerQuality S C u.1), st.2), unitize u.1.2)

def samplerTrialOutputs (S : SpinLaw) (C : ℕ) (u : SamplerInput) : List (List Bool) :=
  (siteNumbers ((unitize u.2).take (retryCount S C (samplerPre u, u.1.2)))).map
    (fun i => samplerTrialOutput S C (u, i))

def samplerRetryOutput (S : SpinLaw) (C : ℕ) (u : SamplerInput) : List Bool :=
  let outs := samplerTrialOutputs S C u
  (outs[outs.findIdx (fun bs => !bs.isEmpty)]?).getD []

def finalSamplerCoins (S : SpinLaw) (C : ℕ) (xs : List Bool) : ℕ :=
  let p := requestParams xs
  if p.1.2.isEmpty then 0 else
    if preInside S C (p.1.1.1, p.1.2) then criticalCoins S C ((p.1.1.1, p.1.2), p.2)
    else enumerationBudget S p

def samplerRequest (xs : List Bool) : SamplerInput :=
  (requestParams (requestPair xs).2, (requestPair xs).1)

attribute [irreducible] samplerRequest

def finalSamplerRun (S : SpinLaw) (C : ℕ) (xs : List Bool) : List Bool :=
  let u := samplerRequest xs
  if u.1.1.2.isEmpty then [] else
    if preInside S C (samplerPre u) then samplerRetryOutput S C u
    else rawEnumerationOutput S xs

attribute [irreducible] finalSamplerRun

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

def encodedSamplerInput {N : ℕ} (I : Inst N) (m : ℕ) (ω : List Bool) : SamplerInput :=
  (((instanceListModel I, List.replicate N ()), m), ω)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

def sampleReference {N : ℕ} (I : Inst N) (m F : ℕ) : SamplerInput :=
  encodedSamplerInput I m (List.replicate F false)

def sampleRootMatrix {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  let A := (1 / ((C : ℚ) * C)) • I.1
  let d := rootTolerance ((List.replicate N (), List.replicate F ()),
    1 / ((C : ℚ) ^ 4 * (m : ℚ) * ((N : ℚ) + 1) ^ 3))
  (C : ℚ) • roundedMatrixSqrt A d F

def sampleEulerData {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) : EulerData N where
  L := sampleRootMatrix C I m F
  h := I.2
  sCap := preSelectedLevel S C (samplerPre (sampleReference I m F))
  a := 1 / (baseBudget S C (samplerPre (sampleReference I m F), m) : ℚ)
  dPhi := samplerMesh S C (sampleReference I m F)
  sigma := samplerStepScale S C (sampleReference I m F)
  dRound := samplerMesh S C (sampleReference I m F)
  snap := samplerMesh S C (sampleReference I m F)
  bound := samplerStateBound S C (sampleReference I m F)
  k := samplerQuality S C (sampleReference I m F)
  fuel := List.replicate F ()

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerDataFacts
open CritWinSpin.LocalTM2.Compiled PreprocessPSD

def trials {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) : ℕ :=
  retryCount S C (encodedInput I.1,m)

def budgetBase {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) : ℕ :=
  C*(N+1)*(m*trials S C I m+1)

def radius {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) : ℕ := (budgetBase S C I m)^100

end CritWinSpin.Implementation.SamplerDataFacts
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerBudgetBounds
open PreprocessIntegral PreprocessPSD

end CritWinSpin.Implementation.SamplerBudgetBounds
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.CriticalAnalyticTrial
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled IsingLTL.BeliefProp
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral
open SamplerDataFacts DensityAnalysis EnvelopeGeometry ContractiveOperator LangevinBudget

end CritWinSpin.Implementation.CriticalAnalyticTrial
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.GibbsPerturbation

open IsingLTL.BeliefProp CritWinSpin.LocalTM2

end CritWinSpin.Implementation.GibbsPerturbation
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerMatrixCertificate
open Matrix IsingLTL.BeliefProp
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches

abbrev rootTarget (C N m : ℕ) : ℚ := 1 / ((C : ℚ)^4 * m * ((N : ℚ)+1)^3)
abbrev rootError (C N m : ℕ) : ℝ := 1 / ((C : ℝ)^2 * m * ((N : ℝ)+1)^3)
abbrev covariance {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  castM (sampleRootMatrix C I m F) * (castM (sampleRootMatrix C I m F)).transpose

end CritWinSpin.LocalTM2.Compiled.SamplerMatrixCertificate
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessCap
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral

end CritWinSpin.Implementation.PreprocessCap
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelPrecisionBudget
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral

def error (S : SpinLaw) (C N k : ℕ) (s : ℝ) : ℝ :=
  (1+(N:ℝ)*(s^2+s+spinErrorCoefficient S*s))/((k:ℝ)+1) +
    4/(2:ℝ)^(acceptanceBits k) +
    (N:ℝ)*((alphabet S).length*(spinPrecision C k:ℝ)/(S.ρ 1:ℝ)+
      (alphabet S).length/(2:ℝ)^(spinBits S k))

end CritWinSpin.Implementation.KernelPrecisionBudget
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness
open Classical IsingLTL.BeliefProp MeasureTheory
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteRetry
open IsingLTL.BeliefProp
variable {A : Type} [Fintype A]

def firstSome : {q : ℕ} → (Fin q → Option A) → Option A
  | 0, _ => none
  | q + 1, xs => match xs 0 with
    | none => firstSome (fun i : Fin q => xs i.succ)
    | some x => some x

end CritWinSpin.Implementation.FiniteRetry
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RetryPacketDecoding
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

end CritWinSpin.Implementation.RetryPacketDecoding
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches

end CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

def trialOnBlock (S : SpinLaw) (C : ℕ) (p : ParsedInput) (F : ℕ) (bits : List Bool) : List Bool :=
  let ref : SamplerInput := (p, List.replicate F false)
  let st := ((unitize ref.2).take (samplerStepCount S C ref)).foldl (fun st _ => eulerStep S st)
    (samplerEulerContext S C ref, (p.1.2.map (fun _ => (0 : ℚ)), bits))
  kernelOutput S C (((samplerDriftContext S C ref, samplerQuality S C ref), st.2), unitize ref.2)

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation PreprocessPSD SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp CritWinSpin.Implementation.EnvelopeAnalysis
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical
noncomputable section

def EulerData.kernelInput {N : ℕ} (D : EulerData N) (z : Fin N → ℚ) (bits : List Bool) : KernelInput :=
  (((D.context.1, D.k), (List.ofFn z, bits)), D.fuel)

def EulerData.fields {N : ℕ} (D : EulerData N) (z : Fin N → ℚ) (i : Fin N) : ℚ :=
  D.L.mulVec z i + D.h i

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

def EulerData.trialCode {N : ℕ} (D : EulerData N) (S : SpinLaw) (C T : ℕ) (bits : List Bool) : List Bool :=
  let st := (List.replicate T ()).foldl (fun st _ => eulerStep S st)
    (D.context, (List.ofFn (fun _ : Fin N => (0 : ℚ)), bits))
  kernelOutput S C (((D.context.1,D.k),st.2),D.fuel)

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.FiniteDraw
open IsingLTL.BeliefProp Classical
noncomputable section

def law {W A : Type} [Fintype W] [Fintype A] (draw : W → A) (a : A) : ℝ :=
  (1 / (Fintype.card W : ℝ)) * ∑ w, if draw w = a then (1 : ℝ) else 0

end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
noncomputable section
open IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteKernelTV
variable {A : Type} [Fintype A]

def productLaw {n : ℕ} (p : Fin n → A → ℝ) (xs : Fin n → A) : ℝ := ∏ i, p i (xs i)

end CritWinSpin.Implementation.FiniteKernelTV
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelAcceptance
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral

end CritWinSpin.Implementation.KernelAcceptance
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
noncomputable section

def kernelWordLaw {N : ℕ} (S : SpinLaw) (C : ℕ) (D : EulerData N) (z : Fin N → ℚ) :
    Option (Config S (Fin N)) → ℝ :=
  FiniteDraw.law (fun w : Fin (acceptanceBits D.k + N * spinBits S D.k) → Bool =>
    decConfig S N (kernelOutput S C (D.kernelInput z (List.ofFn w))))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.FiniteDraw
open Classical IsingLTL.BeliefProp
noncomputable section

def mean {W : Type} [Fintype W] (f : W → ℝ) : ℝ :=
  (1 / (Fintype.card W : ℝ)) * ∑ w, f w

end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled.GenericPacketLaw

end CritWinSpin.LocalTM2.Compiled.GenericPacketLaw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
noncomputable section
attribute [local irreducible] EulerData.trialCode kernelOutput

def trialWordLaw {N : ℕ} (S : SpinLaw) (C : ℕ) (D : EulerData N) (T : ℕ) :
    Option (Config S (Fin N)) → ℝ :=
  FiniteDraw.law (fun w : Fin (T * (N * gaussianNoiseBits D.k) +
    (acceptanceBits D.k + N * spinBits S D.k)) → Bool =>
      decConfig S N (D.trialCode S C T (List.ofFn w)))

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
open CritWinSpin.Implementation
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
open CritWinSpin.Implementation
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Classical
noncomputable section

namespace FiniteDraw

end FiniteDraw

namespace Compiled

section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false

end

end Compiled
end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD SamplerDataFacts
noncomputable section

section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] CritWinSpin.LocalTM2.Compiled.kernelAcceptance CritWinSpin.LocalTM2.Compiled.samplerTrialOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutputs CritWinSpin.LocalTM2.Compiled.samplerTrialState CritWinSpin.LocalTM2.Compiled.samplerEulerContext CritWinSpin.LocalTM2.Compiled.samplerDriftContext CritWinSpin.LocalTM2.Compiled.samplerRoot

end

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness
open Classical IsingLTL.BeliefProp MeasureTheory
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.EnumerationProof
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp
open scoped BigOperators
noncomputable section

end
end CritWinSpin.LocalTM2.Compiled.EnumerationProof

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC IsingLTL.BeliefProp

end CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RuntimeArithmetic

end CritWinSpin.Implementation.RuntimeArithmetic
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessCriticalLevel
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches

end CritWinSpin.Implementation.PreprocessCriticalLevel
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.CriticalCapBudget
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessCriticalLevel PreprocessIntegral PreprocessCap

end CritWinSpin.Implementation.CriticalCapBudget
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerRuntime
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessBranches PreprocessIntegral PreprocessCap RuntimeArithmetic

end CritWinSpin.Implementation.SamplerRuntime
end

end

section

set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.SamplerConstantChoice
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled

end CritWinSpin.Implementation.SamplerConstantChoice
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory IsingLTL.BeliefProp CritWinSpin
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral

end

end


