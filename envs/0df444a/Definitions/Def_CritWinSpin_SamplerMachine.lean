-- Prove2me | Definitions.Def_CritWinSpin_SamplerMachine
-- name    : CritWinSpin_SamplerMachine
-- status  : Definition
-- author  : @Maxliu
-- created : 2026-11-17T18:20:46.268456+00:00
-- url     : https://prove2.me/theorems/b27abd29-b7cb-40aa-bfe9-a7dc6b2e2803
-- title:
--   Compiled finite sampler used in Theorem 4.4
-- statement:
--   This construction compiles the finite sampler of Theorem 4.4 into one randomized $\mathrm{TM2}$ machine for each fixed spin law and numerical scale. The random-bit budget, preprocessing branch, rounded Euler steps, finite acceptance and spin draws, and enumeration fallback are the numerical functions fixed by the shared sampler data.
--
--   The construction includes the polynomial program certificates and encoding interfaces needed to instantiate the machine. The random-bit count and machine output agree with the corresponding numerical functions. Its approximation error and final critical-window running-time estimate are proved in separate lemmas.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 4.4, p.17, equation (24). Concrete TM2 implementation of the finite sampler.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_Wpot
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_SamplerAnalyticData
import Definitions.Def_CritWinSpin_SamplerNumericalData

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

def quoteBinary : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [true, b])
  finish _ := [false, false]

theorem quoteBinary_run (xs : List Bool) :
    quoteBinary.run () xs = xs.flatMap (fun b => [true, b]) ++ [false, false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true, b] ++ quoteBinary.run () xs = _
      rw [ih]
      simp

noncomputable def encBinProgram : PolyProgram Nat.bits id encBin :=
  quoteBinary.program.of_word (fun n => by
    simpa only [quoteBinary, encBin, id_eq] using quoteBinary_run n.bits)

theorem tupleCode_pair_length (xs ys : List Bool) :
    (tupleCode [xs, ys]).length = 2 * (xs.length + ys.length) + 4 := by
  have hlen (zs : List Bool) : (zs.flatMap (fun b => [b, b])).length = 2 * zs.length := by
    induction zs with
    | nil => simp
    | cons b zs ih => simp [ih]; omega
  simp [tupleCode, hlen]
  omega

noncomputable def programRandMachine {f : List Bool → List Bool} {c : List Bool → ℕ}
    (P : PolyProgram id id f) (C : PolyProgram id Nat.bits c) : RandMachine where
  tm := P.stock.toTM2ComputableAux
  run := f
  coins := c
  time x := max (P.time.eval (2 * (c x + x.length) + 4))
    (max ((C.comp encBinProgram).time.eval x.length) (c x))
  halts := by
    intro x ω hω
    have h := P.outputs (tupleCode [ω, x])
    dsimp only [id_eq] at h
    have hlen : (tupleCode [ω, x]).length = 2 * (c x + x.length) + 4 := by
      rw [tupleCode_pair_length, hω]
    rw [hlen] at h
    have hh : TM2OutputsInTime P.machine.tm (tupleCode [ω, x])
        (some (f (tupleCode [ω, x])))
        (max (P.time.eval (2 * (c x + x.length) + 4))
          (max ((C.comp encBinProgram).time.eval x.length) (c x))) :=
      ⟨h.toEvalsTo, h.steps_le_m.trans (le_max_left _ _)⟩
    exact ⟨by simpa only [PolyProgram.stock, Equiv.refl, List.map_id_fun, id_eq] using hh⟩
  coinTm := (C.comp encBinProgram).stock.toTM2ComputableAux
  coins_computed := by
    intro x
    have h := (C.comp encBinProgram).outputs x
    dsimp only [id_eq, Function.comp_apply] at h
    have hh : TM2OutputsInTime (C.comp encBinProgram).machine.tm x (some (encBin (c x)))
        (max (P.time.eval (2 * (c x + x.length) + 4))
          (max ((C.comp encBinProgram).time.eval x.length) (c x))) :=
      ⟨h.toEvalsTo, h.steps_le_m.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    exact ⟨by simpa only [PolyProgram.stock, Equiv.refl, List.map_id_fun, id_eq] using hh⟩
  coins_le := by intro x; exact (le_max_right _ _).trans (le_max_right _ _)

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

inductive BinaryPhase | tag | value | skip | copy deriving DecidableEq
instance : Fintype BinaryPhase := ⟨{.tag, .value, .skip, .copy}, by intro p; cases p <;> simp⟩

def binaryParser : Transducer where
  Q := BinaryPhase
  initial := .tag
  next q b := match q with
    | .tag => if b then (.value, []) else (.skip, [false])
    | .value => (.tag, [true, b])
    | .skip => (.copy, [])
    | .copy => (.copy, [b])
  finish q := match q with
    | .tag | .value => [false]
    | .skip | .copy => []

theorem binaryParser_copy (xs : List Bool) : binaryParser.run .copy xs = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b :: binaryParser.run .copy xs = b :: xs; rw [ih]

theorem binaryParser_run (xs : List Bool) :
    binaryParser.run .tag xs = encodePair id id (binaryWords xs) := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> rfl
  | cons_cons a b xs ih =>
      cases a with
      | false =>
          change false :: binaryParser.run .copy xs = false :: xs
          rw [binaryParser_copy]
      | true =>
          change [true, b] ++ binaryParser.run .tag xs =
            [true, b] ++ encodePair id id (binaryWords xs)
          rw [ih]

noncomputable def binaryWordsProgram : PolyProgram id (encodePair id id) binaryWords :=
  binaryParser.program.of_word binaryParser_run

noncomputable def binaryProgram : PolyProgram id (encodePair Nat.bits id) binaryTotal :=
  (binaryWordsProgram.comp (PolyProgram.toBits.thread id)).congr _ (fun _ => rfl)

@[fun_prop] theorem binaryTotal_poly : Poly binaryTotal :=
  ⟨((BooleanLists.unpackProgram.comp binaryProgram).comp
      (BooleanLists.packProgram.second Nat.bits)).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem integerTotal_poly : Poly integerTotal := by
  unfold integerTotal
  fun_prop

@[fun_prop] theorem rationalTotal_poly : Poly rationalTotal := by
  unfold rationalTotal
  fun_prop

noncomputable def rationalProgram :
    PolyProgram id (encodePair Ratio.encode id) rationalTotal :=
  ((BooleanLists.packProgram.comp (Poly.program rationalTotal_poly)).comp
    (BooleanLists.unpackProgram.second Ratio.encode)).congr _ (fun _ => rfl)

noncomputable def encIntProgram : PolyProgram Signed.encode id encInt :=
  (((PolyProgram.intSign.fanout (PolyProgram.intAbs.comp encBinProgram)).comp
    PolyProgram.cons)).congr _ (fun z => by
      by_cases hz : z < 0 <;> simp [encInt, Signed.sign, hz])

noncomputable def encRatProgram : PolyProgram Ratio.encode id encRat :=
  (((PolyProgram.ratNum.comp encIntProgram).fanout
      (PolyProgram.ratDen.comp encBinProgram)).comp PolyProgram.append).congr _ (fun _ => rfl)

noncomputable def encRatsProgram :
    PolyProgram (encodeList Ratio.encode) id (fun qs : List ℚ => qs.flatMap encRat) :=
  (((encRatProgram.comp BooleanLists.packProgram).listFlatMap 0 false).comp
    BooleanLists.unpackProgram).congr _ (fun _ => rfl)

def tupleParser : Transducer where
  Q := Option Bool ⊕ Unit
  initial := .inl none
  next q b := match q with
    | .inl none => (.inl (some b), [])
    | .inl (some a) => if a = b then (.inl none, [true, a]) else (.inr (), [false])
    | .inr _ => (.inr (), [b])
  finish q := match q with
    | .inl _ => [false]
    | .inr _ => []

theorem tupleParser_copy (xs : List Bool) : tupleParser.run (.inr ()) xs = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b :: tupleParser.run (.inr ()) xs = b :: xs; rw [ih]

theorem tupleParser_run (xs : List Bool) :
    tupleParser.run (.inl none) xs = encodePair id id (tupleWords xs) := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton b => rfl
  | cons_cons a b xs ih =>
      cases a <;> cases b
      · change [true, false] ++ tupleParser.run (.inl none) xs =
          [true, false] ++ encodePair id id (tupleWords xs)
        rw [ih]
      · change false :: tupleParser.run (.inr ()) xs = false :: xs
        rw [tupleParser_copy]
      · change false :: tupleParser.run (.inr ()) xs = false :: xs
        rw [tupleParser_copy]
      · change [true, true] ++ tupleParser.run (.inl none) xs =
          [true, true] ++ encodePair id id (tupleWords xs)
        rw [ih]

noncomputable def tupleWordsProgram : PolyProgram id (encodePair id id) tupleWords :=
  tupleParser.program.of_word tupleParser_run

noncomputable def requestPairProgram : PolyProgram id (encodePair id id) requestPair :=
  (tupleWordsProgram.comp ((PolyProgram.identity id).product
    (tupleWordsProgram.comp (PolyProgram.fst id id)))).congr _ (fun _ => rfl)

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

@[fun_prop] theorem rationalSum_poly : Poly (List.sum : List ℚ → ℚ) :=
  ⟨PolyProgram.ratSum⟩

@[fun_prop] theorem dot_poly : Poly dot := by
  unfold dot
  fun_prop

@[fun_prop] theorem matrixVector_poly : Poly matrixVector := by
  unfold matrixVector
  fun_prop

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

@[fun_prop] theorem ratNum_poly : Poly Rat.num := ⟨PolyProgram.ratNum⟩
@[fun_prop] theorem ratDen_poly : Poly Rat.den := ⟨PolyProgram.ratDen⟩
@[fun_prop] theorem intAbs_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩
@[fun_prop] theorem natDiv_poly : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩

@[fun_prop] theorem rationalFloor_poly : Poly rationalFloor := by
  unfold rationalFloor
  fun_prop

@[fun_prop] theorem naturalSum_poly : Poly naturalSum := by
  unfold naturalSum
  fun_prop

@[fun_prop] theorem normalizedRationals_poly : Poly normalizedRationals := by
  unfold normalizedRationals
  fun_prop

@[fun_prop] theorem quantizedCounts_poly : Poly quantizedCounts := by
  unfold quantizedCounts
  fun_prop

@[fun_prop] theorem bucketStep_poly : Poly bucketStep := by
  unfold bucketStep
  fun_prop

def bucketEncoding : BucketState → List Bool := encodePair Nat.bits (encodePair Nat.bits encodeBool)

theorem bucketEncoding_length (s : BucketState) :
    (bucketEncoding s).length = 2 * s.1.bits.length + 2 * s.2.1.bits.length + 3 := by
  simp only [bucketEncoding, encodePair_length, encodeBool, List.length_singleton]
  omega

theorem bucketStep_size (s : BucketState) (c : ℕ) :
    (bucketEncoding (bucketStep (s, c))).length ≤
      (bucketEncoding s).length + 4 * (2 * c.bits.length + 1) := by
  cases hd : s.2.2 with
  | true => simp [bucketStep, hd]
  | false =>
      by_cases hc : s.2.1 < c
      · simp [bucketStep, hd, hc, bucketEncoding_length]
      · simp only [bucketStep, hd, Bool.false_eq_true, ite_false, hc, bucketEncoding_length]
        have ht := NatBinary.length_mono (Nat.sub_le s.2.1 c)
        have hi := NatBinary.add_length s.1 1
        have hone : (1 : ℕ).bits.length = 1 := rfl
        rw [hone] at hi
        have hm : max s.1.bits.length 1 ≤ s.1.bits.length + 1 := by omega
        omega

noncomputable def bucketFoldProgram :
    PolyProgram (encodePair (encodeList Nat.bits) bucketEncoding) bucketEncoding
      (fun x : List ℕ × BucketState => x.1.foldl (fun s c => bucketStep (s, c)) x.2) :=
  (Poly.program bucketStep_poly).listFoldLinear 0 4 bucketStep_size

@[fun_prop] theorem bucketScan_poly : Poly bucketScan := by
  have hstart : Poly (fun x : List ℕ × ℕ => (x.1, (0, x.2, false))) := by fun_prop
  have hfold : Poly (fun x : List ℕ × ℕ =>
      x.1.foldl (fun s c => bucketStep (s, c)) (0, x.2, false)) :=
    Poly.comp (Poly.of_program bucketFoldProgram) hstart
  change Poly (fun x : List ℕ × ℕ =>
    (x.1.foldl (fun s c => bucketStep (s, c)) (0, x.2, false)).1)
  exact Poly.comp (f := (Prod.fst : BucketState → ℕ)) Poly.fst hfold
    (g := fun x : List ℕ × ℕ => x.1.foldl (fun s c => bucketStep (s, c)) (0, x.2, false))

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem roundTowardZero_poly : Poly roundTowardZero := by
  unfold roundTowardZero
  fun_prop

@[fun_prop] theorem clampTwo_poly : Poly clampTwo := by unfold clampTwo; fun_prop

@[fun_prop] theorem clampedRound_poly : Poly clampedRound := by unfold clampedRound; fun_prop

theorem clampTwo_bounds (x : ℚ) : -2 ≤ clampTwo x ∧ clampTwo x ≤ 2 := by
  unfold clampTwo
  split_ifs <;> constructor <;> linarith

theorem roundTowardZero_den (x d : ℚ) : (roundTowardZero (x, d)).den ≤ d.den := by
  unfold roundTowardZero
  split_ifs <;> simp only [Rat.den_mul, Rat.den_neg_eq_den, Rat.den_natCast, mul_one]
  all_goals exact Nat.div_le_self _ _

theorem clampedRound_den (x d : ℚ) : (clampedRound (x, d)).den ≤ d.den := by
  dsimp only [clampedRound, clampTwo]
  split_ifs
  · norm_num
    exact d.den_pos
  · norm_num
    exact d.den_pos
  · exact roundTowardZero_den x d

theorem clampedRound_height (x d : ℚ) :
    HasHeight (clampedRound (x, d)) ((Ratio.encode d).length + 1) := by
  let v := clampedRound (x, d)
  have hv : |v| ≤ 2 := abs_le.mpr (clampTwo_bounds (roundTowardZero (x, d)))
  have hd := clampedRound_den x d
  have hden0 : (0 : ℚ) < v.den := by exact_mod_cast v.den_pos
  have hnum : |(v.num : ℚ)| ≤ 2 * d.den := by
    have he : (v.num : ℚ) = v * v.den := (div_eq_iff hden0.ne').mp v.num_div_den
    rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ v.den)]
    have hh := mul_le_mul_of_nonneg_right hv (by positivity : (0 : ℚ) ≤ v.den)
    have hd' : (v.den : ℚ) ≤ d.den := by exact_mod_cast hd
    nlinarith
  have hnumZ : |v.num| ≤ 2 * (d.den : ℤ) := by exact_mod_cast hnum
  have hheight := (Ratio.height_length d).2
  constructor
  · change |v.num| ≤ _
    rw [pow_succ]
    nlinarith
  · have hh : (v.den : ℤ) ≤ d.den := by exact_mod_cast hd
    change (v.den : ℤ) ≤ _
    apply (hh.trans hheight).trans
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)

theorem clampedRound_size (x d : ℚ) :
    (Ratio.encode (clampedRound (x, d))).length ≤ 3 * (Ratio.encode d).length + 13 := by
  have hh := Ratio.length_height (clampedRound_height x d)
  omega

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem take_poly_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {xs : α → List β} {n : α → ℕ} (hxs : Poly xs) (hn : Poly n) :
    Poly (fun a => (xs a).take (n a)) :=
  Poly.comp QMCNumericRuntime.parser_take_poly (Poly.pair hxs hn)

@[fun_prop] theorem drop_poly_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {xs : α → List β} {n : α → ℕ} (hxs : Poly xs) (hn : Poly n) :
    Poly (fun a => (xs a).drop (n a)) :=
  Poly.comp QMCNumericRuntime.parser_drop_poly (Poly.pair hxs hn)

@[fun_prop] theorem map_const_poly_comp {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    [Inhabited β] [Inhabited γ] {xs : α → List β} {c : α → γ}
    (hxs : Poly xs) (hc : Poly c) :
    Poly (fun a => (xs a).map (fun _ : β => c a)) :=
  Poly.list_map (f := fun a _ => c a) (as := xs) (Poly.comp hc Poly.fst) hxs

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem rationalProd_poly : Poly (List.prod : List ℚ → ℚ) := ⟨PolyProgram.ratProd⟩

@[fun_prop] theorem exponentialTerms_poly : Poly exponentialTerms := by
  unfold exponentialTerms
  simp only [pow_two]
  fun_prop

@[fun_prop] theorem expWithFuel_poly : Poly expWithFuel := by
  unfold expWithFuel
  dsimp only
  have hmap : Poly (fun u : (ℚ × ℚ) × List Unit =>
      (u.2.take (exponentialTerms u.1)).map
        (fun _ : Unit => 1 + u.1.1 / (exponentialTerms u.1 : ℚ))) := by
    apply Poly.list_map
    · change Poly (fun v : ((ℚ × ℚ) × List Unit) × Unit =>
        1 + v.1.1.1 / (exponentialTerms v.1.1 : ℚ))
      fun_prop
    · fun_prop
  apply Poly.ite_prop (by fun_prop) (by fun_prop)
  have hinv : Poly (fun q : ℚ => 1 / q) := by fun_prop
  exact Poly.comp hinv (Poly.comp rationalProd_poly hmap)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

@[fun_prop] theorem natMod_poly : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩

@[fun_prop] theorem naturalProduct_poly : Poly naturalProduct := by
  unfold naturalProduct
  fun_prop

@[fun_prop] theorem baseDigits_poly : Poly baseDigits := by
  unfold baseDigits
  have hp : Poly (fun v : ((ℕ × ℕ) × List Unit) × ℕ =>
      naturalProduct ((v.1.2.take v.2).map (fun _ : Unit => v.1.1.1))) :=
    Poly.comp naturalProduct_poly (map_const_poly_comp (by fun_prop) (by fun_prop))
  have hd : Poly (fun v : ((ℕ × ℕ) × List Unit) × ℕ =>
      v.1.1.2 / naturalProduct ((v.1.2.take v.2).map (fun _ : Unit => v.1.1.1))) :=
    Poly.comp natDiv_poly (Poly.pair (by fun_prop) hp)
  have hm : Poly (fun v : ((ℕ × ℕ) × List Unit) × ℕ =>
      (v.1.1.2 / naturalProduct ((v.1.2.take v.2).map (fun _ : Unit => v.1.1.1))) % v.1.1.1) :=
    Poly.comp natMod_poly (Poly.pair hd (by fun_prop))
  exact Poly.list_map (f := fun (u : (ℕ × ℕ) × List Unit) (i : ℕ) =>
      (u.1.2 / naturalProduct ((u.2.take i).map (fun _ : Unit => u.1.1))) % u.1.1)
    (as := fun u : (ℕ × ℕ) × List Unit => List.range u.2.length) hm
    (Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun u : (ℕ × ℕ) × List Unit => u.2) Poly.list_indices (by fun_prop))

@[fun_prop] theorem configurationValues_poly (S : SpinLaw) : Poly (configurationValues S) := by
  unfold configurationValues
  fun_prop

@[fun_prop] theorem enumerationValues_poly (S : SpinLaw) : Poly (enumerationValues S) := by
  unfold enumerationValues
  dsimp only
  have hc : Poly (fun u : List Unit × List Bool =>
      naturalProduct (u.1.map (fun _ : Unit => (alphabet S).length))) :=
    Poly.comp naturalProduct_poly (map_const_poly_comp (by fun_prop) (by fun_prop))
  have ht : Poly (fun u : List Unit × List Bool =>
      u.2.take (naturalProduct (u.1.map (fun _ : Unit => (alphabet S).length)))) :=
    take_poly_comp (by fun_prop) hc
  have hi : Poly (fun u : List Unit × List Bool =>
      List.range (u.2.take (naturalProduct (u.1.map (fun _ : Unit => (alphabet S).length)))).length) :=
    Poly.comp (f := fun xs : List Bool => List.range xs.length)
      (g := fun u : List Unit × List Bool =>
        u.2.take (naturalProduct (u.1.map (fun _ : Unit => (alphabet S).length)))) Poly.list_indices ht
  exact Poly.list_map (f := fun (u : List Unit × List Bool) (k : ℕ) => configurationValues S (u.1, k))
    (as := fun u : List Unit × List Bool => List.range (u.2.take (naturalProduct
      (u.1.map (fun _ : Unit => (alphabet S).length)))).length)
    (Poly.comp (configurationValues_poly S) (by fun_prop)) hi

@[fun_prop] theorem energyFromLists_poly : Poly energyFromLists := by
  unfold energyFromLists
  fun_prop

@[fun_prop] theorem lookupWeight_poly (S : SpinLaw) : Poly (lookupWeight S) := by
  unfold lookupWeight
  fun_prop

@[fun_prop] theorem baseWeightFromValues_poly (S : SpinLaw) : Poly (baseWeightFromValues S) := by
  unfold baseWeightFromValues
  fun_prop

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

@[fun_prop] theorem ratMax_poly : Poly (fun x : ℚ × ℚ => max x.1 x.2) := by
  simpa only [max_def] using
    (by fun_prop : Poly (fun x : ℚ × ℚ => if x.1 ≤ x.2 then x.2 else x.1))

noncomputable def maxFoldProgram :
    PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode) Ratio.encode
      (fun x : List ℚ × ℚ => x.1.foldl max x.2) :=
  (Poly.program ratMax_poly).listFoldLinear 0 1 (by
    intro b a
    by_cases hba : b ≤ a <;> simp [max_def, hba] <;> omega)

@[fun_prop] theorem maximumQ_poly : Poly maximumQ := by
  have hs : Poly (fun xs : List ℚ => (xs, xs.head?.getD 0)) := by fun_prop
  exact Poly.comp (f := fun x : List ℚ × ℚ => x.1.foldl max x.2)
    (g := fun xs : List ℚ => (xs, xs.head?.getD 0)) (Poly.of_program maxFoldProgram) hs

theorem bits_power_two (n : ℕ) : (2 ^ n).bits = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Nat.bit0_bits _ (by positivity), ih]
      rfl

def capacityTransducer : Transducer where
  Q := Unit
  initial := ()
  next _ _ := ((), [false])
  finish _ := [false, true]

theorem capacityTransducer_run (xs : List Bool) :
    capacityTransducer.run () xs = List.replicate (xs.length + 1) false ++ [true] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change false :: capacityTransducer.run () xs = _
      rw [ih]
      rfl

noncomputable def capacityProgram : PolyProgram Nat.bits Nat.bits (fun n : ℕ => 2 ^ (n.size + 1)) :=
  capacityTransducer.program.of_word (fun n => by
    change capacityTransducer.run () n.bits = (2 ^ (n.size + 1)).bits
    rw [capacityTransducer_run, bits_power_two]
    simp only [Nat.size_eq_bits_len])

@[fun_prop] theorem capacity_poly : Poly (fun n : ℕ => 2 ^ (n.size + 1)) := ⟨capacityProgram⟩
@[fun_prop] theorem natSize_poly : Poly Nat.size := ⟨PolyProgram.natSize⟩

@[fun_prop] theorem tableBits_poly : Poly tableBits := by unfold tableBits; fun_prop
@[fun_prop] theorem tableCapacity_poly : Poly tableCapacity := by
  unfold tableCapacity tableBits
  exact Poly.comp (f := fun n : ℕ => 2 ^ (n.size + 1))
    (g := fun u : ℕ × ℕ => 4 * u.1 * u.2) capacity_poly (by fun_prop)

@[fun_prop] theorem wordValue_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩

@[fun_prop] theorem sampleFiniteTable_poly : Poly sampleFiniteTable := by
  unfold sampleFiniteTable
  fun_prop

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

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

@[fun_prop] theorem tiltRecords_poly (S : SpinLaw) : Poly (tiltRecords S) := by
  unfold tiltRecords
  fun_prop

@[fun_prop] theorem phiMeanWithFuel_poly (S : SpinLaw) : Poly (phiMeanWithFuel S) := by
  unfold phiMeanWithFuel
  fun_prop

@[fun_prop] theorem rationalMin_poly : Poly rationalMin := by
  unfold rationalMin
  fun_prop

@[fun_prop] theorem positiveModifiedWithFuel_poly (S : SpinLaw) : Poly (positiveModifiedWithFuel S) := by
  unfold positiveModifiedWithFuel
  fun_prop

@[fun_prop] theorem modifiedWithFuel_poly (S : SpinLaw) : Poly (modifiedWithFuel S) := by
  unfold modifiedWithFuel
  fun_prop

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

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

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem siteNumbers_poly : Poly siteNumbers := Poly.list_indices

@[fun_prop] theorem matrixEntry_poly : Poly matrixEntry := by unfold matrixEntry; fun_prop

@[fun_prop] theorem matrixProductEntry_poly : Poly matrixProductEntry := by
  unfold matrixProductEntry
  fun_prop

@[fun_prop] theorem roundedRootRows_poly : Poly roundedRootRows := by
  unfold roundedRootRows
  fun_prop

@[fun_prop] theorem roundedRootStep_poly : Poly roundedRootStep := by
  unfold roundedRootStep
  fun_prop

def matrixEncoding : MatrixCode → List Bool := encodeList (encodeList Ratio.encode)
def rootContextEncoding : RootContext → List Bool :=
  encodePair (encodePair matrixEncoding (encodeList (fun _ : Unit => []))) Ratio.encode
def rootStateEncoding : RootState → List Bool := encodePair rootContextEncoding matrixEncoding

theorem roundedRootRows_size (st : RootState) :
    (matrixEncoding (roundedRootRows st)).length ≤
      st.1.1.2.length * (2 * (st.1.1.2.length * (2 * (3 * (Ratio.encode st.1.2).length + 13) + 1)) + 1) := by
  let n := st.1.1.2.length
  let B := 3 * (Ratio.encode st.1.2).length + 13
  have hrow (i : ℕ) : (encodeList Ratio.encode
      ((siteNumbers st.1.1.2).map fun j => clampedRound
        (matrixEntry (st.2, (i, j)) +
          (matrixEntry (st.1.1.1, (i, j)) - matrixProductEntry ((st.2, st.1.1.2), (i, j))) / 2,
          st.1.2))).length ≤ n * (2 * B + 1) := by
    have hh := EncodedList.length_bound Ratio.encode
      ((siteNumbers st.1.1.2).map fun j => clampedRound
        (matrixEntry (st.2, (i, j)) +
          (matrixEntry (st.1.1.1, (i, j)) - matrixProductEntry ((st.2, st.1.1.2), (i, j))) / 2,
          st.1.2)) B (by
        intro x hx
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
        exact clampedRound_size _ _)
    simpa only [List.length_map, siteNumbers, List.length_range] using hh
  have hh := EncodedList.length_bound (encodeList Ratio.encode) (roundedRootRows st)
    (n * (2 * B + 1)) (by
      intro row hmem
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
      exact hrow i)
  simpa only [matrixEncoding, roundedRootRows, List.length_map, siteNumbers, List.length_range] using hh

theorem rootContext_component_bounds (c : RootContext) :
    c.1.2.length ≤ (rootContextEncoding c).length ∧
      (Ratio.encode c.2).length ≤ (rootContextEncoding c).length := by
  have hu := EncodedList.length_le (fun _ : Unit => []) c.1.2
  simp only [rootContextEncoding, encodePair_length]
  omega

theorem roundedRootStep_size (st : RootState) (L : ℕ)
    (hctx : (rootContextEncoding st.1).length ≤ L) :
    (rootStateEncoding (roundedRootStep st)).length ≤ 1000 * (L + 1) ^ 3 := by
  obtain ⟨hn, hd⟩ := rootContext_component_bounds st.1
  have hlen := roundedRootRows_size st
  have hnL : st.1.1.2.length ≤ L := hn.trans hctx
  have hdL : (Ratio.encode st.1.2).length ≤ L := hd.trans hctx
  have hh : st.1.1.2.length * (2 * (st.1.1.2.length *
        (2 * (3 * (Ratio.encode st.1.2).length + 13) + 1)) + 1) ≤
      L * (2 * (L * (2 * (3 * L + 13) + 1)) + 1) := by gcongr
  simp only [rootStateEncoding, roundedRootStep, encodePair_length]
  nlinarith

def rootUnitStep (u : RootState × Unit) : RootState := roundedRootStep u.1

@[fun_prop] theorem rootUnitStep_poly : Poly rootUnitStep := by
  unfold rootUnitStep
  fun_prop

theorem roundedRootFold_size (xs : List Unit) (st : RootState) (L : ℕ)
    (hctx : (rootContextEncoding st.1).length ≤ L) :
    (rootStateEncoding (xs.foldl (fun st _ => roundedRootStep st) st)).length ≤
      max (rootStateEncoding st).length (1000 * (L + 1) ^ 3) := by
  induction xs generalizing st with
  | nil => exact le_max_left _ _
  | cons u xs ih =>
      have hh := ih (roundedRootStep st) hctx
      exact hh.trans ((max_le (roundedRootStep_size st L hctx) le_rfl).trans (le_max_right _ _))

noncomputable def rootFoldProgram :
    PolyProgram (encodePair (encodeList (fun _ : Unit => [])) rootStateEncoding)
      rootStateEncoding (fun u : List Unit × RootState =>
        u.1.foldl (fun st _ => roundedRootStep st) u.2) :=
  (Poly.program rootUnitStep_poly).listFold () (1001 * (Polynomial.X + 1) ^ 3) (by
    intro xs st pre suf he
    let M := (encodePair (encodeList (fun _ : Unit => [])) rootStateEncoding (xs, st)).length
    have hs : (rootStateEncoding st).length ≤ M := by
      dsimp [M]
      simp only [encodePair_length, Prod.fst, Prod.snd]
      omega
    have hc : (rootContextEncoding st.1).length ≤ M := by
      have hh : (rootContextEncoding st.1).length ≤ (rootStateEncoding st).length := by
        simp only [rootStateEncoding, encodePair_length]
        omega
      exact hh.trans hs
    have hh := roundedRootFold_size pre st M hc
    apply hh.trans
    change max (rootStateEncoding st).length (1000 * (M + 1) ^ 3) ≤
      (1001 * (Polynomial.X + 1) ^ 3 : Polynomial ℕ).eval M
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    apply max_le
    · have hp : M ≤ (M + 1) ^ 3 := by nlinarith [sq_nonneg (M : ℤ)]
      omega
    · omega)

@[fun_prop] theorem rootFold_poly :
    Poly (fun u : List Unit × RootState => u.1.foldl (fun st _ => roundedRootStep st) u.2) :=
  Poly.of_program rootFoldProgram

@[fun_prop] theorem rootZeroRows_poly : Poly rootZeroRows := by
  exact map_const_poly_comp Poly.identity
    (map_const_poly_comp Poly.identity
      (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := List Unit) (β := ℚ) 0))

@[fun_prop] theorem rootCompute_poly : Poly rootCompute := by
  have hi : Poly (fun u : RootContext × List Unit =>
      (u.2, (u.1, rootZeroRows u.1.1.2))) := by fun_prop
  exact Poly.comp (f := fun st : RootState => st.2)
    (Poly.snd) (Poly.comp rootFold_poly hi)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

@[fun_prop] theorem driftArguments_poly : Poly driftArguments := by
  unfold driftArguments
  fun_prop

@[fun_prop] theorem driftCoefficients_poly (S : SpinLaw) : Poly (driftCoefficients S) := by
  unfold driftCoefficients
  fun_prop

@[fun_prop] theorem driftTransposeProduct_poly (S : SpinLaw) : Poly (driftTransposeProduct S) := by
  unfold driftTransposeProduct
  fun_prop

@[fun_prop] theorem driftWithFuel_poly (S : SpinLaw) : Poly (driftWithFuel S) := by
  unfold driftWithFuel
  fun_prop

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

@[fun_prop] theorem snappedDriftWithFuel_poly (S : SpinLaw) : Poly (snappedDriftWithFuel S) := by
  unfold snappedDriftWithFuel
  fun_prop

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

@[fun_prop] theorem gaussianRadius_poly : Poly gaussianRadius := by unfold gaussianRadius; fun_prop
@[fun_prop] theorem gaussianMeshDen_poly : Poly gaussianMeshDen := by
  unfold gaussianMeshDen; simp only [pow_succ, pow_zero, mul_one]; fun_prop
@[fun_prop] theorem gaussianGridSize_poly : Poly gaussianGridSize := by unfold gaussianGridSize; fun_prop
@[fun_prop] theorem gaussianAccuracy_poly : Poly gaussianAccuracy := by unfold gaussianAccuracy; fun_prop
@[fun_prop] theorem gaussianBits_poly : Poly gaussianBits := by unfold gaussianBits; fun_prop
@[fun_prop] theorem gaussianMesh_poly : Poly gaussianMesh := by unfold gaussianMesh; fun_prop

@[fun_prop] theorem gaussianNode_poly : Poly gaussianNode := by unfold gaussianNode; fun_prop

@[fun_prop] theorem unitize_poly : Poly unitize := by
  exact map_const_poly_comp (α := List Bool) (β := Bool) (γ := Unit)
    (xs := id) (c := fun _ => ()) Poly.identity
    (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := List Bool) (β := Unit) ())

@[fun_prop] theorem boolIndices_poly : Poly boolIndices := Poly.list_indices

@[fun_prop] theorem gaussianNodes_poly : Poly gaussianNodes := by unfold gaussianNodes; fun_prop

@[fun_prop] theorem gaussianWeights_poly : Poly gaussianWeights := by unfold gaussianWeights; fun_prop

@[fun_prop] theorem gaussianCounts_poly : Poly gaussianCounts := by unfold gaussianCounts; fun_prop

@[fun_prop] theorem gaussianDraw_poly : Poly gaussianDraw := by unfold gaussianDraw; fun_prop

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic IsingLTL.BeliefProp

@[fun_prop] theorem sampleScalarTable_poly : Poly sampleScalarTable := by
  unfold sampleScalarTable
  fun_prop

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

end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory ProbabilityTheory

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem bitBlock_poly : Poly bitBlock := by unfold bitBlock; fun_prop

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem boundedRound_poly : Poly boundedRound := by unfold boundedRound; fun_prop

noncomputable def boundedRoundSize : Polynomial ℕ :=
  PolyProgram.ratMul.sizeBound.comp
    (2 * Polynomial.X + 3 * PolyProgram.ratDiv.sizeBound.comp (3 * Polynomial.X + 1) + 14)

theorem boundedRound_size (x d M : ℚ) (L : ℕ)
    (hd : (Ratio.encode d).length ≤ L) (hM : (Ratio.encode M).length ≤ L) :
    (Ratio.encode (boundedRound ((x, d), M))).length ≤ boundedRoundSize.eval L := by
  have hd0 := PolyProgram.ratDiv.length_bound (d, M)
  have hpair : (encodePair Ratio.encode Ratio.encode (d, M)).length ≤ 3 * L + 1 := by
    simp only [encodePair_length]
    omega
  have hdiv := hd0.trans (polynomial_eval_mono PolyProgram.ratDiv.sizeBound hpair)
  change (Ratio.encode (d / M)).length ≤ PolyProgram.ratDiv.sizeBound.eval (3 * L + 1) at hdiv
  have hclamp := clampedRound_size (x / M) (d / M)
  have hcl : (Ratio.encode (clampedRound (x / M, d / M))).length ≤
      3 * PolyProgram.ratDiv.sizeBound.eval (3 * L + 1) + 13 := by omega
  have hp : (encodePair Ratio.encode Ratio.encode
      (M, clampedRound (x / M, d / M))).length ≤
        2 * L + 3 * PolyProgram.ratDiv.sizeBound.eval (3 * L + 1) + 14 := by
    simp only [encodePair_length]
    omega
  have hh := (PolyProgram.ratMul.length_bound (M, clampedRound (x / M, d / M))).trans
    (polynomial_eval_mono PolyProgram.ratMul.sizeBound hp)
  simpa only [boundedRound, boundedRoundSize, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one] using hh

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

@[fun_prop] theorem eulerDrift_poly (S : SpinLaw) : Poly (eulerDrift S) := by
  unfold eulerDrift
  fun_prop

@[fun_prop] theorem gaussianNoiseBits_poly : Poly gaussianNoiseBits := by
  unfold gaussianNoiseBits gaussianNoiseTail
  simp only [pow_succ, pow_zero, mul_one]
  fun_prop

@[fun_prop] theorem eulerNoise_poly : Poly eulerNoise := by unfold eulerNoise; fun_prop

@[fun_prop] theorem eulerRaw_poly (S : SpinLaw) : Poly (eulerRaw S) := by
  unfold eulerRaw
  fun_prop

@[fun_prop] theorem eulerRows_poly (S : SpinLaw) : Poly (eulerRows S) := by
  unfold eulerRows
  fun_prop

@[fun_prop] theorem eulerStep_poly (S : SpinLaw) : Poly (eulerStep S) := by
  unfold eulerStep
  fun_prop

def driftContextEncoding : DriftContext → List Bool :=
  encodePair (encodePair matrixEncoding (encodeList Ratio.encode))
    (encodePair (encodeList (fun _ : Unit => []))
      (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
def eulerSettingsEncoding : ((ℚ × ℚ) × ((ℚ × ℕ) × (ℚ × List Unit))) → List Bool :=
  encodePair (encodePair Ratio.encode Ratio.encode)
    (encodePair (encodePair Ratio.encode Nat.bits)
      (encodePair Ratio.encode (encodeList (fun _ : Unit => []))))
def eulerContextEncoding : EulerContext → List Bool :=
  encodePair driftContextEncoding eulerSettingsEncoding
def eulerStateEncoding : EulerState → List Bool :=
  encodePair eulerContextEncoding (encodePair (encodeList Ratio.encode) (encodeList encodeBool))

theorem eulerContext_components (c : EulerContext) :
    c.1.2.1.length ≤ (eulerContextEncoding c).length ∧
      (Ratio.encode c.2.1.2).length ≤ (eulerContextEncoding c).length ∧
      (Ratio.encode c.2.2.2.1).length ≤ (eulerContextEncoding c).length := by
  have hu := EncodedList.length_le (fun _ : Unit => []) c.1.2.1
  simp only [eulerContextEncoding, driftContextEncoding, eulerSettingsEncoding, encodePair_length]
  omega

theorem eulerRows_size (S : SpinLaw) (st : EulerState) (L : ℕ)
    (hctx : (eulerContextEncoding st.1).length ≤ L) :
    (encodeList Ratio.encode (eulerRows S st)).length ≤ L * (2 * boundedRoundSize.eval L + 1) := by
  obtain ⟨hn, hd, hM⟩ := eulerContext_components st.1
  have hs := EncodedList.length_bound Ratio.encode (eulerRows S st) (boundedRoundSize.eval L) (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact boundedRound_size _ _ _ L (hd.trans hctx) (hM.trans hctx))
  have hl : (eulerRows S st).length ≤ L := by
    simp only [eulerRows, List.length_map, siteNumbers, List.length_range]
    exact hn.trans hctx
  exact hs.trans (Nat.mul_le_mul_right _ hl)

def eulerUnitStep (S : SpinLaw) (u : EulerState × Unit) : EulerState := eulerStep S u.1

@[fun_prop] theorem eulerUnitStep_poly (S : SpinLaw) : Poly (eulerUnitStep S) := by
  unfold eulerUnitStep
  fun_prop

theorem encoded_drop_length (xs : List Bool) (n : ℕ) :
    (encodeList encodeBool (xs.drop n)).length ≤ (encodeList encodeBool xs).length := by
  have he := congrArg (fun bs : List Bool => (encodeList encodeBool bs).length)
    (List.take_append_drop n xs)
  rw [EncodedList.append, List.length_append] at he
  omega

noncomputable def eulerStateSize : Polynomial ℕ :=
  10 * (Polynomial.X + 1) * (2 * boundedRoundSize + 3)

theorem eulerStep_size (S : SpinLaw) (st : EulerState) (L : ℕ)
    (hctx : (eulerContextEncoding st.1).length ≤ L)
    (htape : (encodeList encodeBool st.2.2).length ≤ L) :
    (eulerStateEncoding (eulerStep S st)).length ≤ eulerStateSize.eval L := by
  have hv := eulerRows_size S st L hctx
  have ht := (encoded_drop_length st.2.2
    (st.1.1.2.1.length * gaussianNoiseBits st.1.2.2.1.2)).trans htape
  change (encodePair eulerContextEncoding
    (encodePair (encodeList Ratio.encode) (encodeList encodeBool))
      (st.1, (eulerRows S st, st.2.2.drop
        (st.1.1.2.1.length * gaussianNoiseBits st.1.2.2.1.2)))).length ≤ _
  simp only [encodePair_length, eulerStateSize, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  nlinarith

theorem eulerFold_size (S : SpinLaw) (xs : List Unit) (st : EulerState) (L : ℕ)
    (hctx : (eulerContextEncoding st.1).length ≤ L)
    (htape : (encodeList encodeBool st.2.2).length ≤ L) :
    (eulerStateEncoding (xs.foldl (fun st _ => eulerStep S st) st)).length ≤
      max (eulerStateEncoding st).length (eulerStateSize.eval L) := by
  induction xs generalizing st with
  | nil => exact le_max_left _ _
  | cons u xs ih =>
      have ht := (encoded_drop_length st.2.2
        (st.1.1.2.1.length * gaussianNoiseBits st.1.2.2.1.2)).trans htape
      have hh := ih (eulerStep S st) hctx ht
      exact hh.trans ((max_le (eulerStep_size S st L hctx htape) le_rfl).trans (le_max_right _ _))

noncomputable def eulerFoldProgram (S : SpinLaw) :
    PolyProgram (encodePair (encodeList (fun _ : Unit => [])) eulerStateEncoding)
      eulerStateEncoding (fun u : List Unit × EulerState =>
        u.1.foldl (fun st _ => eulerStep S st) u.2) :=
  (Poly.program (eulerUnitStep_poly S)).listFold () (eulerStateSize + Polynomial.X) (by
    intro xs st pre suf he
    let L := (encodePair (encodeList (fun _ : Unit => [])) eulerStateEncoding (xs, st)).length
    have hs : (eulerStateEncoding st).length ≤ L := by
      dsimp [L]
      simp only [encodePair_length]
      omega
    have hc : (eulerContextEncoding st.1).length ≤ L := by
      apply le_trans (show (eulerContextEncoding st.1).length ≤ (eulerStateEncoding st).length from ?_) hs
      change (eulerContextEncoding st.1).length ≤
        (encodePair eulerContextEncoding (encodePair (encodeList Ratio.encode)
          (encodeList encodeBool)) st).length
      simp only [encodePair_length]
      omega
    have ht : (encodeList encodeBool st.2.2).length ≤ L := by
      apply le_trans (show (encodeList encodeBool st.2.2).length ≤ (eulerStateEncoding st).length from ?_) hs
      change (encodeList encodeBool st.2.2).length ≤
        (encodePair eulerContextEncoding (encodePair (encodeList Ratio.encode)
          (encodeList encodeBool)) st).length
      simp only [encodePair_length]
      omega
    have hh := eulerFold_size S pre st L hc ht
    apply hh.trans
    change max (eulerStateEncoding st).length (eulerStateSize.eval L) ≤
      (eulerStateSize + Polynomial.X).eval L
    simp only [Polynomial.eval_add, Polynomial.eval_X]
    apply max_le <;> omega)

@[fun_prop] theorem eulerFold_poly (S : SpinLaw) :
    Poly (fun u : List Unit × EulerState => u.1.foldl (fun st _ => eulerStep S st) u.2) :=
  Poly.of_program (eulerFoldProgram S)

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

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
noncomputable section

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

@[fun_prop] theorem rationalAbs_poly : Poly (abs : ℚ → ℚ) := by
  have hh : Poly (fun q : ℚ => if q < 0 then -q else q) := by fun_prop
  have he : (fun q : ℚ => if q < 0 then -q else q) = abs := by
    funext q
    by_cases hq : q < 0
    · simp [hq, abs_of_neg hq]
    · simp [hq, abs_of_nonneg (le_of_not_gt hq)]
  rw [he] at hh
  exact hh

@[fun_prop] theorem list_all_poly_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {p : α → β → Bool} {xs : α → List β}
    (hp : Poly (fun u : α × β => p u.1 u.2)) (hxs : Poly xs) :
    Poly (fun a => (xs a).all (p a)) :=
  Poly.comp (Poly.of_program ((Poly.program hp).listAllWith default)) (Poly.pair Poly.identity hxs)

@[fun_prop] theorem rootResidualTest_poly : Poly rootResidualTest := by
  unfold rootResidualTest
  fun_prop

@[fun_prop] theorem approximatePSDTest_poly : Poly approximatePSDTest := by
  unfold approximatePSDTest
  fun_prop

@[fun_prop] theorem rootTolerance_poly : Poly rootTolerance := by
  unfold rootTolerance
  fun_prop

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

@[fun_prop] theorem envelopeLeft_poly : Poly envelopeLeft := by
  unfold envelopeLeft
  fun_prop

@[fun_prop] theorem envelopeMesh_poly : Poly envelopeMesh := by unfold envelopeMesh; fun_prop

@[fun_prop] theorem envelopeNode_poly : Poly envelopeNode := by unfold envelopeNode; fun_prop

@[fun_prop] theorem envelopeValue_poly (S : SpinLaw) : Poly (envelopeValue S) := by
  unfold envelopeValue
  fun_prop

@[fun_prop] theorem envelopeWithFuel_poly (S : SpinLaw) : Poly (envelopeWithFuel S) := by
  unfold envelopeWithFuel
  fun_prop

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem natPow_poly (n : ℕ) : Poly (fun x : ℕ => x ^ n) := by
  induction n with
  | zero => simpa using
      (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := ℕ) (β := ℕ) 1)
  | succ n ih =>
      simp only [pow_succ]
      fun_prop

@[fun_prop] theorem unitProduct_poly : Poly unitProduct := by unfold unitProduct; fun_prop

@[fun_prop] theorem unitPower_poly (n : ℕ) : Poly (unitPower n) := by
  induction n with
  | zero => exact OAI.MetricKMedian.Binary.Automatic.Poly.const (α := List Unit) (β := List Unit) [()]
  | succ n ih =>
      change Poly (fun xs : List Unit => unitProduct (unitPower n xs, xs))
      fun_prop

@[fun_prop] theorem polynomialFuel_poly (C n : ℕ) : Poly (polynomialFuel C n) := by
  unfold polynomialFuel
  fun_prop

@[fun_prop] theorem boundedPower_poly (b : ℕ) : Poly (boundedPower b) := by
  unfold boundedPower
  fun_prop

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

@[fun_prop] theorem preTolerance_poly (C : ℕ) : Poly (preTolerance C) := by
  unfold preTolerance
  simp only [pow_succ, pow_zero, mul_one]
  fun_prop

@[fun_prop] theorem preBuffer_poly : Poly preBuffer := by unfold preBuffer; fun_prop

@[fun_prop] theorem candidateLevel_poly (S : SpinLaw) (C : ℕ) : Poly (candidateLevel S C) := by
  unfold candidateLevel
  fun_prop

@[fun_prop] theorem normalizedShift_poly (S : SpinLaw) : Poly (normalizedShift S) := by
  unfold normalizedShift
  fun_prop

@[fun_prop] theorem candidatePSD_poly (S : SpinLaw) (C : ℕ) : Poly (candidatePSD S C) := by
  unfold candidatePSD
  fun_prop

@[fun_prop] theorem preInside_poly (S : SpinLaw) (C : ℕ) : Poly (preInside S C) := by
  unfold preInside
  fun_prop

@[fun_prop] theorem preTests_poly (S : SpinLaw) (C : ℕ) : Poly (preTests S C) := by
  unfold preTests
  fun_prop

@[fun_prop] theorem preSelectedLevel_poly (S : SpinLaw) (C : ℕ) : Poly (preSelectedLevel S C) := by
  unfold preSelectedLevel
  fun_prop

@[fun_prop] theorem preIntegralPrecision_poly (C : ℕ) : Poly (preIntegralPrecision C) := by
  unfold preIntegralPrecision
  fun_prop

@[fun_prop] theorem preIntegral_poly (S : SpinLaw) (C : ℕ) : Poly (preIntegral S C) := by
  unfold preIntegral
  fun_prop

@[fun_prop] theorem preCap_poly (S : SpinLaw) (C : ℕ) : Poly (preCap S C) := by
  unfold preCap
  fun_prop

@[fun_prop] theorem retryCount_poly (S : SpinLaw) (C : ℕ) : Poly (retryCount S C) := by
  unfold retryCount
  fun_prop

@[fun_prop] theorem baseBudget_poly (S : SpinLaw) (C : ℕ) : Poly (baseBudget S C) := by
  unfold baseBudget
  fun_prop

@[fun_prop] theorem uniformBudget_poly (S : SpinLaw) (C : ℕ) : Poly (uniformBudget S C) := by
  unfold uniformBudget
  exact Poly.comp (f := fun x : ℕ => x ^ 100) (g := baseBudget S C)
    (natPow_poly 100) (baseBudget_poly S C)

@[fun_prop] theorem criticalCoins_poly (S : SpinLaw) (C : ℕ) : Poly (criticalCoins S C) := by
  unfold criticalCoins
  exact Poly.comp (f := fun x : ℕ => x ^ 10000) (g := uniformBudget S C)
    (natPow_poly 10000) (uniformBudget_poly S C)

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

@[fun_prop] theorem spinBits_poly (S : SpinLaw) : Poly (spinBits S) := by unfold spinBits; fun_prop

@[fun_prop] theorem spinPrecision_poly (C : ℕ) : Poly (spinPrecision C) := by unfold spinPrecision; fun_prop

@[fun_prop] theorem spinDrawWeights_poly (S : SpinLaw) (C : ℕ) : Poly (spinDrawWeights S C) := by
  unfold spinDrawWeights
  fun_prop

@[fun_prop] theorem spinDraw_poly (S : SpinLaw) (C : ℕ) : Poly (spinDraw S C) := by
  unfold spinDraw
  fun_prop

@[fun_prop] theorem acceptanceBits_poly : Poly acceptanceBits := by unfold acceptanceBits; fun_prop

@[fun_prop] theorem clipProbability_poly : Poly clipProbability := by unfold clipProbability; fun_prop

@[fun_prop] theorem bernoulliDraw_poly : Poly bernoulliDraw := by unfold bernoulliDraw; fun_prop

@[fun_prop] theorem kernelFields_poly : Poly kernelFields := by unfold kernelFields; fun_prop

@[fun_prop] theorem kernelIntegralSum_poly (S : SpinLaw) : Poly (kernelIntegralSum S) := by
  unfold kernelIntegralSum
  fun_prop

@[fun_prop] theorem kernelAcceptance_poly (S : SpinLaw) : Poly (kernelAcceptance S) := by
  unfold kernelAcceptance
  fun_prop

@[fun_prop] theorem kernelSpinValues_poly (S : SpinLaw) (C : ℕ) : Poly (kernelSpinValues S C) := by
  unfold kernelSpinValues
  fun_prop

@[fun_prop] theorem kernelOutput_auto_poly (S : SpinLaw) (C : ℕ) : Poly (kernelOutput S C) := by
  have hout : Poly (fun u : KernelInput => (kernelSpinValues S C u).flatMap
      QAlgorithms.LocalHamiltonian.encRat) :=
    Poly.comp (f := fun qs : List ℚ => qs.flatMap QAlgorithms.LocalHamiltonian.encRat)
      (Poly.of_program (encRatsProgram.comp BooleanLists.packProgram)) (kernelSpinValues_poly S C)
  unfold kernelOutput
  fun_prop

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

@[fun_prop] theorem enumerationRecords_poly (S : SpinLaw) : Poly (enumerationRecords S) := by
  unfold enumerationRecords
  fun_prop

@[fun_prop] theorem enumerationMaximum_poly (S : SpinLaw) : Poly (enumerationMaximum S) := by
  unfold enumerationMaximum
  fun_prop

@[fun_prop] theorem enumerationPivotWeight_poly (S : SpinLaw) : Poly (enumerationPivotWeight S) := by
  unfold enumerationPivotWeight
  fun_prop

@[fun_prop] theorem enumerationTolerance_poly (S : SpinLaw) : Poly (enumerationTolerance S) := by
  unfold enumerationTolerance
  fun_prop

@[fun_prop] theorem enumerationWeights_poly (S : SpinLaw) : Poly (enumerationWeights S) := by
  unfold enumerationWeights
  fun_prop

@[fun_prop] theorem enumerationCounts_poly (S : SpinLaw) : Poly (enumerationCounts S) := by
  unfold enumerationCounts
  fun_prop

@[fun_prop] theorem enumerationSelected_poly (S : SpinLaw) : Poly (enumerationSelected S) := by
  unfold enumerationSelected
  fun_prop

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem binaryWords_rest_length (xs : List Bool) : (binaryWords xs).2.length ≤ xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [binaryWords]
  | singleton b => cases b <;> simp [binaryWords]
  | cons_cons a b xs ih => cases a <;> simp [binaryWords] <;> omega

theorem integerTotal_rest_length (xs : List Bool) : (integerTotal xs).2.length ≤ xs.length := by
  exact (binaryWords_rest_length xs.tail).trans (by simp)

theorem rationalTotal_rest_length (xs : List Bool) : (rationalTotal xs).2.length ≤ xs.length :=
  (binaryWords_rest_length (integerTotal xs).2).trans (integerTotal_rest_length xs)

noncomputable def rationalReadBound : Polynomial ℕ := rationalProgram.sizeBound

theorem rationalTotal_value_size (xs : List Bool) :
    (Ratio.encode (rationalTotal xs).1).length ≤ rationalReadBound.eval xs.length := by
  have hh := rationalProgram.length_bound xs
  simp only [encodePair_length, id_eq] at hh
  change _ ≤ rationalProgram.sizeBound.eval xs.length
  omega

@[fun_prop] theorem rationalReadStep_poly : Poly rationalReadStep := by
  unfold rationalReadStep
  fun_prop

def readerEncoding : RationalReaderState → List Bool :=
  encodePair (encodeList encodeBool) (encodeList Ratio.encode)

theorem readerEncoding_length (s : RationalReaderState) :
    (readerEncoding s).length = 6 * s.1.length + 1 + (encodeList Ratio.encode s.2).length := by
  simp only [readerEncoding, encodePair_length, BooleanLists.length]
  omega

theorem rationalReadStep_rest_length (s : RationalReaderState) (u : Unit) :
    (rationalReadStep (s, u)).1.length ≤ s.1.length := rationalTotal_rest_length s.1

theorem rationalReadStep_size (s : RationalReaderState) (u : Unit) (R : ℕ) (hs : s.1.length ≤ R) :
    (readerEncoding (rationalReadStep (s, u))).length ≤
      (readerEncoding s).length + 2 * rationalReadBound.eval R + 1 := by
  have hrest := rationalReadStep_rest_length s u
  have hvalue := (rationalTotal_value_size s.1).trans (polynomial_eval_mono rationalReadBound hs)
  simp only [readerEncoding_length, rationalReadStep, EncodedList.cons_length] at *
  omega

theorem rationalReadFold_bound (us : List Unit) (s : RationalReaderState) (R : ℕ)
    (hs : s.1.length ≤ R) :
    (us.foldl (fun s u => rationalReadStep (s, u)) s).1.length ≤ R ∧
      (readerEncoding (us.foldl (fun s u => rationalReadStep (s, u)) s)).length ≤
        (readerEncoding s).length + us.length * (2 * rationalReadBound.eval R + 1) := by
  induction us generalizing s with
  | nil => simpa using And.intro hs (le_refl (readerEncoding s).length)
  | cons u us ih =>
      have hstep := rationalReadStep_size s u R hs
      have hnext := (rationalReadStep_rest_length s u).trans hs
      obtain ⟨hr, he⟩ := ih (rationalReadStep (s, u)) hnext
      refine ⟨hr, ?_⟩
      simp only [List.foldl_cons, List.length_cons]
      nlinarith

noncomputable def rationalReadFoldProgram :
    PolyProgram (encodePair (encodeList (fun _ : Unit => [])) readerEncoding) readerEncoding
      (fun x : List Unit × RationalReaderState =>
        x.1.foldl (fun s u => rationalReadStep (s, u)) x.2) :=
  (Poly.program rationalReadStep_poly).listFold ()
    (Polynomial.X * (2 * rationalReadBound + 2)) (by
      intro us s pre suf heq
      let L := (encodePair (encodeList (fun _ : Unit => [])) readerEncoding (us, s)).length
      have hsLen : (readerEncoding s).length ≤ L := by simp [L, encodePair_length]
      have hsRest : s.1.length ≤ L := by
        have hh := readerEncoding_length s
        omega
      have hpre : pre.length ≤ L := by
        have hu := EncodedList.length_le (fun _ : Unit => []) us
        have hparts := congrArg List.length heq
        simp only [List.length_append] at hparts
        simp only [L, encodePair_length]
        omega
      have hh := (rationalReadFold_bound pre s L hsRest).2
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_ofNat]
      change (readerEncoding (pre.foldl (fun s u => rationalReadStep (s, u)) s)).length ≤
        L * (2 * rationalReadBound.eval L + 2)
      nlinarith)

@[fun_prop] theorem readRationals_poly : Poly readRationals := by
  have hs : Poly (fun x : List Unit × List Bool => (x.1, (x.2, ([] : List ℚ)))) := by fun_prop
  have hf : Poly (fun x : List Unit × List Bool =>
      x.1.foldl (fun s u => rationalReadStep (s, u)) (x.2, [])) :=
    Poly.comp (Poly.of_program rationalReadFoldProgram) hs
  have hout : Poly (fun s : RationalReaderState => s.2.reverse) := by fun_prop
  change Poly (fun x : List Unit × List Bool =>
    (x.1.foldl (fun s u => rationalReadStep (s, u)) (x.2, [])).2.reverse)
  exact Poly.comp (f := fun s : RationalReaderState => s.2.reverse)
    (g := fun x : List Unit × List Bool =>
      x.1.foldl (fun s u => rationalReadStep (s, u)) (x.2, [])) hout hf

@[fun_prop] theorem siteTokens_poly : Poly siteTokens := by
  unfold siteTokens
  fun_prop

@[fun_prop] theorem rationalSlots_poly : Poly rationalSlots := by
  unfold rationalSlots
  fun_prop

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem modelFromFlat_poly : Poly modelFromFlat := by
  unfold modelFromFlat
  dsimp only
  have hi : Poly (fun u : List Unit × List ℚ => List.range u.1.length) :=
    Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun u : List Unit × List ℚ => u.1) Poly.list_indices (by fun_prop)
  have hr : Poly (fun u : List Unit × List ℚ =>
      (List.range u.1.length).map (fun i => (u.2.drop (i * u.1.length)).take u.1.length)) :=
    Poly.list_map (f := fun (u : List Unit × List ℚ) (i : ℕ) =>
      (u.2.drop (i * u.1.length)).take u.1.length)
      (as := fun u : List Unit × List ℚ => List.range u.1.length) (by fun_prop) hi
  exact Poly.pair hr (by fun_prop)

@[fun_prop] theorem parseModel_poly : Poly parseModel := by unfold parseModel; fun_prop

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

@[fun_prop] theorem requestPair_auto_poly : Poly requestPair :=
  ⟨((BooleanLists.unpackProgram.comp requestPairProgram).comp
    (BooleanLists.packProgram.product BooleanLists.packProgram)).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem requestParams_poly : Poly requestParams := by
  apply Poly.pair
  · exact Poly.comp parseModel_poly (Poly.comp (by fun_prop) requestPair_auto_poly)
  · exact Poly.comp (by fun_prop : Poly (fun p : ℕ × List Bool => p.1))
      (Poly.comp binaryTotal_poly (Poly.comp (by fun_prop) requestPair_auto_poly))

@[fun_prop] theorem budgetFromPowers_poly : Poly budgetFromPowers := by
  unfold budgetFromPowers
  simp only [pow_succ, pow_zero, mul_one]
  fun_prop

@[fun_prop] theorem enumerationBudget_poly (S : SpinLaw) : Poly (enumerationBudget S) := by
  have hn : Poly (fun p : ParsedInput =>
      naturalProduct (p.1.2.map (fun _ : Unit => (alphabet S).length))) :=
    Poly.comp naturalProduct_poly (map_const_poly_comp (by fun_prop) (by fun_prop))
  have hd : Poly (fun p : ParsedInput =>
      naturalProduct (p.1.2.map (fun _ : Unit => (alphabet S).length * weightDenominatorBound S))) :=
    Poly.comp naturalProduct_poly (map_const_poly_comp (by fun_prop) (by fun_prop))
  exact Poly.comp (f := budgetFromPowers)
    (g := fun p : ParsedInput =>
      (naturalProduct (p.1.2.map (fun _ : Unit => (alphabet S).length)),
       naturalProduct (p.1.2.map (fun _ : Unit => (alphabet S).length * weightDenominatorBound S)), p.2))
    budgetFromPowers_poly (Poly.pair hn (Poly.pair hd (by fun_prop)))

@[fun_prop] theorem rawEnumerationSelected_poly (S : SpinLaw) : Poly (rawEnumerationSelected S) := by
  unfold rawEnumerationSelected
  fun_prop

section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] List.flatMap
noncomputable section
def ratListOutputLift {f : List Bool → List ℚ}
    (P : PolyProgram id (encodeList Ratio.encode) f) :
    PolyProgram id id (fun xs => (f xs).flatMap encRat) :=
  (P.comp encRatsProgram).congr _ (fun _ => rfl)

noncomputable def rawEnumerationOutputProgram (S : SpinLaw) :
    PolyProgram id id (rawEnumerationOutput S) := by
  let P : PolyProgram id (encodeList Ratio.encode) (rawEnumerationSelected S) :=
    BooleanLists.packProgram.comp (Poly.program (rawEnumerationSelected_poly S))
  exact (ratListOutputLift P).congr (rawEnumerationOutput S) (fun xs => by
    unfold rawEnumerationOutput
    rfl)

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

@[fun_prop] theorem samplerPre_poly : Poly samplerPre := by unfold samplerPre; fun_prop

@[fun_prop] theorem samplerR_poly (S : SpinLaw) (C : ℕ) : Poly (samplerR S C) := by unfold samplerR; fun_prop

@[fun_prop] theorem samplerQuality_poly (S : SpinLaw) (C : ℕ) : Poly (samplerQuality S C) := by
  unfold samplerQuality
  exact Poly.comp (f := fun x : ℕ => x ^ 100) (g := samplerR S C) (natPow_poly 100) (samplerR_poly S C)

@[fun_prop] theorem samplerMesh_poly (S : SpinLaw) (C : ℕ) : Poly (samplerMesh S C) := by unfold samplerMesh; fun_prop

@[fun_prop] theorem samplerStepScale_poly (S : SpinLaw) (C : ℕ) : Poly (samplerStepScale S C) := by
  unfold samplerStepScale
  fun_prop

@[fun_prop] theorem samplerStepCount_poly (S : SpinLaw) (C : ℕ) : Poly (samplerStepCount S C) := by
  unfold samplerStepCount
  exact Poly.comp (by fun_prop : Poly (fun n : ℕ => 16 * 2048 ^ 2 * n))
    (Poly.comp (natPow_poly 12) (samplerR_poly S C))

@[fun_prop] theorem samplerRootTarget_poly (C : ℕ) : Poly (samplerRootTarget C) := by
  unfold samplerRootTarget
  simp only [pow_succ, pow_zero, mul_one]
  fun_prop

@[fun_prop] theorem samplerNormalizedMatrix_poly (C : ℕ) : Poly (samplerNormalizedMatrix C) := by
  unfold samplerNormalizedMatrix
  fun_prop

@[fun_prop] theorem samplerRoot_poly (C : ℕ) : Poly (samplerRoot C) := by unfold samplerRoot; fun_prop

@[fun_prop] theorem samplerDriftContext_poly (S : SpinLaw) (C : ℕ) : Poly (samplerDriftContext S C) := by
  unfold samplerDriftContext
  fun_prop

@[fun_prop] theorem samplerStateBound_poly (S : SpinLaw) (C : ℕ) : Poly (samplerStateBound S C) := by
  unfold samplerStateBound
  fun_prop

@[fun_prop] theorem samplerEulerContext_poly (S : SpinLaw) (C : ℕ) : Poly (samplerEulerContext S C) := by
  unfold samplerEulerContext
  fun_prop

@[fun_prop] theorem samplerTrialBits_poly (S : SpinLaw) (C : ℕ) : Poly (samplerTrialBits S C) := by
  unfold samplerTrialBits
  fun_prop

@[fun_prop] theorem samplerTrialState_poly (S : SpinLaw) (C : ℕ) : Poly (samplerTrialState S C) := by
  unfold samplerTrialState
  exact Poly.comp (f := fun p : List Unit × EulerState => p.1.foldl (fun st _ => eulerStep S st) p.2)
    (g := fun u : SamplerInput × ℕ =>
      ((unitize u.1.2).take (samplerStepCount S C u.1),
       (samplerEulerContext S C u.1, (u.1.1.1.2.map (fun _ => (0 : ℚ)),
         bitBlock ((u.1.2, samplerTrialBits S C u.1), u.2)))))
    (eulerFold_poly S) (by fun_prop)

@[fun_prop] theorem samplerTrialOutput_poly (S : SpinLaw) (C : ℕ) : Poly (samplerTrialOutput S C) := by
  unfold samplerTrialOutput
  fun_prop

@[fun_prop] theorem samplerTrialOutputs_poly (S : SpinLaw) (C : ℕ) : Poly (samplerTrialOutputs S C) := by
  unfold samplerTrialOutputs
  fun_prop

@[fun_prop] theorem samplerRetryOutput_poly (S : SpinLaw) (C : ℕ) : Poly (samplerRetryOutput S C) := by
  unfold samplerRetryOutput
  fun_prop

@[fun_prop] theorem finalSamplerCoins_poly (S : SpinLaw) (C : ℕ) : Poly (finalSamplerCoins S C) := by
  unfold finalSamplerCoins
  fun_prop

attribute [local semireducible] samplerRequest

@[fun_prop] theorem samplerRequest_poly : Poly samplerRequest := by
  apply Poly.pair
  · exact Poly.comp (f := requestParams) (g := fun xs : List Bool => (requestPair xs).2)
      requestParams_poly (Poly.comp Poly.snd requestPair_auto_poly)
  · exact Poly.comp Poly.fst requestPair_auto_poly

attribute [local irreducible] samplerRequest

@[fun_prop] theorem finalSamplerRun_poly (S : SpinLaw) (C : ℕ) : Poly (finalSamplerRun S C) := by
  have henum : Poly (rawEnumerationOutput S) :=
    Poly.of_program (((BooleanLists.unpackProgram.comp (rawEnumerationOutputProgram S)).comp
      BooleanLists.packProgram).congr _ (fun _ => rfl))
  unfold finalSamplerRun
  fun_prop

noncomputable def finalSamplerProgram (S : SpinLaw) (C : ℕ) :
    PolyProgram id id (finalSamplerRun S C) :=
  ((BooleanLists.packProgram.comp (Poly.program (finalSamplerRun_poly S C))).comp
    BooleanLists.unpackProgram).congr _ (fun _ => by simp only [Function.comp_apply, id_eq])

noncomputable def finalCoinProgram (S : SpinLaw) (C : ℕ) :
    PolyProgram id Nat.bits (finalSamplerCoins S C) :=
  (BooleanLists.packProgram.comp (Poly.program (finalSamplerCoins_poly S C))).congr _ (fun _ => rfl)

noncomputable def criticalWindowMachine (S : SpinLaw) (C : ℕ) : RandMachine :=
  programRandMachine (finalSamplerProgram S C) (finalCoinProgram S C)

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

theorem criticalWindowMachine_run_eq (S : SpinLaw) (C : ℕ) (xs : List Bool) :
    (criticalWindowMachine S C).run xs = finalSamplerRun S C xs := rfl

theorem criticalWindowMachine_coins_eq (S : SpinLaw) (C : ℕ) (xs : List Bool) :
    (criticalWindowMachine S C).coins xs = finalSamplerCoins S C xs := rfl

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
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerDataFacts
open CritWinSpin.LocalTM2.Compiled PreprocessPSD

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
attribute [local irreducible] CritWinSpin.LocalTM2.Compiled.criticalWindowMachine CritWinSpin.LocalTM2.Compiled.kernelOutput CritWinSpin.LocalTM2.Compiled.kernelAcceptance CritWinSpin.LocalTM2.Compiled.trialOnBlock CritWinSpin.LocalTM2.Compiled.samplerRetryOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutputs CritWinSpin.LocalTM2.Compiled.samplerTrialState CritWinSpin.LocalTM2.Compiled.samplerEulerContext CritWinSpin.LocalTM2.Compiled.samplerDriftContext CritWinSpin.LocalTM2.Compiled.samplerRoot CritWinSpin.Implementation.FiniteRetry.retry CritWinSpin.LocalTM2.FiniteDraw.law

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
attribute [local irreducible] criticalWindowMachine kernelOutput EulerData.trialCode
  trialOnBlock samplerRetryOutput FiniteRetry.retry FiniteDraw.law

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


