-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P20
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:32:58.654891+00:00
-- url     : https://prove2.me/theorems/34a3210b-91e1-41e6-851b-5c2fddf85729
-- title:
--   Definitions for Exponents of quantum fixed-length pure state source coding
-- statement:
--   The objects the formalized statements of *Exponents of quantum fixed-length pure state source coding* (arXiv:quant-ph/0202002) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DiscretePureSource`: PDF pp.1-2: a discrete pure ensemble; its label set need not be finite. Summability and total mass one express a discrete probability distribution. The frozen Renew46.P43.PureSource is finite and injectively labelled, so it cannot represent this source domain; purity itself is imported from P08.
--   - `DiscretePureSource.average`: PDF p.2: the average is computed from the ensemble, never supplied freely.
--   - `DiscretePureSource.wordWeight`: PDF p.2: independent product probabilities at block length n.
--   - `DiscretePureSource.wordState`: PDF p.2: the tensor product of the actual word states.
--   - `VisibleCode`: PDF pp.1-2: finite nonzero memory, an arbitrary visible state map, and a CPTP decoder.
--   - `BlindCode`: PDF pp.1-2: a single quantum encoder fixed independently of the label.
--   - `averageLoss`: PDF pp.1-3: overlap loss, or exactly the square-root-overlap loss of Remark 2. The latter has no factor of two or outer square root.
--   - `VisibleSequence`: PDF p.2: visible code sequences, indexed by all positive block lengths.
--   - `BlindSequence`: PDF p.2: blind code sequences, with no oracle/label dependent encoder choice.
--   - `sequenceRate`: PDF p.2: limsup of log memory dimension divided by positive block length, in nats.
--   - `logRate`: PDF pp.2-3: -log 0 is +infinity, before taking any limit.
--   - `exponentObjective`: PDF pp.2-3: every exponent objective is a liminf.
--   - `visibleExponent`: PDF pp.2-3: visible error exponents are suprema; success exponents are infima. The feasible set uses limsup memory rate <= R.
--   - `blindExponent`: PDF pp.2-3: the blind analogue, optimizing over fixed CPTP encoders.
--   - `sourceLossAdmissible`: Section II, PDF p.2: ordinary admissibility requires error tending to zero; converse admissibility requires liminf error strictly below one. The latter is not convergence of the error and is not a limsup condition.
--   - `visibleMinimumRate`: Section II, PDF p.2: the infimum of limsup memory rates among actual visible code sequences satisfying the selected error criterion. Logarithms are natural; positive block lengths and memory dimensions come from VisibleSequence.
--   - `blindMinimumRate`: Section II, PDF p.2: the corresponding blind rate, with one CPTP encoder at each block length, fixed independently of the source word.
--   - `thresholdProjection`: PDF p.5: strict lower and inclusive upper threshold spectral projectors.
--   - `logPowerTrace`: PDF pp.3,5: psi(s) = log Tr rho^s, in natural logarithms.
--   - `visibleEncoders`: PDF p.5: the real convex set of all visible encoders.
--   - `extremeEncoders`: PDF p.5: the standard real extreme points of the visible-encoder set.
--   - `decoders`: PDF p.5: decoders are all CPTP maps between the full matrix algebras.
--   - `dilatedDecoders`: PDF p.5, (29): a finite nonzero ancillary space and a vector isometry, chosen before the input density. Its induced action is V rho V dagger.
--   - `IsPositiveTracePreserving`: PDF p.6 and Appendix D p.11: positive, trace-preserving complex-linear map.
--   - `quantumDValues`: Appendix A p.8: quantum relative entropies attained under an entropy constraint.
--   - `classicalDValues`: Appendix A p.8: the classical entropy-constrained value set.
--   - `expNegD`: Appendix B p.10: e^(-nD), with the extended boundary e^(-infinity) = 0.
--   - `blockMass`: Appendix B p.10: mass of the actual full isotypic block, not a highest-weight ray.
--   - `eventTypes`: Appendix B p.10: arbitrary simplex event, restricted to its empirical Young types.
--   - `eventD`: Appendix B p.10: finite event minimum, as an extended infimum; empty = +infinity.
--   - `lowerPrefactor`: Appendix B pp.9-10: the lower-bound polynomial, with real exponent -d(d+1)/2.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, https://arxiv.org/abs/quant-ph/0202002v6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)
open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)
open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)
open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- PDF pp.1-2: a discrete pure ensemble; its label set need not be finite.
Summability and total mass one express a discrete probability distribution.
The frozen Renew46.P43.PureSource is finite and injectively labelled, so it
cannot represent this source domain; purity itself is imported from P08. -/
structure DiscretePureSource (L : Type*) (d : ℕ) where
  dimension_pos : 0 < d
  weight : L → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_summable : Summable weight
  weight_total : ∑' i, weight i = 1
  state : L → Matrix (Fin d) (Fin d) ℂ
  state_density : ∀ i, IsDensityMatrix (state i)
  state_pure : ∀ i, IsPure (state i)

/-- PDF p.2: the average is computed from the ensemble, never supplied freely. -/
def DiscretePureSource.average {L : Type*} {d : ℕ} (S : DiscretePureSource L d) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑' i, (S.weight i : ℂ) • S.state i

/-- PDF p.2: independent product probabilities at block length n. -/
def DiscretePureSource.wordWeight {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (n : ℕ) (w : Fin n → L) : ℝ :=
  ∏ j, S.weight (w j)

/-- PDF p.2: the tensor product of the actual word states. -/
def DiscretePureSource.wordState {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (n : ℕ) (w : Fin n → L) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun x y => ∏ j, S.state (w j) (x j) (y j)

/-- PDF pp.1-2: finite nonzero memory, an arbitrary visible state map, and a CPTP decoder. -/
structure VisibleCode (L I : Type*) [Fintype I] [DecidableEq I] where
  memory : ℕ
  memory_pos : 0 < memory
  encode : L → Matrix (Fin memory) (Fin memory) ℂ
  encode_density : ∀ i, IsDensityMatrix (encode i)
  decode : Superop (Fin memory) I
  decode_channel : IsChannel decode

/-- PDF pp.1-2: a single quantum encoder fixed independently of the label. -/
structure BlindCode (I : Type*) [Fintype I] [DecidableEq I] where
  memory : ℕ
  memory_pos : 0 < memory
  encode : Superop I (Fin memory)
  encode_channel : IsChannel encode
  decode : Superop (Fin memory) I
  decode_channel : IsChannel decode

/-- PDF pp.1-3: overlap loss, or exactly the square-root-overlap loss of Remark 2.
The latter has no factor of two or outer square root. -/
def averageLoss {L I : Type*} [Fintype I] (p : L → ℝ)
    (rho output : L → Matrix I I ℂ) (bures : Bool) : ℝ :=
  ∑' i, p i * (if bures then 1 - Real.sqrt ((output i * rho i).trace.re)
    else 1 - (output i * rho i).trace.re)

/-- PDF p.2: visible code sequences, indexed by all positive block lengths. -/
abbrev VisibleSequence (L : Type*) (d : ℕ) :=
  (t : ℕ) → VisibleCode (Fin (t + 1) → L) (Fin (t + 1) → Fin d)

/-- PDF p.2: blind code sequences, with no oracle/label dependent encoder choice. -/
abbrev BlindSequence (d : ℕ) :=
  (t : ℕ) → BlindCode (Fin (t + 1) → Fin d)

/-- PDF p.2: limsup of log memory dimension divided by positive block length, in nats. -/
def sequenceRate (memory : ℕ → ℕ) : EReal :=
  Filter.limsup (fun t : ℕ =>
    ((Real.log (memory t : ℝ) / (t + 1 : ℕ) : ℝ) : EReal)) Filter.atTop

/-- PDF pp.2-3: -log 0 is +infinity, before taking any limit. -/
def logRate (q : ℝ) (n : ℕ) : EReal :=
  if q = 0 then ⊤ else ((-Real.log q / (n : ℝ) : ℝ) : EReal)

/-- PDF pp.2-3: every exponent objective is a liminf. -/
def exponentObjective (loss : ℕ → ℝ) (success : Bool) : EReal :=
  Filter.liminf (fun t : ℕ => logRate (if success then 1 - loss t else loss t) (t + 1))
    Filter.atTop

/-- PDF pp.2-3: visible error exponents are suprema; success exponents are infima.
The feasible set uses limsup memory rate <= R. -/
def visibleExponent {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (R : ℝ) (bures success : Bool) : EReal :=
  let values : Set EReal := {e | ∃ C : VisibleSequence L d,
    sequenceRate (fun t => (C t).memory) ≤ (R : EReal) ∧
    e = exponentObjective (fun t => averageLoss (S.wordWeight (t + 1))
      (S.wordState (t + 1)) (fun w => (C t).decode ((C t).encode w)) bures) success}
  if success then sInf values else sSup values

/-- PDF pp.2-3: the blind analogue, optimizing over fixed CPTP encoders. -/
def blindExponent {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (R : ℝ) (bures success : Bool) : EReal :=
  let values : Set EReal := {e | ∃ C : BlindSequence d,
    sequenceRate (fun t => (C t).memory) ≤ (R : EReal) ∧
    e = exponentObjective (fun t => averageLoss (S.wordWeight (t + 1))
      (S.wordState (t + 1))
      (fun w => (C t).decode ((C t).encode (S.wordState (t + 1) w))) bures) success}
  if success then sInf values else sSup values

/-- Section II, PDF p.2: ordinary admissibility requires error tending to zero;
converse admissibility requires liminf error strictly below one. The latter
is not convergence of the error and is not a limsup condition. -/
def sourceLossAdmissible (loss : ℕ → ℝ) (converse : Bool) : Prop :=
  if converse then
    Filter.liminf (fun t => (loss t : EReal)) Filter.atTop < (1 : EReal)
  else Filter.Tendsto loss Filter.atTop (𝓝 (0 : ℝ))

/-- Section II, PDF p.2: the infimum of limsup memory rates among actual visible
code sequences satisfying the selected error criterion. Logarithms are natural;
positive block lengths and memory dimensions come from VisibleSequence. -/
def visibleMinimumRate {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (converse : Bool) : EReal :=
  sInf {r | ∃ C : VisibleSequence L d,
    sourceLossAdmissible (fun t => averageLoss (S.wordWeight (t + 1))
      (S.wordState (t + 1)) (fun w => (C t).decode ((C t).encode w)) false) converse ∧
    r = sequenceRate (fun t => (C t).memory)}

/-- Section II, PDF p.2: the corresponding blind rate, with one CPTP encoder
at each block length, fixed independently of the source word. -/
def blindMinimumRate {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (converse : Bool) : EReal :=
  sInf {r | ∃ C : BlindSequence d,
    sourceLossAdmissible (fun t => averageLoss (S.wordWeight (t + 1))
      (S.wordState (t + 1))
      (fun w => (C t).decode ((C t).encode (S.wordState (t + 1) w))) false) converse ∧
    r = sequenceRate (fun t => (C t).memory)}

/-- PDF p.5: strict lower and inclusive upper threshold spectral projectors. -/
def thresholdProjection {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ)
    (lambda : ℝ) (upper : Bool) : Matrix (Fin d) (Fin d) ℂ :=
  cfc (fun x : ℝ => if upper then (if Real.exp lambda ≤ x then 1 else 0)
    else (if x < Real.exp lambda then 1 else 0)) rho

/-- PDF pp.3,5: psi(s) = log Tr rho^s, in natural logarithms. -/
def logPowerTrace {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) : ℝ :=
  Real.log ((cfc (fun x : ℝ => Real.rpow x s) rho).trace.re)

/-- PDF p.5: the real convex set of all visible encoders. -/
def visibleEncoders (L : Type*) (m : ℕ) : Set (L → Matrix (Fin m) (Fin m) ℂ) :=
  {F | ∀ i, IsDensityMatrix (F i)}

/-- PDF p.5: the standard real extreme points of the visible-encoder set. -/
def extremeEncoders (L : Type*) (m : ℕ) : Set (L → Matrix (Fin m) (Fin m) ℂ) :=
  (visibleEncoders L m).extremePoints ℝ

/-- PDF p.5: decoders are all CPTP maps between the full matrix algebras. -/
def decoders (m d : ℕ) : Set (Superop (Fin m) (Fin d)) :=
  {D | IsChannel D}

/-- PDF p.5, (29): a finite nonzero ancillary space and a vector isometry,
chosen before the input density. Its induced action is V rho V dagger. -/
def dilatedDecoders (m d : ℕ) : Set (Superop (Fin m) (Fin d)) :=
  {D | D ∈ decoders m d ∧ ∃ k : ℕ, 0 < k ∧
    ∃ V : Matrix (Fin d × Fin k) (Fin m) ℂ,
      Vᴴ * V = 1 ∧ ∀ rho, D rho = traceRight (V * rho * Vᴴ)}

/-- PDF p.6 and Appendix D p.11: positive, trace-preserving complex-linear map. -/
def IsPositiveTracePreserving {m d : ℕ}
    (D : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ A, A.PosSemidef → (D A).PosSemidef) ∧ ∀ A, (D A).trace = A.trace

/-- Appendix A p.8: quantum relative entropies attained under an entropy constraint. -/
def quantumDValues {d : ℕ} (rho : {M : Matrix (Fin d) (Fin d) ℂ // IsDensityMatrix M})
    (condition : ℝ → Prop) : Set ℝ≥0∞ :=
  {v | ∃ sigma : {M : Matrix (Fin d) (Fin d) ℂ // IsDensityMatrix M},
    condition (QAlgorithms.Papers.Independent.Information100.P56.entropy sigma.val) ∧
      v = QuantumLoss.umegakiEntropy sigma.val rho.val sigma.property rho.property}

/-- Appendix A p.8: the classical entropy-constrained value set. -/
def classicalDValues {d : ℕ} (a : Fin d → ℝ) (condition : ℝ → Prop) : Set ℝ≥0∞ :=
  {v | ∃ b : Fin d → ℝ, IsProbability b ∧ condition (shannonNats b) ∧ v = (classicalD (.finite 1 (by norm_num)) b a).toENNReal}

/-- Appendix B p.10: e^(-nD), with the extended boundary e^(-infinity) = 0. -/
def expNegD (n : ℕ) (D : ℝ≥0∞) : ℝ :=
  if D = ⊤ then 0 else Real.exp (-(n : ℝ) * D.toReal)

/-- Appendix B p.10: mass of the actual full isotypic block, not a highest-weight ray. -/
def blockMass {d n : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ)
    (shape : Schur.Partition d n) : ℝ :=
  (Schur.isotypicProjector shape * piKron n rho).trace.re

/-- Appendix B p.10: arbitrary simplex event, restricted to its empirical Young types. -/
def eventTypes {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (A : Set (Fin d → ℝ)) : Finset (Schur.Partition d n) :=
  Finset.univ.filter fun shape => Schur.normalizedRows hd hn shape ∈ A

/-- Appendix B p.10: finite event minimum, as an extended infimum; empty = +infinity. -/
def eventD {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (a : Fin d → ℝ) (A : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ⨅ shape : {shape : Schur.Partition d n // shape ∈ eventTypes hd hn A},
    (classicalD (.finite 1 (by norm_num)) (Schur.normalizedRows hd hn shape.val) a).toENNReal

/-- Appendix B pp.9-10: the lower-bound polynomial, with real exponent -d(d+1)/2. -/
def lowerPrefactor (d n : ℕ) : ℝ :=
  Real.rpow (n + d : ℝ) (-((d : ℝ) * (d + 1)) / 2)

-- Small definitional sanity checks: the zero-copy extension is never used as a code.
example {L : Type*} {d : ℕ} (S : DiscretePureSource L d) (w : Fin 0 → L) :
    S.wordWeight 0 w = 1 := by simp [DiscretePureSource.wordWeight]

example (n : ℕ) : logRate 0 n = ⊤ := by simp [logRate]

example : shannonNats (fun _ : Fin 1 => (1 : ℝ)) = 0 := by simp [shannonNats]

example {d : ℕ} : (classicalD (.finite 1 (by norm_num)) (fun _ : Fin d => 0) (fun _ => 0)).toENNReal = 0 := by
  simp [classicalD, EReal.toENNReal]

example (n : ℕ) : expNegD n ⊤ = 0 := by simp [expNegD]

example {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    eventTypes hd hn (∅ : Set (Fin d → ℝ)) = ∅ := by simp [eventTypes]

example {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (a : Fin d → ℝ) :
    eventD hd hn a ∅ = ⊤ := by simp [eventD, eventTypes]

example (m : ℕ) : visibleEncoders Empty m = Set.univ := by
  ext F
  simp [visibleEncoders]

-- Further sanity checks for the local source, code, loss, and shannonNats interfaces.
example {I : Type} [Fintype I] (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    IsPure (pureDensity v) := ⟨v, hv, rfl⟩

example {d : ℕ} (S : DiscretePureSource (Fin 1) d) :
    S.average = (S.weight 0 : ℂ) • S.state 0 := by simp [DiscretePureSource.average]

example {L : Type*} {d : ℕ} (S : DiscretePureSource L d) (w : Fin 1 → L)
    (x y : Fin 1 → Fin d) : S.wordState 1 w x y = S.state (w 0) (x 0) (y 0) := by
  simp [DiscretePureSource.wordState]

example {L I : Type*} [Fintype I] [DecidableEq I] (C : VisibleCode L I) (i : L) :
    IsDensityMatrix (C.encode i) := C.encode_density i

example {I : Type*} [Fintype I] [DecidableEq I] (C : BlindCode I) :
    IsChannel C.encode := C.encode_channel

example {L I : Type*} [Fintype I] (p : L → ℝ) (rho : L → Matrix I I ℂ) :
    averageLoss p rho (fun _ => 0) false = ∑' i, p i := by simp [averageLoss]

example : sequenceRate (fun _ => 1) = 0 := by simp [sequenceRate]

example (n : ℕ) : logRate 1 n = 0 := by simp [logRate]

example : exponentObjective (fun _ => 0) false = ⊤ := by
  simp [exponentObjective, logRate]

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) :
    thresholdProjection rho 0 true = cfc (fun x : ℝ => if 1 ≤ x then 1 else 0) rho := by
  simp [thresholdProjection]

example (s : ℝ) : logPowerTrace (1 : Matrix (Fin 1) (Fin 1) ℂ) s = 0 := by
  simp [logPowerTrace, cfc_one]

example (L : Type*) (m : ℕ) :
    extremeEncoders L m = (visibleEncoders L m).extremePoints ℝ := rfl

example (m d : ℕ) : dilatedDecoders m d ⊆ decoders m d := fun _ h => h.1

example (d : ℕ) : IsPositiveTracePreserving
    (LinearMap.id : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun _ h => h, fun _ => rfl⟩

example : IsProbability (fun _ : Fin 1 => (1 : ℝ)) := ⟨by simp, by simp⟩

example : QAlgorithms.Papers.Independent.Information100.P56.entropy (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P56.entropy, cfc_one]

example : (classicalD (.finite 1 (by norm_num)) (fun _ : Fin 1 => 1) (fun _ => 0)).toENNReal = ⊤ := by
  simp [classicalD, EReal.toENNReal]

example (n : ℕ) : expNegD n 0 = 1 := by simp [expNegD]

example : lowerPrefactor 1 1 = (1 / 2 : ℝ) := by
  norm_num [lowerPrefactor, Real.rpow_neg_one]

-- The new rate criteria accept exact coding and reject perpetual unit error.
example : sourceLossAdmissible (fun _ => 0) false := by
  simp [sourceLossAdmissible]

example : sourceLossAdmissible (fun _ => 0) true := by
  simp [sourceLossAdmissible]

example : ¬ sourceLossAdmissible (fun _ => 1) true := by
  simp [sourceLossAdmissible]

end QAlgorithms.Papers.Independent.Intakenext100.P20


