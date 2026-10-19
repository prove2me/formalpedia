-- Prove2me | Definitions.Def_QAlgorithms_Defs_BoundedMeanEstimation
-- name    : QAlgorithms_Defs_BoundedMeanEstimation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:41.637983+00:00
-- url     : https://prove2.me/theorems/8d6719d2-d2d6-4398-929c-b73bf952e38c
-- title:
--   BoundedMeanEstimation
-- statement:
--   BoundedMeanEstimation
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\BoundedMeanEstimation.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_SamplingUtilities
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- The §2 computation A: h+k qubits, a unitary matrix, initial zeroKet(h+k), last k wires as output, and fixed real-valued φ on Qubits k. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
structure CoherentValueSampler where
  h : ℕ
  k : ℕ
  A : Matrix.unitaryGroup (Qubits (h + k)) ℂ
  value : Qubits k → ℝ
  range : ∀ x, 0 ≤ value x ∧ value x ≤ 1

/-- μ=E[v(A)] computed as Σ_z prob(act A (zeroKet(h+k)),z) φ((qubitsAppendEquiv h k z).2), equivalently densityMean of pureDensity of the sampler state with that observable. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.9. -/
def samplerMean (S : CoherentValueSampler) : ℝ :=
  ∑ z, prob (act (S.A : Matrix _ _ ℂ) (zeroKet (S.h + S.k))) z *
    S.value (qubitsAppendEquiv S.h S.k z).2

/-- The random variable v(A) and its finite-support law: Born-measure act A (zeroKet(h+k)), take the last k wires, and output φ(x). Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.9. -/
def samplerValueLaw (S : CoherentValueSampler) : ℝ → ℝ :=
  fun a => ∑ z, if S.value (qubitsAppendEquiv S.h S.k z).2 = a
    then prob (act (S.A : Matrix _ _ ℂ) (zeroKet (S.h + S.k))) z else 0

/-- Algorithm 1's W preserves x and has flag matrix [[√(1−φ(x)),−√φ(x)],[√φ(x),√(1−φ(x))]]. Source: arxiv-1504.06987v3 PDF p.8. -/
def valueControlledRotation (S : CoherentValueSampler) : Matrix (Qubits S.k × Bool) (Qubits S.k × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then
    match p.2, q.2 with
    | false, false => (Real.sqrt (1 - S.value q.1) : ℂ)
    | false, true => -(Real.sqrt (S.value q.1) : ℂ)
    | true, false => (Real.sqrt (S.value q.1) : ℂ)
    | true, true => (Real.sqrt (1 - S.value q.1) : ℂ)
  else 0

/-- Construct the normalized state ψ=(I_h⊗W)(A⊗I_flag)|0^(h+k+1)⟩ from A and φ, in the source's register order. Source: arxiv-1504.06987v3 PDF p.8; arxiv-1504.06987v3 PDF p.9. -/
def boundedMeanState (S : CoherentValueSampler) : EuclideanSpace ℂ (Qubits (S.h + S.k) × Bool) :=
  WithLp.toLp 2 fun p => (act (S.A : Matrix _ _ ℂ) (zeroKet (S.h + S.k))) p.1 *
    ((if p.2 then Real.sqrt (S.value (qubitsAppendEquiv S.h S.k p.1).2)
      else Real.sqrt (1 - S.value (qubitsAppendEquiv S.h S.k p.1).2)) : ℂ)

/-- The source's U=2|ψ⟩⟨ψ|−I, computed as 2 pureDensity(boundedMeanEstimationState A φ)−I. Source: arxiv-1504.06987v3 PDF p.8; arxiv-1504.06987v3 PDF p.9. -/
def meanEstimationReflection (S : CoherentValueSampler) :
    Matrix (Qubits (S.h + S.k) × Bool) (Qubits (S.h + S.k) × Bool) ℂ :=
  2 • pureDensity (boundedMeanState S) - 1

/-- P=I⊗|1⟩⟨1|: the diagonal projector on the last appended flag being true, on the h+k+1-qubit register. Source: arxiv-1504.06987v3 PDF p.8. -/
def meanFlagProjector (S : CoherentValueSampler) :
    Matrix (Qubits (S.h + S.k) × Bool) (Qubits (S.h + S.k) × Bool) ℂ :=
  Matrix.diagonal fun z => if z.2 then 1 else 0

/-- V=I−2P, derived from meanEstimationFlagProjector, with the source's negative sign on the good/flag-one subspace.. Source: arxiv-1504.06987v3 PDF p.8; arxiv-1504.06987v3 PDF p.9. -/
def meanFlagReflection (S : CoherentValueSampler) :
    Matrix (Qubits (S.h + S.k) × Bool) (Qubits (S.h + S.k) × Bool) ℂ :=
  1 - 2 • meanFlagProjector S

/-- Operational helper boundedMeanSchedule for the source construction. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
def boundedMeanSchedule (t : ℕ) : List ℕ :=
  List.range (t - 1)

/-- Operational helper boundedMeanShotState for the source construction. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
def boundedMeanShotState (S : CoherentValueSampler) (t : ℕ) :
    EuclideanSpace ℂ (Fin t × (Qubits (S.h + S.k) × Bool)) :=
  let Q := meanEstimationReflection S * meanFlagReflection S
  let power : Matrix (Fin t × (Qubits (S.h + S.k) × Bool))
      (Fin t × (Qubits (S.h + S.k) × Bool)) ℂ :=
    ((boundedMeanSchedule t).map fun k => Matrix.of fun p q =>
      if p.1 = q.1 then (if k < (p.1 : ℕ) then Q p.2 q.2
        else (1 : Matrix (Qubits (S.h + S.k) × Bool) (Qubits (S.h + S.k) × Bool) ℂ) p.2 q.2)
      else 0).reverse.prod
  act (Matrix.kronecker (star (qftMatrix t)) 1 * power)
    (tensorVec (uniformState (Fin t)) (boundedMeanState S))

/-- One Algorithm 1 step 3(a) / Theorem 2 execution at any t≥1: uniform Fin t control, controlled powers of Q=U V on ψ, inverse qftMatrix t, control measurement j, and real estimate sin²(πj/t). Source: arxiv-1504.06987v3 PDF p.8. -/
def boundedMeanShot (S : CoherentValueSampler) (t : ℕ) (ht : 1 ≤ t) : Fin t → ℝ :=
  fun j => marginalFst (boundedMeanShotState S t) j

/-- Operational helper boundedMeanRepetitions for the source construction. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
def boundedMeanRepetitions (delta : ℝ) : ℕ := 2 * ⌈100 * Real.log delta⁻¹⌉₊ + 1

/-- Algorithm 1 step 3: r(δ)=2⌈100 log(1/δ)⌉+1 independent shots for 0<δ<1, and the sorted middle real estimate. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8; arxiv-1504.06987v3 PDF p.9. -/
def boundedMeanMedianEstimator (S : CoherentValueSampler) (t : ℕ) (ht : 1 ≤ t) (delta : ℝ)
    (hdelta : 0 < delta ∧ delta < 1) :
    ℝ → ℝ :=
  fun a => ∑ z : Fin (boundedMeanRepetitions delta) → Fin t,
    if realMedian (List.ofFn fun i => Real.sin (Real.pi * (z i : ℕ) / t) ^ 2) = a
    then ∏ i, boundedMeanShot S t ht (z i) else 0

/-- Fresh A|0ⁿ⟩ copies actually consumed by the concrete shot/repetition program: one per shot, hence r(δ). Source: arxiv-1504.06987v3 PDF p.8. -/
def boundedMeanCopyCount (delta : ℝ) : ℕ :=
  (List.replicate (boundedMeanRepetitions delta) 1).sum

/-- Counts computed from the concrete shot/repetition program: r fresh A|0ⁿ⟩ copies and at most rt U invocations, including controlled invocations. Source: arxiv-1504.06987v3 PDF p.8; arxiv-1504.06987v3 PDF p.9. -/
def boundedMeanReflectionCount (t : ℕ) (delta : ℝ) : ℕ :=
  (List.replicate (boundedMeanRepetitions delta) (boundedMeanSchedule t).length).sum

/-- Sanity test. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
example (delta : ℝ) : Odd (boundedMeanRepetitions delta) := by
  exact ⟨⌈100 * Real.log delta⁻¹⌉₊, rfl⟩

/-- Sanity test. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
example (delta : ℝ) : 1 ≤ boundedMeanCopyCount delta := by
  simp [boundedMeanCopyCount, boundedMeanRepetitions]

/-- Sanity test. Source: arxiv-1504.06987v3 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
example (delta : ℝ) : boundedMeanReflectionCount 1 delta = 0 := by
  simp [boundedMeanReflectionCount, boundedMeanSchedule]

/-- Zero observable has zero finite expectation. Source: arxiv-1504.06987v3 PDF pp.8–9. -/
example (S : CoherentValueSampler) (h : S.value = fun _ => 0) : samplerMean S = 0 := by
  simp [samplerMean, h]

end QAlgorithms


