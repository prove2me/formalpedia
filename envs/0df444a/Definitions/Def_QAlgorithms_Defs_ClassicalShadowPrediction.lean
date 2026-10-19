-- Prove2me | Definitions.Def_QAlgorithms_Defs_ClassicalShadowPrediction
-- name    : QAlgorithms_Defs_ClassicalShadowPrediction
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:27.584822+00:00
-- url     : https://prove2.me/theorems/e917a3e6-0619-4025-a377-ee9abee7887d
-- title:
--   ClassicalShadowPrediction
-- statement:
--   ClassicalShadowPrediction
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ClassicalShadowPrediction.lean

import Definitions.Def_QAlgorithms_Defs_ClassicalShadowChannels
import Definitions.Def_QAlgorithms_Defs_SamplingUtilities
noncomputable section

open MeasureTheory
open scoped Matrix ENNReal

namespace QAlgorithms.ClassicalShadows

variable {n m d k b w M K N c out : ℕ}

/-- Actual joint unitary/Born-outcome law, 2002.08953 p.11 Eqs.(S1)–(S3).
Unitaries follow the ensemble; computational outcomes are conditional Born draws. -/
def oneShotLaw (P : MeasurementPrimitive n) (rho : Space n) (hrho : IsDensityMatrix rho) :
    Measure (Matrix.unitaryGroup (Qubits n) ℂ × Qubits n) :=
  ∑ b : Qubits n,
    (P.ensemble.withDensity (fun U => ENNReal.ofReal
      (((U : Space n) * rho * star (U : Space n)) b b).re)).map (fun U => (U, b))

/-- K independent batches of N independent shots (2002.08953 pp.3,12–13). -/
def arrayLaw (P : MeasurementPrimitive n) (rho : Space n) (hrho : IsDensityMatrix rho) (K N : ℕ) :
    Measure (Fin K × Fin N → Matrix.unitaryGroup (Qubits n) ℂ × Qubits n) :=
  Measure.pi fun _ => oneShotLaw P rho hrho

/-- Traceless observable part, 2002.08953 p.12 Eq.(S8). -/
def tracelessPart (O : Space n) : Space n :=
  O - (O.trace / ((2 : ℂ) ^ n)) • 1

/-- Centering preserves the Hermitian observable domain,
2002.08953 p.12 Eq.(S8). -/
theorem tracelessPart_hermitian (O : Space n) (hO : O.IsHermitian) :
    (tracelessPart O).IsHermitian := by
  have ht : star O.trace = O.trace := by
    rw [← Matrix.trace_conjTranspose,hO.eq]
  unfold tracelessPart
  change (O-(O.trace/(2:ℂ)^n) • 1)ᴴ = O-(O.trace/(2:ℂ)^n) • 1
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,hO.eq]
  simp [ht]

/-- Primitive-dependent worst-state second-moment norm, 2002.08953 p.12
Eq.(S7). The supremum ranges over all density matrices. -/
def shadowNorm (P : MeasurementPrimitive n) (O : Space n) (hO : O.IsHermitian) : ℝ :=
  Real.sqrt (sSup {v | ∃ sigma : Space n, IsDensityMatrix sigma ∧
    v = ∫ U, ∑ b : Qubits n,
      (((U : Space n) * sigma * star (U : Space n)) b b).re *
        (((U : Space n) * inverseChannel P O * star (U : Space n)) b b).re ^ 2 ∂P.ensemble})

/-- Median of the K batch means, 2002.08953 p.12 Eq.(S12).
N,K are positive; the frozen lower median implements the permitted even case. -/
def medianOfMeans (P : MeasurementPrimitive n) (O : Space n)
    (K N : ℕ) (hK : 0 < K) (hN : 0 < N)
    (shots : Fin K × Fin N → Matrix.unitaryGroup (Qubits n) ℂ × Qubits n) : ℝ :=
  realMedian (List.ofFn fun k : Fin K => (N : ℝ)⁻¹ *
    ∑ j : Fin N, (O * snapshot P (shots (k,j)).1 (shots (k,j)).2).trace.re)

/-- Integer sample schedule (2002.08953 pp.12–13 Eq.(S13)).
At least one sample per batch avoids empty means for scalar observables. -/
def sampleSchedule (P : MeasurementPrimitive n) (O : Fin M → Space n)
    (hO : ∀ i, (O i).IsHermitian) (hM : 0 < M) (eps delta : ℝ) (heps : 0 < eps ∧ eps ≤ 1)
    (hdelta : 0 < delta ∧ delta ≤ 1) : ℕ × ℕ :=
  let V := Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0,hM⟩⟩)
    (fun i => shadowNorm P (tracelessPart (O i)) (tracelessPart_hermitian (O i) (hO i)) ^ 2)
  (⌈2 * Real.log (2 * (M : ℝ) / delta)⌉₊, max 1 ⌈34 * V / eps ^ 2⌉₊)

/-- Sanity check for the modeled source objects (arxiv-2002.08953v2, PDF pp.3,11,12,13). -/
example (O : Space n) : (tracelessPart O).trace = 0 := by
  simp [tracelessPart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Sanity check for the modeled source objects (arxiv-2002.08953v2, PDF pp.3,11,12,13). -/
example (P : MeasurementPrimitive n)
    (shots : Fin 1 × Fin 1 → Matrix.unitaryGroup (Qubits n) ℂ × Qubits n) :
    medianOfMeans P 0 1 1 (by decide) (by decide) shots = 0 := by
  simp [medianOfMeans, realMedian]

end QAlgorithms.ClassicalShadows


