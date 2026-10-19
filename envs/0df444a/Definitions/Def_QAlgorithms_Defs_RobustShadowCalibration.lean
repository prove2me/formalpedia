-- Prove2me | Definitions.Def_QAlgorithms_Defs_RobustShadowCalibration
-- name    : QAlgorithms_Defs_RobustShadowCalibration
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:53.718934+00:00
-- url     : https://prove2.me/theorems/aaf994b7-33d4-465d-855a-da916af4ecaa
-- title:
--   RobustShadowCalibration
-- statement:
--   RobustShadowCalibration
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\RobustShadowCalibration.lean

import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_SamplingUtilities
noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.RobustShadow

/-- Computational-basis dephasing, rather than an ideal or noisy twirl
(2011.09636 p.2; p.18, Eq.(B1)). -/
def dephase {n : ℕ} (X : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ := Matrix.diagonal fun b => X b b

/-- Mean survival probability of computational-basis probes for one fixed CPTP noise map
(2011.09636 p.19, Eq.(B3)). Informative fidelity is a theorem restriction, not assumed here. -/
def zFidelity {n : ℕ} (Lambda : Superop (Qubits n) (Qubits n))
    (_lawful : IsChannel Lambda) : ℝ :=
  ((2 : ℝ)^n)⁻¹*∑ b : Qubits n, (Lambda (pureDensity (ket b)) b b).re

/-- The computed traceless-sector factor, with n positive so d²-1 is nonzero
(2011.09636 p.19, Eq.(B3)). Equality to the twirl is not a defining premise. -/
def pauliFidelity {n : ℕ} (_hn : 0 < n) (Lambda : Superop (Qubits n) (Qubits n))
    (lawful : IsChannel Lambda) : ℝ :=
  ((2 : ℝ)^n*zFidelity Lambda lawful-1)/((2 : ℝ)^(2*n)-1)

/-- Single-shot decoder from the ideal recorded Clifford amplitude, even when its
outcome was measured with noise (2011.09636 p.4, Eq.(11); p.18, Protocol 1).
A full-normalizer representative is accepted; its global phase cancels in prob. -/
def noiseEstimate {n : ℕ} (_hn : 0 < n) (U : Clifford.normalizer n) (b : Qubits n) : ℝ :=
  ((2 : ℝ)^n*prob (act (U.val : Matrix (Qubits n) (Qubits n) ℂ) (zeroKet n)) b-1)/
    ((2 : ℝ)^n-1)

/-- Median of K batch means of N computed single-shot decoders
(2011.09636 p.18, Protocol 1; p.22, Eq.(B21)). The frozen lower-median convention
is used. N and K are positive; no noise parameter enters the decoder. -/
def calibrationEstimate {n N K : ℕ} (hn : 0 < n) (_hN : 0 < N) (_hK : 0 < K)
    (record : Fin K × Fin N → Clifford.normalizer n × Qubits n) : ℝ :=
  realMedian (List.ofFn fun k : Fin K => (N : ℝ)⁻¹*
    ∑ i : Fin N, noiseEstimate hn (record (k,i)).1 (record (k,i)).2)

example {n : ℕ} : dephase (0 : Matrix (Qubits n) (Qubits n) ℂ) = 0 := by
  ext b c
  simp [dephase,Matrix.diagonal_apply]

example {n : ℕ} (X : Matrix (Qubits n) (Qubits n) ℂ) (b : Qubits n) :
    dephase X b b = X b b := by simp [dephase]

example (lawful : IsChannel (id : Superop (Qubits 1) (Qubits 1))) :
    pauliFidelity (by decide) id lawful = 1/3 := by
  norm_num [pauliFidelity,zFidelity,pureDensity,ket]


/-- Joint record weights from uniform global Clifford choice followed by the
actual fixed CPTP noise and computational-basis measurement. These are the
unmodified source probabilities, without re-normalization
(2011.09636 pp.2-4,16,18-19). -/
def shotLaw {n : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (Lambda : Superop (Qubits n) (Qubits n)) (_lawful : IsChannel Lambda)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (_density : IsDensityMatrix rho) :
    Clifford.ProjectiveGroup n × Qubits n → ℝ :=
  fun Ub => (Clifford.uniformGlobalEnsemble n Ub.1).toReal *
    (Lambda (conjSuperop ((Clifford.representative Ub.1).val : Matrix _ _ ℂ) rho) Ub.2 Ub.2).re

/-- Noisy twirl computed from the same fixed noise map and the complete global
ensemble. Its depolarizing form is a consequence, not a defining field
(2011.09636 pp.3-4,18, Eqs.(9),(B1)). -/
def noisyTwirl {n : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (Lambda : Superop (Qubits n) (Qubits n)) (_lawful : IsChannel Lambda) :
    Superop (Qubits n) (Qubits n) :=
  fun X => ∑ U : Clifford.ProjectiveGroup n,
    ((Clifford.uniformGlobalEnsemble n U).toReal : ℂ) •
      conjSuperop (star ((Clifford.representative U).val : Matrix _ _ ℂ))
        (dephase (Lambda (conjSuperop ((Clifford.representative U).val : Matrix _ _ ℂ) X)))

/-- Discrete record sigma-algebra, for the finite global projective labels
(2011.09636 p.18, Protocol 1). -/
instance recordMeasurable (n : ℕ) :
    MeasurableSpace (Clifford.ProjectiveGroup n × Qubits n) := ⊤

/-- Independent calibration records from a perfectly prepared zero probe.
The measure uses the actual shot weights and has exactly N*K positions
(2011.09636 pp.18-19,22). Probability normalization is supporting legality work. -/
def calibrationLaw {n N K : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (_hn : 0 < n) (_hN : 0 < N) (_hK : 0 < K)
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda) :
    MeasureTheory.Measure (Fin K × Fin N → Clifford.ProjectiveGroup n × Qubits n) :=
  MeasureTheory.Measure.pi fun _ =>
    ∑ Ub : Clifford.ProjectiveGroup n × Qubits n,
      ENNReal.ofReal (shotLaw Lambda lawful (pureDensity (zeroKet n))
        (by
          constructor
          · exact Matrix.posSemidef_vecMulVec_self_star _
          · simp [pureDensity,zeroKet,ket,Matrix.trace,Matrix.diag]) Ub) • MeasureTheory.Measure.dirac Ub

example {n : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (Lambda : Superop (Qubits n) (Qubits n)) (h : IsChannel Lambda) :
    noisyTwirl Lambda h 0 = 0 := by
  obtain ⟨m,E,_,hE⟩ := h
  have hz : Lambda 0 = 0 := by rw [hE]; simp [krausApply]
  simp [noisyTwirl,conjSuperop,dephase,hz]

end QAlgorithms.RobustShadow


