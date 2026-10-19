-- Prove2me | Definitions.Def_QAlgorithms_Defs_CancellationExperiments
-- name    : QAlgorithms_Defs_CancellationExperiments
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:15.775991+00:00
-- url     : https://prove2.me/theorems/fe90cccd-3d38-4570-bfef-6b87e25d1c6f
-- title:
--   CancellationExperiments
-- statement:
--   CancellationExperiments
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CancellationExperiments.lean

import Definitions.Def_QAlgorithms_Defs_FiniteNoisyCircuits
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ProbabilisticCancellation

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.10; arxiv-1612.02058v3 PDF p.11. -/
structure QPR {n m : ℕ} (B : NoisyCircuits.ChannelBasis n m) (L : ℕ)
    (ideal : Matrix.unitaryGroup (Qubits n) ℂ) where
  gamma : ℝ
  gamma_ge : 1 ≤ gamma
  words : PMF (Fin L → Fin m)
  sign : (Fin L → Fin m) → Bool
  represents : ∀ X, conjSuperop (ideal : Matrix _ _ ℂ) X =
    ∑ alpha, ((gamma*(words alpha).toReal*(if sign alpha then 1 else -1) : ℝ) : ℂ) •
      NoisyCircuits.executeWord B.operation (List.ofFn alpha) X

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.10. -/
structure DiagonalReadout (n : ℕ) where
  value : Qubits n → ℝ
  bounded : ∀ z, |value z| ≤ 1

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.10. -/
def circuitExpectation {n m : ℕ} (B : NoisyCircuits.ChannelBasis n m)
    (alpha : List (Fin m)) (A : DiagonalReadout n) : ℝ :=
  effectProb (Matrix.diagonal fun z => (A.value z : ℂ))
    (NoisyCircuits.executeWord B.operation alpha (pureDensity (zeroKet n)))

/-- arxiv-1612.02058v3 PDF p.3. -/
def trialLaw {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal) :
    PMF ((Fin L → Fin m) × Qubits n) :=
  Q.words.bind fun alpha => (NoisyCircuits.computationalReadoutLaw B (List.ofFn alpha)).map
    fun z => (alpha,z)

/-- arxiv-1612.02058v3 PDF p.3. -/
def shotEstimator {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (A : DiagonalReadout n) (trial : (Fin L → Fin m) × Qubits n) : ℝ :=
  Q.gamma*(if Q.sign trial.1 then 1 else -1)*A.value trial.2

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.4. -/
def repeatedLaw {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (M : ℕ) (_hM : 0 < M) :
    (Fin M → (Fin L → Fin m) × Qubits n) → ℝ :=
  fun trials => ∏ i, (trialLaw Q (trials i)).toReal

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.4. -/
def sampleMean {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (A : DiagonalReadout n) (M : ℕ) (_hM : 0 < M)
    (trials : Fin M → (Fin L → Fin m) × Qubits n) : ℝ :=
  (M : ℝ)⁻¹*∑ i, shotEstimator Q A (trials i)

/-- Sanity check for the source model (arxiv-1612.02058v3 PDF p.3). -/
example {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (A : DiagonalReadout n) (trial : (Fin L → Fin m) × Qubits n) :
    sampleMean Q A 1 (by omega) (fun _ => trial) = shotEstimator Q A trial := by simp [sampleMean]

end QAlgorithms.ProbabilisticCancellation


