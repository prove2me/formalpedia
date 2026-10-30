-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16
-- name    : QAlgorithms_Papers_Independent_Bridge50_P16
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:35:35.879312+00:00
-- url     : https://prove2.me/theorems/e0ba6c9b-41cf-4620-9a12-684541b4db55
-- title:
--   Definitions for Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes
-- statement:
--   The objects the formalized statements of *Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes* (arXiv:1801.07271) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `coefficientChannel`: PDF pp.2,14--16: coordinate adapter for the accepted physical Fock map. Nuclear input coefficients have a unique bounded realization; no cutoff is used.
--   - `blockPhotonEnergy`: PDF pp.5,13: extended total photon expectation of an n-mode coefficient array. For a density each summand is nonnegative; infinity is retained.
--   - `EnergyAchievable`: PDF pp.5--7,13: mean-code-state energy constraint for entanglement transmission. Enc(I/2^m) is the actual unconditional encoded state. The same single code works at every logical matrix unit through squared entanglement fidelity.
--   - `energyCapacity`: PDF p.5 Eq.(22): operational supremum, including zero and infinity.
--   - `PhaseIndex`: PDF pp.14--16: interleaved coordinates (q_i,p_i), represented by (i,0),(i,1).
--   - `tensorWeylCharacteristic`: PDF pp.14--16: Tr(rho D((xi_q+i xi_p)/sqrt(2))) on each mode, with actual tensor-product Weyl coefficients. Trace-class pairing includes all inputs.
--   - `GaussianSpecification`: PDF p.2 Eq.(2), Appendix A: physical multimode Gaussian specification. The full characteristic law, CPTP, symmetric noise, and CP matrix condition identify the channel beyond its action on two moments.
--   - `dephasedOperator`: PDF p.5, Eqs.(18)--(22): transport the accepted complete Fock dephasing.
--   - `pureLossIc`: PDF pp.4--5: true pure-loss complement is loss with transmissivity 1-eta. The finite-energy statements below establish that both entropy values are finite.
--   - `oneShotPureLoss`: PDF p.5 Eq.(22): one-shot coherent information on the finite-energy domain.
--   - `optimizedObjective`: PDF p.7 Eq.(41), Appendix C: fixed physical gain substitutions.
--   - `noiseContraction`: PDF p.12 Eq.(64): E Choi wires are logical first, physical second; f_N reverses both indices so the trace contraction has exactly Eq.(63).
--   - `jointObjective`: PDF p.12 Eq.(65): unnormalized real SDP objective. Fidelity divides by d^2.
--   - `encodingEnergy`: PDF pp.12--13 Eq.(67): trace((I_d tensor H) XE), in input-first wires.
--   - `feasibleEncoding`: PDF p.13 Eq.(67): mean energy only for E(I_d/d).
--   - `truncatedKraus`: PDF p.13: exact pure-loss Kraus coefficient on the first n Fock levels. The test m=j+ell prevents truncated natural subtraction outside its domain.
--   - `truncatedLoss`: PDF p.13: actual finite Kraus channel; this is not a noisy truncation rule.
--   - `embedTruncation`: PDF p.13: inclusion of the invariant finite sector into full Fock operators.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, https://arxiv.org/abs/1801.07271v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P51
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

/-!
Noh--Albert--Jiang, arXiv:1801.07271v2. Full Fock channels in Sections II--IV;
finite matrices only in Section V. Every new object belongs to this paper.
Ideal-code and numerical claims deferred in HARD.md have no substitute theorems.
Compilation and independent moderation are pending the separate batch stages.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace B
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad IsTraceClass IsDensity HasFockMatrix
   operatorOfMatrix characteristic displacementMatrix DisplacementRealized
   AmplifierRealized ThermalRealized)
end B

namespace C
export QAlgorithms.Papers.Independent.Claimed50.P39
  (thermal amplifier displacementNoiseChannel photonMeanThermalState
   IsNormalFockChannel FiniteEnergy fockEntropyNats)
end C

namespace T
export QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClassChannel IsTraceClass IsDensity State)
export QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower codeFidelity traceClassAchievableRate
   operationalTraceClassCapacity)
end T

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)
open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- PDF pp.2,14--16: coordinate adapter for the accepted physical Fock map.
Nuclear input coefficients have a unique bounded realization; no cutoff is used. -/
def coefficientChannel (E : B.FockOperator → B.FockOperator) : T.Operation ℕ ℕ :=
  fun X => operatorCoeff (E (boundedOperator X))

/-- PDF pp.5,13: extended total photon expectation of an n-mode coefficient array.
For a density each summand is nonnegative; infinity is retained. -/
def blockPhotonEnergy {n : ℕ} (X : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) : ℝ≥0∞ :=
  ∑' a : Fin n → ℕ, ENNReal.ofReal (∑ i, (a i : ℝ)) * ENNReal.ofReal (X a a).re

/-- PDF pp.5--7,13: mean-code-state energy constraint for entanglement transmission.
Enc(I/2^m) is the actual unconditional encoded state. The same single code works
at every logical matrix unit through squared entanglement fidelity. -/
def EnergyAchievable (E : T.Operation ℕ ℕ) (budget : ℝ) (R : ℝ≥0) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∃ m : ℕ,
      ∃ Enc : T.Operation (Fin (2 ^ m)) (Fin n → ℕ),
      ∃ Dec : T.Operation (Fin n → ℕ) (Fin (2 ^ m)),
        T.IsTraceClassChannel Enc ∧ T.IsTraceClassChannel Dec ∧
        blockPhotonEnergy (Enc (((((2 : ℝ) ^ m)⁻¹ : ℝ) : ℂ) •
          (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ))) ≤ ENNReal.ofReal (n * budget) ∧
        ((R : ℝ) - delta) * (n : ℝ) ≤ (m : ℝ) ∧
        1 - epsilon ≤ T.codeFidelity m (Dec ∘ T.traceClassTensorPower E n ∘ Enc)

/-- PDF p.5 Eq.(22): operational supremum, including zero and infinity. -/
def energyCapacity (E : T.Operation ℕ ℕ) (budget : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ≥0 // EnergyAchievable E budget R}, (R.val : ℝ≥0∞)

/-- PDF pp.14--16: interleaved coordinates (q_i,p_i), represented by (i,0),(i,1). -/
abbrev PhaseIndex (n : ℕ) := Fin n × Fin 2

/-- PDF pp.14--16: Tr(rho D((xi_q+i xi_p)/sqrt(2))) on each mode, with
actual tensor-product Weyl coefficients. Trace-class pairing includes all inputs. -/
def tensorWeylCharacteristic {n : ℕ}
    (X : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) (xi : PhaseIndex n → ℝ) : ℂ :=
  ∑' a : Fin n → ℕ, ∑' b : Fin n → ℕ, X a b *
    ∏ i : Fin n, B.displacementMatrix
      (((xi (i, 0) : ℂ) + Complex.I * (xi (i, 1) : ℂ)) / (Real.sqrt 2 : ℂ)) (b i) (a i)

/-- PDF p.2 Eq.(2), Appendix A: physical multimode Gaussian specification.
The full characteristic law, CPTP, symmetric noise, and CP matrix condition
identify the channel beyond its action on two moments. -/
def GaussianSpecification {n : ℕ}
    (E : T.Operation (Fin n → ℕ) (Fin n → ℕ))
    (M V : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (d : PhaseIndex n → ℝ) : Prop :=
  T.IsTraceClassChannel E ∧ V.transpose = V ∧
    Matrix.PosSemidef ((fun a b => (V a b : ℂ) + Complex.I / 2 *
      ((interleavedSymplecticForm n - M * interleavedSymplecticForm n * M.transpose) a b : ℝ)) :
        Matrix (PhaseIndex n) (PhaseIndex n) ℂ) ∧
    ∀ X, T.IsTraceClass X → ∀ xi,
      tensorWeylCharacteristic (E X) xi =
        tensorWeylCharacteristic X ((interleavedSymplecticForm n * M.transpose * (interleavedSymplecticForm n).transpose).mulVec xi) *
          Complex.exp
            (((-(∑ a, xi a * ((interleavedSymplecticForm n * V * (interleavedSymplecticForm n).transpose).mulVec xi) a) / 2 : ℝ) : ℂ) +
              Complex.I * ((∑ a, d a * ((interleavedSymplecticForm n).mulVec xi) a : ℝ) : ℂ))

/-- PDF p.5, Eqs.(18)--(22): transport the accepted complete Fock dephasing. -/
def dephasedOperator (X : B.FockOperator) : B.FockOperator :=
  B.operatorOfMatrix (QAlgorithms.Papers.Independent.Information100.P51.fockDephasing (operatorCoeff X))

/-- PDF pp.4--5: true pure-loss complement is loss with transmissivity 1-eta.
The finite-energy statements below establish that both entropy values are finite. -/
def pureLossIc (eta : ℝ) (X : B.FockOperator) : ℝ :=
  (C.fockEntropyNats (C.thermal eta 0 X) / ENNReal.ofReal (Real.log 2)).toReal -
    (C.fockEntropyNats (C.thermal (1 - eta) 0 X) / ENNReal.ofReal (Real.log 2)).toReal

/-- PDF p.5 Eq.(22): one-shot coherent information on the finite-energy domain. -/
def oneShotPureLoss (eta budget : ℝ) : ℝ≥0∞ :=
  ⨆ X : {X : B.FockOperator // B.IsDensity X ∧ C.FiniteEnergy X ∧
      (∑' j : ℕ, (j : ℝ) * (X (B.fockKet j) j).re) ≤ budget},
    ENNReal.ofReal (pureLossIc eta X.val)

/-- PDF p.7 Eq.(41), Appendix C: fixed physical gain substitutions. -/
def optimizedObjective (eta b budget gain : ℝ) : ℝ :=
  let etaBar := 1 - (1 - eta) * (b + 1) / gain
  let gain2 := eta / (gain - (1 - eta) * (b + 1))
  let energy2 := gain2 * budget + (gain2 - 1)
  max (thermalEntropyBits (etaBar * energy2) -
    thermalEntropyBits ((1 - etaBar) * energy2)) 0

/-- PDF p.12 Eq.(64): E Choi wires are logical first, physical second;
f_N reverses both indices so the trace contraction has exactly Eq.(63). -/
def noiseContraction {d n : ℕ} (N : Superop (Fin n) (Fin n))
    (XE : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) :
    Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ :=
  fun a b => ∑ k : Fin n, ∑ kp : Fin n,
    choi N (k, b.1) (kp, a.1) * XE (b.2, k) (a.2, kp)

/-- PDF p.12 Eq.(65): unnormalized real SDP objective. Fidelity divides by d^2. -/
def jointObjective {d n : ℕ} (N : Superop (Fin n) (Fin n))
    (XE : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ)
    (XD : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ) : ℝ :=
  (XD * noiseContraction N XE).trace.re

/-- PDF pp.12--13 Eq.(67): trace((I_d tensor H) XE), in input-first wires. -/
def encodingEnergy {d n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (XE : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) : ℝ :=
  ((Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) H) * XE).trace.re

/-- PDF p.13 Eq.(67): mean energy only for E(I_d/d). -/
def feasibleEncoding (d n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (budget : ℝ) :
    Set (Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) :=
  {XE | CPTP XE ∧ encodingEnergy H XE ≤ budget * d}

/-- PDF p.13: exact pure-loss Kraus coefficient on the first n Fock levels.
The test m=j+ell prevents truncated natural subtraction outside its domain. -/
def truncatedKraus (n : ℕ) (eta : ℝ) (ell : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun j m => if m.val = j.val + ell.val then
    (Real.sqrt (Nat.choose m.val ell.val : ℝ) *
      Real.sqrt (1 - eta) ^ ell.val * Real.sqrt eta ^ j.val : ℝ) else 0

/-- PDF p.13: actual finite Kraus channel; this is not a noisy truncation rule. -/
def truncatedLoss (n : ℕ) (eta : ℝ) : Superop (Fin n) (Fin n) :=
  krausApply (truncatedKraus n eta)

/-- PDF p.13: inclusion of the invariant finite sector into full Fock operators. -/
def embedTruncation {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : B.FockOperator :=
  ∑ i : Fin n, ∑ j : Fin n, X i j • B.fockDyad i.val j.val

example : interleavedSymplecticForm 1 (0, 0) (0, 1) = 1 := by simp [interleavedSymplecticForm]

example : interleavedSymplecticForm 1 (0, 1) (0, 0) = -1 := by simp [interleavedSymplecticForm]

example {n : ℕ} : blockPhotonEnergy (0 : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) = 0 := by
  simp [blockPhotonEnergy]

example {n : ℕ} (N : Superop (Fin n) (Fin n)) :
    noiseContraction (d := 1) N 0 = 0 := by
  ext a b
  simp [noiseContraction]

example {n : ℕ} : embedTruncation (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [embedTruncation]

example (eta : ℝ) : truncatedKraus 1 eta 0 0 0 = 1 := by
  simp [truncatedKraus]

example (X : B.FockOperator) : C.displacementNoiseChannel 0 X = X := by
  simp [C.displacementNoiseChannel]

end QAlgorithms.Papers.Independent.Bridge50.P16


