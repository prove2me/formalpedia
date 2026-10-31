-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P75
-- name    : QAlgorithms_Papers_Independent_Intake100_P75
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:00:37.789523+00:00
-- url     : https://prove2.me/theorems/35c24644-8431-4d91-ac81-d52e457330e8
-- title:
--   Definitions for Inseparability criterion for continuous variable systems
-- statement:
--   The objects the formalized statements of *Inseparability criterion for continuous variable systems* (arXiv:quant-ph/9908056) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pairedKernel`: PDF pp.1--2, (1): basis relabeling between the two full oscillator spaces. The two natural occupations are retained without a cutoff.
--   - `eprImage`: PDF p.1, (2): coefficients of |a| X1+X2/a and |a| P1-P2/a. The combinations are formed before imposing their maximal operator domains. Both signs of the real gain are retained; the theorems exclude a=0.
--   - `centeredEprForm`: PDF pp.1--2: extended centered quadratic form of the canonical EPR observable. The nonnegative series is infinity off the maximal domain, rather than a zero-valued nonsummable complex series.
--   - `varianceOfForm`: PDF pp.1--2, (3)--(4): mixed-state variance as the least centered second moment. A positive observable form has the same expectation in every normalized pure-state ensemble of a density. Taking the infimum over all such ensembles therefore implements its trace expectation, including infinity. The ensembles are unrestricted probability measures with the actual operator barycenter; no product decomposition, finite energy, or Gaussianity is assumed. The extended empty infimum is infinity. Every normalized density has a spectral ensemble.
--   - `eprTotalVariance`: PDF pp.1--2, (3): total extended variance of the two canonical EPR operators.
--   - `tensorUnitaryKernel`: PDF p.2: kernel of the genuine tensor product of arbitrary local unitaries. A one-mode occupation is written as Fin 1 -> N, compatibly with the frozen Gaussian-unitary interface.
--   - `tensorImageCoefficients`: PDF p.2: actual local-unitary image coefficients on the full two-mode space.
--   - `tensorImage`: PDF p.2: completed tensor-unitary image. Physical unitaries always give square-summable coefficients; realization is expressly included in the local unitary theorem, so the off-domain fallback is not treated as an observable.
--   - `transportedEprForm`: PDF p.2: form of U A U-adjoint, including transport of its unbounded domain. It is evaluated at U-adjoint psi, while the tested density remains fixed.
--   - `localCanonicalMatrix`: PDF p.3, (9): active block-diagonal phase-space matrix of two local LLUBOs.
--   - `coherentProductKernel`: PDF pp.4--5, (19): coherent product projector at the physical mean x. D((x_q+i x_p)/sqrt(2)) applied to the vacuum has these coefficients.
--   - `transmissivity`: PDF p.5: intensity transmissivity for damping rate eta and finite time t.
--   - `thermalBeam`: PDF p.5, independent thermal noise: real beam splitter for a system and its environment. For 0<=tau<=1 this is a unitary matrix with system amplitude sqrt(tau); the reflected bath amplitude is sqrt(1-tau).
--   - `thermalBeamKernel`: PDF p.5, thermal transmission: second quantization of the physical splitter, using the accepted finite occupation polynomial on every number ket.
--   - `oscillatorThermalAttenuator`: PDF p.5: actual local thermal attenuator, computed by appending an independent Gibbs density, conjugating by the number-preserving beam splitter and tracing out the environment. It is a map of every input kernel, not a prescribed output covariance. Only tau in [0,1] and finite nbar>=0 are used in source statements. This full oscillator map is distinct from the frozen Information100.P08.thermalChannel, whose input and output are qubits (Fin 2), not oscillator occupations (Nat).
--   - `independentChannels`: PDF p.5: independent application of two local channels to the bipartite kernel; off-diagonal input blocks are retained.
--   - `thermalOutput`: PDF p.5: transmission of the printed exp[-r(a1†a2†-a1a2)] vacuum. The accepted positive-r vector has the opposite sign, so the input is -r. No desired covariance or separability property is used to define this output.
--   - `thermalLifetime`: PDF p.5, (20): finite entanglement-death threshold, used only for eta,nbar>0. Zero temperature has its own theorem and is never evaluated through this division.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, https://arxiv.org/abs/quant-ph/9908056v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

/-!
Duan--Giedke--Cirac--Zoller, quant-ph/9908056v2, PDF pp.1--5.
Full completed oscillator spaces, hbar=1, vacuum variance 1/2 and full
anticommutator covariance I. Accepted paper modules supply frozen definitions.
The unrestricted standard-II lemma and prescribed-gain theorem are deferred:
the printed ratios have no specified boundary meaning. No boundary restriction
is silently added. Compilation and independent moderation are pending.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P75

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable IsBarycenter rankOne productCoeff)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl CharacteristicSummable multimodeWeylTrace
   covarianceCharacteristicValue)
open QAlgorithms.Papers.Independent.Next46.P45
  (TwoMode PureVector Decomposes ladderCoefficients squeezedVector
   squeezedCoefficients GaussianShiftLaw shiftArgument)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel partialRight)
open QAlgorithms.Papers.Independent.Frontier18.P14 (occupationOutput)
open QAlgorithms.Papers.Independent.Gap48.P26 (thermalKernel)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF pp.1--2, (1): basis relabeling between the two full oscillator spaces.
The two natural occupations are retained without a cutoff. -/
def pairedKernel (rho : DensityKernel 2) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => rho ![i.1, i.2] ![j.1, j.2]

/-- PDF p.1, (2): coefficients of |a| X1+X2/a and |a| P1-P2/a.
The combinations are formed before imposing their maximal operator domains.
Both signs of the real gain are retained; the theorems exclude a=0. -/
def eprImage (momentum : Bool) (a : ℝ) (psi : TwoMode)
    (i : FockIndex 2) : ℂ :=
  if momentum then
    (Complex.I / (Real.sqrt 2 : ℂ)) *
      (((|a| : ℝ) : ℂ) * (ladderCoefficients true 0 psi i - ladderCoefficients false 0 psi i) -
       (a : ℂ)⁻¹ * (ladderCoefficients true 1 psi i - ladderCoefficients false 1 psi i))
  else (1 / (Real.sqrt 2 : ℂ)) *
    (((|a| : ℝ) : ℂ) * (ladderCoefficients true 0 psi i + ladderCoefficients false 0 psi i) +
     (a : ℂ)⁻¹ * (ladderCoefficients true 1 psi i + ladderCoefficients false 1 psi i))

/-- PDF pp.1--2: extended centered quadratic form of the canonical EPR observable.
The nonnegative series is infinity off the maximal domain, rather than a
zero-valued nonsummable complex series. -/
def centeredEprForm (momentum : Bool) (a center : ℝ) (psi : TwoMode) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Complex.normSq (eprImage momentum a psi i - (center : ℂ) * psi i))

/-- PDF pp.1--2, (3)--(4): mixed-state variance as the least centered second
moment. A positive observable form has the same expectation in every normalized
pure-state ensemble of a density. Taking the infimum over all such ensembles
therefore implements its trace expectation, including infinity. The ensembles
are unrestricted probability measures with the actual operator barycenter;
no product decomposition, finite energy, or Gaussianity is assumed. The extended
empty infimum is infinity. Every normalized density has a spectral ensemble. -/
def varianceOfForm (form : ℝ → TwoMode → ℝ≥0∞) (rho : DensityKernel 2) : ℝ≥0∞ :=
  ⨅ center : ℝ,
    ⨅ mu : {mu : Measure PureVector // Decomposes mu rho},
      ∫⁻ psi, form center psi.val ∂mu.val

/-- PDF pp.1--2, (3): total extended variance of the two canonical EPR operators. -/
def eprTotalVariance (rho : DensityKernel 2) (a : ℝ) : ℝ≥0∞ :=
  varianceOfForm (centeredEprForm false a) rho +
    varianceOfForm (centeredEprForm true a) rho

/-- PDF p.2: kernel of the genuine tensor product of arbitrary local unitaries.
A one-mode occupation is written as Fin 1 -> N, compatibly with the frozen
Gaussian-unitary interface. -/
def tensorUnitaryKernel
    (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1)) : DensityKernel 2 :=
  fun i j => unitaryCoeff U (fun _ => i 0) (fun _ => j 0) *
    unitaryCoeff V (fun _ => i 1) (fun _ => j 1)

/-- PDF p.2: actual local-unitary image coefficients on the full two-mode space. -/
def tensorImageCoefficients
    (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1)) (psi : TwoMode)
    (i : FockIndex 2) : ℂ :=
  ∑' j, tensorUnitaryKernel U V i j * psi j

/-- PDF p.2: completed tensor-unitary image. Physical unitaries always give
square-summable coefficients; realization is expressly included in the local
unitary theorem, so the off-domain fallback is not treated as an observable. -/
def tensorImage
    (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1)) (psi : TwoMode) : TwoMode :=
  if h : Memℓp (tensorImageCoefficients U V psi) 2 then
    ⟨tensorImageCoefficients U V psi, h⟩ else 0

/-- PDF p.2: form of U A U-adjoint, including transport of its unbounded domain.
It is evaluated at U-adjoint psi, while the tested density remains fixed. -/
def transportedEprForm
    (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1))
    (momentum : Bool) (a center : ℝ) (psi : TwoMode) : ℝ≥0∞ :=
  centeredEprForm momentum a center (tensorImage U.symm V.symm psi)

/-- PDF p.3, (9): active block-diagonal phase-space matrix of two local LLUBOs. -/
def localCanonicalMatrix (U V : AffineMultimodeGaussianUnitary 1) : Cov 2 :=
  fun i j => if i.1 = j.1 then
    (if i.1 = 0 then U.symplecticMatrix (0, i.2) (0, j.2)
     else V.symplecticMatrix (0, i.2) (0, j.2)) else 0

/-- PDF pp.4--5, (19): coherent product projector at the physical mean x.
D((x_q+i x_p)/sqrt(2)) applied to the vacuum has these coefficients. -/
def coherentProductKernel (x : (Fin 2 × Fin 2) → ℝ) : DensityKernel 2 :=
  fun i j => productWeyl (shiftArgument x) i (fun _ => 0) *
    star (productWeyl (shiftArgument x) j (fun _ => 0))

/-- PDF p.5: intensity transmissivity for damping rate eta and finite time t. -/
def transmissivity (eta t : ℝ) : ℝ := Real.exp (-2 * eta * t)

/-- PDF p.5, independent thermal noise: real beam splitter for a system and
its environment. For 0<=tau<=1 this is a unitary matrix with system amplitude
sqrt(tau); the reflected bath amplitude is sqrt(1-tau). -/
def thermalBeam (tau : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt tau : ℂ), (Real.sqrt (1 - tau) : ℂ);
     -(Real.sqrt (1 - tau) : ℂ), (Real.sqrt tau : ℂ)]

/-- PDF p.5, thermal transmission: second quantization of the physical splitter,
using the accepted finite occupation polynomial on every number ket. -/
def thermalBeamKernel (tau : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => occupationOutput (thermalBeam tau) j.1 j.2 i

/-- PDF p.5: actual local thermal attenuator, computed by appending an independent
Gibbs density, conjugating by the number-preserving beam splitter and tracing
out the environment. It is a map of every input kernel, not a prescribed output
covariance. Only tau in [0,1] and finite nbar>=0 are used in source statements.
This full oscillator map is distinct from the frozen Information100.P08.thermalChannel,
whose input and output are qubits (Fin 2), not oscillator occupations (Nat). -/
def oscillatorThermalAttenuator (tau nbar : ℝ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  partialRight (conjugateKernel (thermalBeamKernel tau)
    (productCoeff X (thermalKernel nbar)))

/-- PDF p.5: independent application of two local channels to the bipartite
kernel; off-diagonal input blocks are retained. -/
def independentChannels
    (Phi Psi : Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ)
    (rho : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => Phi (fun a b => Psi (fun c d => rho (a, c) (b, d)) i.2 j.2) i.1 j.1

/-- PDF p.5: transmission of the printed exp[-r(a1†a2†-a1a2)] vacuum.
The accepted positive-r vector has the opposite sign, so the input is -r.
No desired covariance or separability property is used to define this output. -/
def thermalOutput (r eta nbar t : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  let Phi := oscillatorThermalAttenuator (transmissivity eta t) nbar
  independentChannels Phi Phi (pairedKernel (rankOne (squeezedVector (-r))))

/-- PDF p.5, (20): finite entanglement-death threshold, used only for eta,nbar>0.
Zero temperature has its own theorem and is never evaluated through this division. -/
def thermalLifetime (r eta nbar : ℝ) : ℝ :=
  Real.log (1 + (1 - Real.exp (-2 * r)) / (2 * nbar)) / (2 * eta)

/-! Sanity checks for new definitions; no source theorem is proved here. -/

example (rho : DensityKernel 2) : pairedKernel rho (0, 1) (2, 3) = rho ![0, 1] ![2, 3] := rfl

example (momentum : Bool) (a center : ℝ) : centeredEprForm momentum a center 0 = 0 := by
  simp [centeredEprForm, eprImage, ladderCoefficients]

example (rho : DensityKernel 2) :
    varianceOfForm (fun _ _ => (⊤ : ℝ≥0∞)) rho = ⊤ := by
  simp only [varianceOfForm]
  have cost (mu : {mu : Measure PureVector // Decomposes mu rho}) :
      (∫⁻ _ : PureVector, (⊤ : ℝ≥0∞) ∂mu.val) = ⊤ := by
    letI : IsProbabilityMeasure mu.val := mu.property.1
    simp
  simp only [cost, iInf_top]

example (rho : DensityKernel 2) (a : ℝ) :
    eprTotalVariance rho a = varianceOfForm (centeredEprForm false a) rho +
      varianceOfForm (centeredEprForm true a) rho := rfl

example (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1)) :
    tensorImageCoefficients U V 0 = 0 := by
  funext i
  simp [tensorImageCoefficients]

example (U V : Hilbert (FockIndex 1) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1))
    (momentum : Bool) (a center : ℝ) (psi : TwoMode) :
    transportedEprForm U V momentum a center psi =
      centeredEprForm momentum a center (tensorImage U.symm V.symm psi) := rfl

example (U V : AffineMultimodeGaussianUnitary 1) :
    localCanonicalMatrix U V (0, 0) (1, 0) = 0 := by
  simp [localCanonicalMatrix]

example (x : (Fin 2 × Fin 2) → ℝ) (i : FockIndex 2) :
    coherentProductKernel x i i =
      productWeyl (shiftArgument x) i (fun _ => 0) *
        star (productWeyl (shiftArgument x) i (fun _ => 0)) := rfl

example (eta : ℝ) : transmissivity eta 0 = 1 := by simp [transmissivity]

example : thermalBeam 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [thermalBeam]

example (tau : ℝ) : thermalBeamKernel tau (0, 0) (0, 0) = 1 := by
  simp [thermalBeamKernel, QAlgorithms.Papers.Independent.Dependency50.P34.fockOutput,
    QAlgorithms.Papers.Independent.Dependency50.P34.fockKet]

example (tau nbar : ℝ) : oscillatorThermalAttenuator tau nbar 0 = 0 := by
  funext i j
  simp [oscillatorThermalAttenuator, partialRight, conjugateKernel, productCoeff]

example (r eta : ℝ) : thermalLifetime 0 eta r = 0 := by simp [thermalLifetime]

example (rho : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) :
    independentChannels id id rho = rho := rfl

end QAlgorithms.Papers.Independent.Intake100.P75


