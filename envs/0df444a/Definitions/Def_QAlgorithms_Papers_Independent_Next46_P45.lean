-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45
-- name    : QAlgorithms_Papers_Independent_Next46_P45
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T15:46:39.081441+00:00
-- url     : https://prove2.me/theorems/325cc3bc-58ef-4af6-8688-cb21a97f16e5
-- title:
--   Definitions for Entanglement of formation for symmetric Gaussian states
-- statement:
--   The objects the formalized statements of *Entanglement of formation for symmetric Gaussian states* (arXiv:quant-ph/0304042) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TwoMode`: PDF p.1: the complete two-mode oscillator space, with occupation coordinates.
--   - `PureVector`: PDF p.1: all normalized pure vectors, including infinite-energy vectors.
--   - `firstReduction`: PDF p.2, (6): reduced density of the FIRST oscillator, from the actual vector.
--   - `pureEntanglement`: PDF p.2, (6), note [19]: actual spectral entropy of the reduction in bits. The extended value retains infinite entropy; it is not a covariance formula.
--   - `ladderCoefficients`: PDF p.1: ladder coefficients on the full space, with explicit vacuum boundary. This raw sequence need not be square summable and is not a total bounded operator.
--   - `eprCoefficients`: PDF p.1, (2): coefficients of X_A-X_B or P_A+P_B. The combinations are formed BEFORE checking their domains, allowing cancellation of unbounded terms.
--   - `eprVariance`: PDF p.1, (2): maximal oscillator quadrature domain; variance is infinity outside the domain. On the domain the expectation is real and the norm is finite.
--   - `eprUncertainty`: PDF p.1, (2): clipping takes place in the extended nonnegative reals, so an infinite variance gives exactly one, rather than toReal(infinity)=0.
--   - `squeezingAt`: PDF p.2, (4): natural logarithm, distinct from base-two entropy.
--   - `squeezedCoefficients`: PDF p.1, (1): normalized Fock coefficients, continuously extended to r=0.
--   - `squeezedVector`: PDF pp.1–2, (1): the actual l2 vector. The fallback is unused for r>=0; normalization and membership are conclusions of squeezed_state_identities.
--   - `SchmidtClass`: PDF p.2: the sequence class C, with actual l2 normalization and monotonicity.
--   - `sequenceUncertainty`: PDF p.2, (7) and its proof: the nonnegative difference-square series, equal to (7) on C. This does not subtract divergent number expectations.
--   - `sequenceEntropy`: PDF p.2, (6): extended Shannon entropy of squared Schmidt coefficients in bits.
--   - `geometricCoefficients`: PDF pp.1–3, (1),(3),(4): the geometric coefficients selected by the EPR level. This corrects the printed exp(-N r_Delta) parameter mismatch in Lemma 2.
--   - `IsGeometric`: PDF p.3, Lemma 2: normalized geometric sequences are identified within C, not by a freely chosen Lagrange-multiplier parameter.
--   - `xlog2x`: PDF pp.2,4: x log_2 x with the explicit zero convention.
--   - `formationCoefficient`: PDF pp.3–4, (17): c-plus/minus, used only for delta>0.
--   - `gaussianFormationBits`: PDF pp.3–4, (17): the paper's f, in bits and on 0<delta<=1. Distinct from the imported Adesso–Datta f (different argument, nats), and from Information100.P08.formationFunction (qubit concurrence, value 1 at argument 1). Here the EPR argument 1 is vacuum and the value is 0; those are different concepts.
--   - `symmetricEprLevel`: PDF p.3, (14): full product under the radical, clipped for the separable branch.
--   - `Decomposes`: PDF p.3, (15): all probability ensembles of normalized pure vectors with this barycenter. Scalar integrability prevents default-zero Bochner integrals. The Borel structure comes from the full Hilbert norm; no Gaussian restriction.
--   - `ensembleCost`: PDF p.3, (16): average actual pure-state entanglement, including infinity.
--   - `entanglementOfFormation`: PDF p.3, (15)–(16): unrestricted entanglement of formation. Both countable and continuous ensembles are included. The extended empty infimum is infinity.
--   - `shiftArgument`: PDF p.3: D(z) shifts the first moments by x when z=(x_q+i x_p)/sqrt(2). This differs from the dual Weyl argument v used in a characteristic function.
--   - `shiftedCoefficients`: PDF p.3, D_0: actual displaced pure-vector coefficients.
--   - `localSeedCoefficients`: PDF p.3: local unitary images of the specific squeezed seed, in full Fock space.
--   - `GaussianShiftLaw`: PDF p.3: singular Gaussian displacement law described by its characteristic function. G is the full anticommutator residual: the classical covariance is G/2. No inverse or Lebesgue density is required, including G=0 (a Dirac mass).
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, https://arxiv.org/abs/quant-ph/0304042v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

/-!
Giedke et al., quant-ph/0304042v1. Full two-mode Fock space, hbar=1,
full anticommutator covariance, entropy in bits, no photon cutoff.
Accepted paper modules are imported as pinned definition providers, as authorized
by the independent-paper workflow. No source theorem is assumed as a hypothesis.
Compilation and independent moderation are pending the batch handoff.
- boundary correction: Proposition 2 uses f(min(1,d)), since f has domain (0,1].
- printed Lemma 2's exp(-N r_Delta) is corrected to tanh(r_Delta)^N using (1),(3),(4).
- the displacement ensemble is a probability law, allowing singular covariance.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)
open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

/-- PDF p.1: the complete two-mode oscillator space, with occupation coordinates. -/
abbrev TwoMode := Hilbert (Fin 2 → ℕ)

/-- PDF p.1: all normalized pure vectors, including infinite-energy vectors. -/
abbrev PureVector := {psi : TwoMode // ‖psi‖ = 1}

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.2, (6): reduced density of the FIRST oscillator, from the actual vector. -/
def firstReduction (psi : TwoMode) : Matrix ℕ ℕ ℂ :=
  fun m n => ∑' k : ℕ, psi ![m, k] * star (psi ![n, k])

/-- PDF p.2, (6), note [19]: actual spectral entropy of the reduction in bits.
The extended value retains infinite entropy; it is not a covariance formula. -/
def pureEntanglement (psi : TwoMode) : ℝ≥0∞ :=
  spectralEntropyBits (firstReduction psi)

/-- PDF p.1: ladder coefficients on the full space, with explicit vacuum boundary.
This raw sequence need not be square summable and is not a total bounded operator. -/
def ladderCoefficients (creation : Bool) (j : Fin 2) (psi : TwoMode)
    (i : Fin 2 → ℕ) : ℂ :=
  if creation then
    if i j = 0 then 0 else
      (Real.sqrt (i j : ℝ) : ℂ) * psi (Function.update i j (i j - 1))
  else (Real.sqrt ((i j : ℝ) + 1) : ℂ) * psi (Function.update i j (i j + 1))

/-- PDF p.1, (2): coefficients of X_A-X_B or P_A+P_B. The combinations are
formed BEFORE checking their domains, allowing cancellation of unbounded terms. -/
def eprCoefficients (momentum : Bool) (psi : TwoMode) : (Fin 2 → ℕ) → ℂ :=
  fun i => if momentum then
    (Complex.I / (Real.sqrt 2 : ℂ)) *
      (ladderCoefficients true 0 psi i - ladderCoefficients false 0 psi i +
       ladderCoefficients true 1 psi i - ladderCoefficients false 1 psi i)
  else (1 / (Real.sqrt 2 : ℂ)) *
      (ladderCoefficients true 0 psi i + ladderCoefficients false 0 psi i -
       ladderCoefficients true 1 psi i - ladderCoefficients false 1 psi i)

/-- PDF p.1, (2): maximal oscillator quadrature domain; variance is infinity
outside the domain. On the domain the expectation is real and the norm is finite. -/
def eprVariance (momentum : Bool) (psi : TwoMode) : ℝ≥0∞ :=
  if h : Memℓp (eprCoefficients momentum psi) 2 then
    let image : TwoMode := ⟨eprCoefficients momentum psi, h⟩
    ENNReal.ofReal (‖image‖ ^ 2 - (inner ℂ psi image).re ^ 2)
  else ⊤

/-- PDF p.1, (2): clipping takes place in the extended nonnegative reals, so an
infinite variance gives exactly one, rather than toReal(infinity)=0. -/
def eprUncertainty (psi : TwoMode) : ℝ :=
  (min 1 ((eprVariance false psi + eprVariance true psi) / 2)).toReal

/-- PDF p.2, (4): natural logarithm, distinct from base-two entropy. -/
def squeezingAt (delta : ℝ) : ℝ := -Real.log delta / 2

/-- PDF p.1, (1): normalized Fock coefficients, continuously extended to r=0. -/
def squeezedCoefficients (r : ℝ) (i : Fin 2 → ℕ) : ℂ :=
  if i 0 = i 1 then ((Real.tanh r ^ i 0 / Real.cosh r : ℝ) : ℂ) else 0

/-- PDF pp.1–2, (1): the actual l2 vector. The fallback is unused for r>=0;
normalization and membership are conclusions of squeezed_state_identities. -/
def squeezedVector (r : ℝ) : TwoMode :=
  if h : Memℓp (squeezedCoefficients r) 2 then ⟨squeezedCoefficients r, h⟩ else 0

/-- PDF p.2: the sequence class C, with actual l2 normalization and monotonicity. -/
def SchmidtClass (c : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ c n ∧ c (n + 1) ≤ c n) ∧ HasSum (fun n => c n ^ 2) 1

/-- PDF p.2, (7) and its proof: the nonnegative difference-square series, equal
to (7) on C. This does not subtract divergent number expectations. -/
def sequenceUncertainty (c : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * (c n - c (n + 1)) ^ 2)

/-- PDF p.2, (6): extended Shannon entropy of squared Schmidt coefficients in bits. -/
def sequenceEntropy (c : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (-(c n ^ 2) * Real.logb 2 (c n ^ 2))

/-- PDF pp.1–3, (1),(3),(4): the geometric coefficients selected by the EPR level.
This corrects the printed exp(-N r_Delta) parameter mismatch in Lemma 2. -/
def geometricCoefficients (delta : ℝ) (n : ℕ) : ℝ :=
  Real.tanh (squeezingAt delta) ^ n / Real.cosh (squeezingAt delta)

/-- PDF p.3, Lemma 2: normalized geometric sequences are identified within C,
not by a freely chosen Lagrange-multiplier parameter. -/
def IsGeometric (c : ℕ → ℝ) : Prop :=
  ∃ a q : ℝ, 0 < a ∧ 0 ≤ q ∧ q < 1 ∧ ∀ n, c n = a * q ^ n

/-- PDF pp.2,4: x log_2 x with the explicit zero convention. -/
def xlog2x (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.logb 2 x

/-- PDF pp.3–4, (17): c-plus/minus, used only for delta>0. -/
def formationCoefficient (plus : Bool) (delta : ℝ) : ℝ :=
  ((1 / Real.sqrt delta + (if plus then Real.sqrt delta else -Real.sqrt delta)) ^ 2) / 4

/-- PDF pp.3–4, (17): the paper's f, in bits and on 0<delta<=1.
Distinct from the imported Adesso–Datta f (different argument, nats), and from
Information100.P08.formationFunction (qubit concurrence, value 1 at argument 1).
Here the EPR argument 1 is vacuum and the value is 0; those are different concepts. -/
def gaussianFormationBits (delta : ℝ) : ℝ :=
  xlog2x (formationCoefficient true delta) - xlog2x (formationCoefficient false delta)

/-- PDF p.3, (14): full product under the radical, clipped for the separable branch. -/
def symmetricEprLevel (n kx kp : ℝ) : ℝ := min 1 (Real.sqrt ((n - kx) * (n - kp)))

/-- PDF p.3, (15): all probability ensembles of normalized pure vectors with this
barycenter. Scalar integrability prevents default-zero Bochner integrals.
The Borel structure comes from the full Hilbert norm; no Gaussian restriction. -/
def Decomposes (mu : Measure PureVector) (rho : DensityKernel 2) : Prop :=
  IsProbabilityMeasure mu ∧ IsBarycenter mu (fun psi => rankOne psi.val) rho

/-- PDF p.3, (16): average actual pure-state entanglement, including infinity. -/
def ensembleCost (mu : Measure PureVector) : ℝ≥0∞ :=
  ∫⁻ psi, pureEntanglement psi.val ∂mu

/-- PDF p.3, (15)–(16): unrestricted entanglement of formation. Both countable and
continuous ensembles are included. The extended empty infimum is infinity. -/
def entanglementOfFormation (rho : DensityKernel 2) : ℝ≥0∞ :=
  ⨅ mu : {mu : Measure PureVector // Decomposes mu rho}, ensembleCost mu.val

/-- PDF p.3: D(z) shifts the first moments by x when z=(x_q+i x_p)/sqrt(2).
This differs from the dual Weyl argument v used in a characteristic function. -/
def shiftArgument (x : (InterleavedPhase 2)) : Fin 2 → ℂ :=
  fun j => ((x (j, 0) : ℂ) + Complex.I * (x (j, 1) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- PDF p.3, D_0: actual displaced pure-vector coefficients. -/
def shiftedCoefficients (x : (InterleavedPhase 2)) (psi : TwoMode) : (Fin 2 → ℕ) → ℂ :=
  fun i => ∑' j, productWeyl (shiftArgument x) i j * psi j

/-- PDF p.3: local unitary images of the specific squeezed seed, in full Fock space. -/
def localSeedCoefficients (U V : Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ) (r : ℝ)
    (i : Fin 2 → ℕ) : ℂ :=
  ∑' j : ℕ, ((Real.tanh r ^ j / Real.cosh r : ℝ) : ℂ) *
    U (lp.single 2 j 1) (i 0) * V (lp.single 2 j 1) (i 1)

/-- PDF p.3: singular Gaussian displacement law described by its characteristic
function. G is the full anticommutator residual: the classical covariance is G/2.
No inverse or Lebesgue density is required, including G=0 (a Dirac mass). -/
def GaussianShiftLaw (mu : Measure (InterleavedPhase 2)) (m : (InterleavedPhase 2)) (G : Cov 2) : Prop :=
  IsProbabilityMeasure mu ∧ G.PosSemidef ∧ ∀ v : (InterleavedPhase 2),
    (∫ x, Complex.exp (Complex.I * ((∑ i, v i * x i : ℝ) : ℂ)) ∂mu) =
      Complex.exp (((-(∑ i, ∑ j, v i * G i j * v j) / 4 : ℝ) : ℂ) +
        Complex.I * ((∑ i, v i * m i : ℝ) : ℂ))

/-! Small boundary checks for the complete local definitions. -/

example : xlog2x 0 = 0 := by simp [xlog2x]

example : xlog2x 1 = 0 := by simp [xlog2x]

example : squeezingAt 1 = 0 := by simp [squeezingAt]

example : squeezedCoefficients 0 ![0, 0] = 1 := by simp [squeezedCoefficients]

example : squeezedCoefficients 0 ![1, 1] = 0 := by simp [squeezedCoefficients, Real.tanh_zero]

example : formationCoefficient true 1 = 1 := by norm_num [formationCoefficient]

example : formationCoefficient false 1 = 0 := by norm_num [formationCoefficient]

example : gaussianFormationBits 1 = 0 := by norm_num [gaussianFormationBits, formationCoefficient, xlog2x]

example (psi : TwoMode) : ladderCoefficients true 0 psi ![0, 0] = 0 := by
  simp [ladderCoefficients]

example : shiftArgument 0 = 0 := by ext j; simp [shiftArgument]

example (momentum : Bool) (psi : TwoMode)
    (h : ¬ Memℓp (eprCoefficients momentum psi) 2) : eprVariance momentum psi = ⊤ := by
  simp [eprVariance, h]

example : firstReduction 0 = 0 := by
  ext i j
  simp [firstReduction]

example : sequenceUncertainty (fun _ => 0) = 0 := by
  simp [sequenceUncertainty]

example : sequenceEntropy (fun _ => 0) = 0 := by
  simp [sequenceEntropy]

example (x : (InterleavedPhase 2)) : shiftedCoefficients x 0 = 0 := by
  ext i
  simp [shiftedCoefficients]

example : geometricCoefficients 1 0 = 1 := by
  simp [geometricCoefficients, squeezingAt]

end QAlgorithms.Papers.Independent.Next46.P45


