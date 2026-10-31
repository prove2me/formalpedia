-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24
-- name    : QAlgorithms_Papers_Independent_Intake100_P24
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:11:53.973486+00:00
-- url     : https://prove2.me/theorems/695b4e95-26d8-465f-a6ec-fe7a178cfda4
-- title:
--   Definitions for Quantum features of macroscopic fields. Entropy and dynamics
-- statement:
--   The objects the formalized statements of *Quantum features of macroscopic fields. Entropy and dynamics* (arXiv:1904.06170) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PolarizationMatrix`: Two polarization coordinates, ordered 0 then 1 (PDF pp.2,8). Fin 2 matches the accepted trace dual; finTwoEquiv sends 0 to false and 1 to true when importing the frozen Pauli matrices.
--   - `JonesVector`: Jones amplitudes carry intensity and are not unit vectors (PDF pp.1,8).
--   - `stokesMatrix`: The Pauli expansion (2), with the frozen Pauli sign convention (PDF p.2).
--   - `jonesOuter`: The unnormalized Jones outer product (PDF pp.8–9).
--   - `leftMultiplication`: Left multiplication as a continuous complex-linear map (PDF p.8, (46)).
--   - `rightMultiplication`: Right multiplication as a continuous complex-linear map (PDF p.8, (46)).
--   - `jonesConjugation`: The map X ↦ V X V†, without a trace-preservation requirement (PDF p.9).
--   - `IsDoublyContracting`: Complete positivity and both passive inequalities (50) (PDF pp.8–9). All order comparisons use positive semidefinite differences.
--   - `IsScatteringUnitary`: Unitary support for an ordinary finite-rate scattering measure (PDF pp.6,8).
--   - `decoherencePart`: The Hermitian dissipative part of (49) (PDF p.8).
--   - `frequencyShift`: The Hermitian frequency shift in B = i delta + gamma_dec (PDF p.8, (49)).
--   - `stokesGenerator`: The literal standalone Stokes generator (46) (PDF p.8). Absorption has coefficient one, as printed. Correction: the stray S_1 in (46) is read as S, the matrix explicitly evolved there; no S_1 is defined. This definition makes no claim of compatibility with the differently normalized Jones equation (48). The measure is used below only when finite and supported on unitaries.
--   - `muellerPropagation`: Integration of the constant-coefficient Stokes equation (46) (PDF pp.8–9). This exponential constructs the global map rather than assuming its passivity.
--   - `jonesPropagation`: Integration of the standalone Jones equation (48) (PDF pp.8–9).
--   - `MuellerJonesPair`: Abstract Mueller–Jones pairs from the paragraph after (54) (PDF p.9).
--   - `IsMuellerJones`: Admissibility of an abstract optical map, including the positive difference (PDF p.9). No full-field realization of an arbitrary pair is assumed.
--   - `muellerJonesCompose`: Composition (55): the right device acts first (PDF p.9).
--   - `modeEntropy`: One-mode entropy g(lambda); natural logarithms, 0 log 0 = 0 (PDF pp.5,9).
--   - `polarizationEntropy`: Spectral form of (32) specialized to an admissible polarization pair (PDF p.9). It is extended nonnegative entropy; the two-mode sum is necessarily finite. This is not the entropy of an arbitrary pure full-field density.
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, https://arxiv.org/abs/1904.06170v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

/-!
Statements from R. Alicki, arXiv:1904.06170v1.
The finite-dimensional polarization results below are independent of the defective
full-field-to-polarization reduction (45),(47). Full-Fock interfaces and the
inconsistent kinetic claims are recorded in this unit's HARD.md and GAPS.json.
-/

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)
open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

/-- Two polarization coordinates, ordered 0 then 1 (PDF pp.2,8).
Fin 2 matches the accepted trace dual; finTwoEquiv sends 0 to false and 1 to true
when importing the frozen Pauli matrices. -/
abbrev PolarizationMatrix := Matrix (Fin 2) (Fin 2) ℂ

-- Scattering is measured with the Borel sigma-algebra of the matrix topology.
local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- Jones amplitudes carry intensity and are not unit vectors (PDF pp.1,8). -/
abbrev JonesVector := Fin 2 → ℂ

/-- The Pauli expansion (2), with the frozen Pauli sign convention (PDF p.2). -/
def stokesMatrix (s0 s1 s2 s3 : ℝ) : PolarizationMatrix :=
  ((1 / 2 : ℂ) • ((s0 : ℂ) • 1 + (s1 : ℂ) • QAlgorithms.pauliX +
    (s2 : ℂ) • QAlgorithms.pauliY + (s3 : ℂ) • QAlgorithms.pauliZ)).submatrix
      finTwoEquiv finTwoEquiv

/-- The unnormalized Jones outer product (PDF pp.8–9). -/
def jonesOuter (alpha : JonesVector) : PolarizationMatrix :=
  Matrix.vecMulVec alpha (fun j => star (alpha j))

/-- Left multiplication as a continuous complex-linear map (PDF p.8, (46)). -/
def leftMultiplication (A : PolarizationMatrix) :
    PolarizationMatrix →L[ℂ] PolarizationMatrix :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)

/-- Right multiplication as a continuous complex-linear map (PDF p.8, (46)). -/
def rightMultiplication (A : PolarizationMatrix) :
    PolarizationMatrix →L[ℂ] PolarizationMatrix :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ A)

/-- The map X ↦ V X V†, without a trace-preservation requirement (PDF p.9). -/
def jonesConjugation (V : PolarizationMatrix) :
    PolarizationMatrix →ₗ[ℂ] PolarizationMatrix :=
  ((rightMultiplication Vᴴ).comp (leftMultiplication V)).toLinearMap

/-- Complete positivity and both passive inequalities (50) (PDF pp.8–9).
All order comparisons use positive semidefinite differences. -/
def IsDoublyContracting (Phi : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive Phi ∧
    (1 - Phi 1).PosSemidef ∧ (1 - traceDual Phi 1).PosSemidef

/-- Unitary support for an ordinary finite-rate scattering measure (PDF pp.6,8). -/
def IsScatteringUnitary (U : PolarizationMatrix) : Prop :=
  U * Uᴴ = 1 ∧ Uᴴ * U = 1

/-- The Hermitian dissipative part of (49) (PDF p.8). -/
def decoherencePart (B : PolarizationMatrix) : PolarizationMatrix :=
  (1 / 2 : ℂ) • (B + Bᴴ)

/-- The Hermitian frequency shift in B = i delta + gamma_dec (PDF p.8, (49)). -/
def frequencyShift (B : PolarizationMatrix) : PolarizationMatrix :=
  (-Complex.I / 2) • (B - Bᴴ)

/-- The literal standalone Stokes generator (46) (PDF p.8).
Absorption has coefficient one, as printed. Correction: the stray S_1 in (46)
is read as S, the matrix explicitly evolved there; no S_1 is defined.
This definition makes no claim of
compatibility with the differently normalized Jones equation (48).
The measure is used below only when finite and supported on unitaries. -/
def stokesGenerator (omega gamma : PolarizationMatrix)
    (mu : Measure PolarizationMatrix) : PolarizationMatrix →L[ℂ] PolarizationMatrix :=
  (-Complex.I) • (leftMultiplication omega - rightMultiplication omega) -
    (leftMultiplication gamma + rightMultiplication gamma) +
    ∫ U, LinearMap.toContinuousLinearMap (jonesConjugation U) -
      ContinuousLinearMap.id ℂ PolarizationMatrix ∂mu

/-- Integration of the constant-coefficient Stokes equation (46) (PDF pp.8–9).
This exponential constructs the global map rather than assuming its passivity. -/
def muellerPropagation (omega gamma : PolarizationMatrix)
    (mu : Measure PolarizationMatrix) (t : ℝ) :
    PolarizationMatrix →ₗ[ℂ] PolarizationMatrix :=
  (NormedSpace.exp ((t : ℂ) • stokesGenerator omega gamma mu)).toLinearMap

/-- Integration of the standalone Jones equation (48) (PDF pp.8–9). -/
def jonesPropagation (omega gamma gammaDec : PolarizationMatrix) (t : ℝ) :
    PolarizationMatrix :=
  NormedSpace.exp ((-(t : ℂ)) •
    (Complex.I • omega + (1 / 2 : ℂ) • gamma + gammaDec))

/-- Abstract Mueller–Jones pairs from the paragraph after (54) (PDF p.9). -/
abbrev MuellerJonesPair :=
  (PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) × PolarizationMatrix

/-- Admissibility of an abstract optical map, including the positive difference (PDF p.9).
No full-field realization of an arbitrary pair is assumed. -/
def IsMuellerJones (P : MuellerJonesPair) : Prop :=
  IsDoublyContracting P.1 ∧ (1 - P.2 * P.2ᴴ).PosSemidef ∧
    IsPositiveMap (P.1 - jonesConjugation P.2)

/-- Composition (55): the right device acts first (PDF p.9). -/
def muellerJonesCompose (P Q : MuellerJonesPair) : MuellerJonesPair :=
  (P.1.comp Q.1, P.2 * Q.2)

/-- One-mode entropy g(lambda); natural logarithms, 0 log 0 = 0 (PDF pp.5,9). -/
def modeEntropy (x : ℝ) : ℝ :=
  (x + 1) * Real.log (x + 1) - x * Real.log x

/-- Spectral form of (32) specialized to an admissible polarization pair (PDF p.9).
It is extended nonnegative entropy; the two-mode sum is necessarily finite.
This is not the entropy of an arbitrary pure full-field density. -/
def polarizationEntropy (kB : ℝ) (S : PolarizationMatrix) (alpha : JonesVector)
    (hCov : (S - jonesOuter alpha).PosSemidef) : ℝ≥0∞ :=
  ENNReal.ofReal kB * ∑ j : Fin 2,
    ENNReal.ofReal (modeEntropy (hCov.isHermitian.eigenvalues j))

/-- Zero intensity is allowed in (2) (PDF p.2). -/
example : stokesMatrix 0 0 0 0 = 0 := by
  simp [stokesMatrix]

/-- A zero Jones amplitude contributes no coherent intensity (PDF p.9). -/
example : jonesOuter 0 = 0 := by
  ext i j
  simp [jonesOuter, Matrix.vecMulVec]

/-- Multiplication maps have the intended order (PDF p.9, (51)). -/
example (V X : PolarizationMatrix) : jonesConjugation V X = V * X * Vᴴ := rfl

/-- The zero optical map has zero dual (PDF p.9, (51)). -/
example (M : PolarizationMatrix) :
    traceDual (0 : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) M = 0 := by
  ext i j
  change (∑ a : Fin 2, ∑ b : Fin 2, (0 : ℂ) * M a b) = 0
  simp

/-- A zero map is positive without preserving trace (PDF p.9). -/
example : IsPositiveMap (0 : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) := by
  intro X hX
  exact Matrix.PosSemidef.zero

/-- Zero scattering produces no decoherence or frequency shift (PDF p.8). -/
example : decoherencePart 0 = 0 ∧ frequencyShift 0 = 0 := by
  simp [decoherencePart, frequencyShift]

/-- The identity scattering matrix is allowed (PDF p.8). -/
example : IsScatteringUnitary 1 := by
  simp [IsScatteringUnitary]

/-- A zero propagation time acts identically on Jones amplitudes (PDF p.9, (53)). -/
example (omega gamma gammaDec : PolarizationMatrix) :
    jonesPropagation omega gamma gammaDec 0 = 1 := by
  simp [jonesPropagation]

/-- The order of paired composition follows (55) (PDF p.9). -/
example (P Q : MuellerJonesPair) :
    (muellerJonesCompose P Q).2 = P.2 * Q.2 := rfl

/-- Vacuum occupation contributes zero entropy (PDF p.5, (32)). -/
example : modeEntropy 0 = 0 := by
  simp [modeEntropy]

end QAlgorithms.Papers.Independent.Intake100.P24


