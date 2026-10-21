-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P37
-- name    : QAlgorithms_Papers_Independent_Claimed50_P37
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:37:26.588302+00:00
-- url     : https://prove2.me/theorems/46b3550e-13ad-4360-adb1-59eb8b852b8c
-- title:
--   Definitions for Gaussian transformations and distillation of entangled Gaussian states
-- statement:
--   The objects the formalized statements of *Gaussian transformations and distillation of entangled Gaussian states* (arXiv:quant-ph/0204069) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FockLabel`: PDF p.2: full n-mode number-basis labels, without a cutoff.
--   - `Quadrature`: PDF p.2: interleaved quadratures; 0 = x and 1 = p within each mode.
--   - `PhaseCoordinates`: PDF p.2: phase coordinates with coordinate Lebesgue measure.
--   - `weylParameter`: PDF p.2, Eq.(5): exp(i(q_x x+q_p p)) = D((-q_p+i q_x)/sqrt(2)). This fixes the vacuum characteristic function to exp(-sum q_j^2/4).
--   - `weylCoeff`: PDF p.2: product of fixed bounded Fock Weyl operators.
--   - `multimodeCharacteristic`: PDF p.2, Eq.(5): Tr(X D(q)) on full Fock coefficients. Trace-class restrictions and convergence are enforced in the theorem.
--   - `pairCharacteristic`: PDF p.2, Eqs.(3),(5): characteristic function on input tensor output.
--   - `phasePairing`: PDF p.2, Eq.(5): ordinary real coordinate pairing.
--   - `wigner`: PDF p.2, Eq.(5): inverse Fourier transform with (2 pi)^(-2n). The theorem uses only Gaussian inputs and their trace-class contraction.
--   - `pairWigner`: PDF p.2, Eqs.(3)–(5): resource inverse Fourier transform.
--   - `HasCenteredGaussian`: PDF p.2: centered finite Gaussian covariance, vacuum I. Actual positivity and normalization come separately from State or IsDensity; positive definiteness specifies the finite physical covariance domain.
--   - `HasCenteredGaussianResource`: PDF p.2, Eq.(3): centered resource with blocks A,C,C^T,B. This constrains an actual density and does not define a state by covariance.
--   - `reflection`: PDF p.2, Eq.(4): transposition fixes x and negates p.
--   - `contraction`: PDF pp.1–2, Eq.(1): Tr_in[chi (rho^T tensor I)]. Transposition gives rho(i,j), not rho(j,i), in this full-space coefficient formula.
--   - `successTrace`: PDF pp.1–2: real trace on positive trace-class unnormalized outputs. Diagonal summability and strict positivity are theorem conclusions.
--   - `normalizeFockCoefficients`: PDF pp.1–2: normalization, used only when successTrace > 0.
--   - `outputCovariance`: PDF p.2, Eq.(7): Schur covariance with the printed orientation of C.
--   - `canonicalForm`: PDF pp.3–4: the real canonical commutator form for interleaved x,p.
--   - `IsSymplecticUnitary`: PDF pp.3–4: an actual bounded metaplectic unitary. The implementing coordinate matrix is symplectic; its transpose acts on characteristic arguments. The unitary is on the full complete oscillator space, not a real coordinate matrix.
--   - `IsGaussianPair`: PDF pp.2–4: Gaussian resource allowing arbitrary first moments. The full trace-class density requirement comes from the State/PureState theorem binder.
--   - `squeezedVacuumAmplitude`: PDF p.4: two-mode squeezed vacuum on input 0/output 0, with vacuum on input 1. Squeezing parameter r≥0 includes the complete product vacuum. The geometric coefficients fix the state, including its infinite Fock tail.
--   - `squeezedVacuumResource`: PDF p.4: the pure squeezed-pair/vacuum density coefficients. The theorem concludes that these coefficients are a normalized pure trace-class state.
--   - `normalFormPreparation`: PDF pp.2–4: local symplectic preparation and local Weyl displacements. The two-input unitary may mix the input modes; the output unitary acts on one mode. Parameters di/do are Weyl generator coordinates, not asserted to be first moments.
--   - `squeezedPairAmplitude`: PDF p.4, Eq.(12): squeezed pair on the first input and output alone.
--   - `residualResource`: PDF p.4, Eq.(12): chi_A0, absorbing the one-output unitary and displacement. It is constructed from the squeezed pair, not an arbitrary assumed factorization.
--   - `transposedInput`: PDF p.4, Eq.(13), step (i): conjugation by the OPERATOR transpose of D(di) Ui in the fixed Fock basis. This is not a transpose of S in phase space.
--   - `vacuumEmbedding`: PDF p.4, Eq.(13): retain the first input and fix the second input in vacuum.
--   - `vacuumProjection`: PDF p.4, Eq.(13), step (ii): the UNNORMALIZED vacuum projection.
-- source:
--   Gaussian transformations and distillation of entangled Gaussian states, arXiv:quant-ph/0204069v2, https://arxiv.org/abs/quant-ph/0204069v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

/-!
Fiurasek, arXiv:quant-ph/0204069v2, PDF pp.1–4.
Finite-resource contraction on actual full oscillator densities. Operational
results missing an instrument interface are deferred in HARD.md and GAPS.json.
No infinite-squeezing object is a density. Compilation is pending batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P37

/-! Reuse the accepted generic real quadratic form at the interleaved index type.
The accepted P10.Phase is a grouped coordinate INDEX, P39.characteristic takes a
single-mode bounded operator, and Information100.P48.normalize requires a finite
index type. Their types differ from the full multimode coordinate/trace-series
objects below; those objects have explicit distinct names, with unchanged bodies.
-/

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass productCoeff)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

/-- PDF p.2: full n-mode number-basis labels, without a cutoff. -/
abbrev FockLabel (n : ℕ) := Fin n → ℕ

/-- PDF p.2: interleaved quadratures; 0 = x and 1 = p within each mode. -/
abbrev Quadrature (n : ℕ) := Fin n × Fin 2

/-- PDF p.2: phase coordinates with coordinate Lebesgue measure. -/
abbrev PhaseCoordinates (n : ℕ) := Quadrature n → ℝ

/-- PDF p.2, Eq.(5): exp(i(q_x x+q_p p)) = D((-q_p+i q_x)/sqrt(2)).
This fixes the vacuum characteristic function to exp(-sum q_j^2/4). -/
def weylParameter {n : ℕ} (q : PhaseCoordinates n) (k : Fin n) : ℂ :=
  (-(q (k, 1) : ℂ) + Complex.I * (q (k, 0) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- PDF p.2: product of fixed bounded Fock Weyl operators. -/
def weylCoeff {n : ℕ} (q : PhaseCoordinates n) : Matrix (FockLabel n) (FockLabel n) ℂ :=
  fun a b => ∏ k, displacementMatrix (weylParameter q k) (a k) (b k)

/-- PDF p.2, Eq.(5): Tr(X D(q)) on full Fock coefficients.
Trace-class restrictions and convergence are enforced in the theorem. -/
def multimodeCharacteristic {n : ℕ} (X : Matrix (FockLabel n) (FockLabel n) ℂ)
    (q : PhaseCoordinates n) : ℂ :=
  ∑' a, ∑' b, X a b * weylCoeff q b a

/-- PDF p.2, Eqs.(3),(5): characteristic function on input tensor output. -/
def pairCharacteristic {ni no : ℕ}
    (X : Matrix (FockLabel ni × FockLabel no) (FockLabel ni × FockLabel no) ℂ)
    (q : PhaseCoordinates ni) (s : PhaseCoordinates no) : ℂ :=
  ∑' a, ∑' b, X a b * productCoeff (weylCoeff q) (weylCoeff s) b a

/-- PDF p.2, Eq.(5): ordinary real coordinate pairing. -/
def phasePairing {n : ℕ} (r q : PhaseCoordinates n) : ℝ := ∑ j, r j * q j

/-- PDF p.2, Eq.(5): inverse Fourier transform with (2 pi)^(-2n).
The theorem uses only Gaussian inputs and their trace-class contraction. -/
def wigner {n : ℕ} (X : Matrix (FockLabel n) (FockLabel n) ℂ)
    (r : PhaseCoordinates n) : ℂ :=
  ((2 * Real.pi : ℂ) ^ (2 * n))⁻¹ *
    ∫ q : PhaseCoordinates n, multimodeCharacteristic X q *
      Complex.exp (-Complex.I * (phasePairing r q : ℂ))

/-- PDF p.2, Eqs.(3)–(5): resource inverse Fourier transform. -/
def pairWigner {ni no : ℕ}
    (X : Matrix (FockLabel ni × FockLabel no) (FockLabel ni × FockLabel no) ℂ)
    (r : PhaseCoordinates ni) (s : PhaseCoordinates no) : ℂ :=
  ((2 * Real.pi : ℂ) ^ (2 * (ni + no)))⁻¹ *
    ∫ q : PhaseCoordinates ni, ∫ t : PhaseCoordinates no, pairCharacteristic X q t *
      Complex.exp (-Complex.I * ((phasePairing r q + phasePairing s t : ℝ) : ℂ))

/-- PDF p.2: centered finite Gaussian covariance, vacuum I.
Actual positivity and normalization come separately from State or IsDensity;
positive definiteness specifies the finite physical covariance domain. -/
def HasCenteredGaussian {n : ℕ}
    (X : Matrix (FockLabel n) (FockLabel n) ℂ)
    (G : Matrix (Quadrature n) (Quadrature n) ℝ) : Prop :=
  G.PosDef ∧ ∀ q, multimodeCharacteristic X q = Complex.exp ((-quadratic G q / 4 : ℝ) : ℂ)

/-- PDF p.2, Eq.(3): centered resource with blocks A,C,C^T,B.
This constrains an actual density and does not define a state by covariance. -/
def HasCenteredGaussianResource {ni no : ℕ}
    (X : Matrix (FockLabel ni × FockLabel no) (FockLabel ni × FockLabel no) ℂ)
    (A : Matrix (Quadrature ni) (Quadrature ni) ℝ)
    (B : Matrix (Quadrature no) (Quadrature no) ℝ)
    (C : Matrix (Quadrature ni) (Quadrature no) ℝ) : Prop :=
  (Matrix.fromBlocks A C C.transpose B).PosDef ∧
    ∀ q s, pairCharacteristic X q s = Complex.exp
      ((-(quadratic A q + 2 * (∑ i, ∑ j, q i * C i j * s j) + quadratic B s) / 4 : ℝ) : ℂ)

/-- PDF p.2, Eq.(4): transposition fixes x and negates p. -/
def reflection (n : ℕ) : Matrix (Quadrature n) (Quadrature n) ℝ :=
  Matrix.diagonal (fun j => if j.2 = 0 then 1 else -1)

/-- PDF pp.1–2, Eq.(1): Tr_in[chi (rho^T tensor I)]. Transposition gives
rho(i,j), not rho(j,i), in this full-space coefficient formula. -/
def contraction {ni no : ℕ}
    (chi : Matrix (FockLabel ni × FockLabel no) (FockLabel ni × FockLabel no) ℂ)
    (rho : Matrix (FockLabel ni) (FockLabel ni) ℂ) :
    Matrix (FockLabel no) (FockLabel no) ℂ :=
  fun a b => ∑' i, ∑' j, chi (i, a) (j, b) * rho i j

/-- PDF pp.1–2: real trace on positive trace-class unnormalized outputs.
Diagonal summability and strict positivity are theorem conclusions. -/
def successTrace {n : ℕ} (X : Matrix (FockLabel n) (FockLabel n) ℂ) : ℝ :=
  ∑' a, (X a a).re

/-- PDF pp.1–2: normalization, used only when successTrace > 0. -/
def normalizeFockCoefficients {n : ℕ} (X : Matrix (FockLabel n) (FockLabel n) ℂ) :
    Matrix (FockLabel n) (FockLabel n) ℂ :=
  fun a b => X a b / (successTrace X : ℂ)

/-- PDF p.2, Eq.(7): Schur covariance with the printed orientation of C. -/
def outputCovariance {ni no : ℕ}
    (G A : Matrix (Quadrature ni) (Quadrature ni) ℝ)
    (B : Matrix (Quadrature no) (Quadrature no) ℝ)
    (C : Matrix (Quadrature ni) (Quadrature no) ℝ) :
    Matrix (Quadrature no) (Quadrature no) ℝ :=
  B - C.transpose * (A + reflection ni * G * reflection ni)⁻¹ * C

example {n : ℕ} (k : Fin n) : weylParameter (0 : PhaseCoordinates n) k = 0 := by
  simp [weylParameter]

example (q : PhaseCoordinates 0) (a b : FockLabel 0) : weylCoeff q a b = 1 := by
  simp [weylCoeff]

example : reflection 1 ((0 : Fin 1), (1 : Fin 2)) ((0 : Fin 1), (1 : Fin 2)) = -1 := by
  norm_num [reflection, Matrix.diagonal]

example {n : ℕ} (G A : Matrix (Quadrature n) (Quadrature n) ℝ)
    (B : Matrix (Quadrature n) (Quadrature n) ℝ) :
    outputCovariance G A B 0 = B := by
  simp [outputCovariance]

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (PureState rankOne)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel composeKernel)

/-- PDF pp.3–4: the real canonical commutator form for interleaved x,p. -/
def canonicalForm (n : ℕ) : Matrix (Quadrature n) (Quadrature n) ℝ :=
  fun i j => if i.1 = j.1 then
    (if i.2 = 0 ∧ j.2 = 1 then 1 else if i.2 = 1 ∧ j.2 = 0 then -1 else 0)
    else 0

/-- PDF pp.3–4: an actual bounded metaplectic unitary. The implementing
coordinate matrix is symplectic; its transpose acts on characteristic arguments.
The unitary is on the full complete oscillator space, not a real coordinate matrix. -/
def IsSymplecticUnitary {n : ℕ}
    (U : Hilbert (FockLabel n) ≃ₗᵢ[ℂ] Hilbert (FockLabel n)) : Prop :=
  ∃ S : Matrix (Quadrature n) (Quadrature n) ℝ,
    S * canonicalForm n * S.transpose = canonicalForm n ∧
    ∀ q : PhaseCoordinates n,
      conjugateKernel (unitaryCoeff U.symm) (weylCoeff q) =
        weylCoeff (S.transpose.mulVec q)

/-- PDF pp.2–4: Gaussian resource allowing arbitrary first moments. The full
trace-class density requirement comes from the State/PureState theorem binder. -/
def IsGaussianPair {ni no : ℕ}
    (X : Matrix (FockLabel ni × FockLabel no) (FockLabel ni × FockLabel no) ℂ) : Prop :=
  ∃ (A : Matrix (Quadrature ni) (Quadrature ni) ℝ)
    (B : Matrix (Quadrature no) (Quadrature no) ℝ)
    (C : Matrix (Quadrature ni) (Quadrature no) ℝ)
    (mi : PhaseCoordinates ni) (mo : PhaseCoordinates no),
    (Matrix.fromBlocks A C C.transpose B).PosDef ∧
      ∀ q t, pairCharacteristic X q t = Complex.exp
        (((-(quadratic A q + 2 * (∑ i, ∑ j, q i * C i j * t j) +
          quadratic B t) / 4 : ℝ) : ℂ) +
          Complex.I * ((phasePairing mi q + phasePairing mo t : ℝ) : ℂ))

/-- PDF p.4: two-mode squeezed vacuum on input 0/output 0, with vacuum
on input 1. Squeezing parameter r≥0 includes the complete product vacuum.
The geometric coefficients fix the state, including its infinite Fock tail. -/
def squeezedVacuumAmplitude (r : ℝ) (a : FockLabel 2 × FockLabel 1) : ℂ :=
  if a.1 1 = 0 ∧ a.1 0 = a.2 0 then
    (Real.tanh r : ℂ) ^ (a.2 0) / (Real.cosh r : ℂ) else 0

/-- PDF p.4: the pure squeezed-pair/vacuum density coefficients. The theorem
concludes that these coefficients are a normalized pure trace-class state. -/
def squeezedVacuumResource (r : ℝ) :
    Matrix (FockLabel 2 × FockLabel 1) (FockLabel 2 × FockLabel 1) ℂ :=
  fun a b => squeezedVacuumAmplitude r a * star (squeezedVacuumAmplitude r b)

/-- PDF pp.2–4: local symplectic preparation and local Weyl displacements.
The two-input unitary may mix the input modes; the output unitary acts on one mode.
Parameters di/do are Weyl generator coordinates, not asserted to be first moments. -/
def normalFormPreparation
    (Ui : Hilbert (FockLabel 2) ≃ₗᵢ[ℂ] Hilbert (FockLabel 2))
    (Uo : Hilbert (FockLabel 1) ≃ₗᵢ[ℂ] Hilbert (FockLabel 1))
    (di : PhaseCoordinates 2) (dout : PhaseCoordinates 1) (r : ℝ) :
    Matrix (FockLabel 2 × FockLabel 1) (FockLabel 2 × FockLabel 1) ℂ :=
  conjugateKernel
    (productCoeff (composeKernel (weylCoeff di) (unitaryCoeff Ui))
      (composeKernel (weylCoeff dout) (unitaryCoeff Uo)))
    (squeezedVacuumResource r)

example : canonicalForm 1 ((0 : Fin 1), (0 : Fin 2))
    ((0 : Fin 1), (1 : Fin 2)) = 1 := by
  norm_num [canonicalForm]

example : squeezedVacuumAmplitude 0 ((fun _ => 0), (fun _ => 0)) = 1 := by
  simp [squeezedVacuumAmplitude]

open QAlgorithms.Papers.Independent.Frontier30.P14 (identityCoeff)

/-- PDF p.4, Eq.(12): squeezed pair on the first input and output alone. -/
def squeezedPairAmplitude (r : ℝ) (a : FockLabel 1 × FockLabel 1) : ℂ :=
  if a.1 0 = a.2 0 then
    (Real.tanh r : ℂ) ^ (a.2 0) / (Real.cosh r : ℂ) else 0

/-- PDF p.4, Eq.(12): chi_A0, absorbing the one-output unitary and displacement.
It is constructed from the squeezed pair, not an arbitrary assumed factorization. -/
def residualResource
    (Uo : Hilbert (FockLabel 1) ≃ₗᵢ[ℂ] Hilbert (FockLabel 1))
    (dout : PhaseCoordinates 1) (r : ℝ) :
    Matrix (FockLabel 1 × FockLabel 1) (FockLabel 1 × FockLabel 1) ℂ :=
  conjugateKernel
    (productCoeff (identityCoeff (FockLabel 1))
      (composeKernel (weylCoeff dout) (unitaryCoeff Uo)))
    (fun a b => squeezedPairAmplitude r a * star (squeezedPairAmplitude r b))

/-- PDF p.4, Eq.(13), step (i): conjugation by the OPERATOR transpose
of D(di) Ui in the fixed Fock basis. This is not a transpose of S in phase space. -/
def transposedInput
    (Ui : Hilbert (FockLabel 2) ≃ₗᵢ[ℂ] Hilbert (FockLabel 2))
    (di : PhaseCoordinates 2) (X : Matrix (FockLabel 2) (FockLabel 2) ℂ) :
    Matrix (FockLabel 2) (FockLabel 2) ℂ :=
  conjugateKernel (composeKernel (weylCoeff di) (unitaryCoeff Ui)).transpose X

/-- PDF p.4, Eq.(13): retain the first input and fix the second input in vacuum. -/
def vacuumEmbedding (m : FockLabel 1) : FockLabel 2 :=
  fun k => if k = 0 then m 0 else 0

/-- PDF p.4, Eq.(13), step (ii): the UNNORMALIZED vacuum projection. -/
def vacuumProjection (X : Matrix (FockLabel 2) (FockLabel 2) ℂ) :
    Matrix (FockLabel 1) (FockLabel 1) ℂ :=
  fun m n => X (vacuumEmbedding m) (vacuumEmbedding n)

example (m : FockLabel 1) : vacuumEmbedding m 1 = 0 := by
  simp [vacuumEmbedding]

example : squeezedPairAmplitude 0 ((fun _ => 0), (fun _ => 0)) = 1 := by
  simp [squeezedPairAmplitude]

end QAlgorithms.Papers.Independent.Claimed50.P37


