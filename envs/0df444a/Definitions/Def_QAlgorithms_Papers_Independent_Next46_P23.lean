-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
-- name    : QAlgorithms_Papers_Independent_Next46_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T18:44:34.056918+00:00
-- url     : https://prove2.me/theorems/ec849e49-857e-4437-8d35-34d1cb61ca44
-- title:
--   Definitions for Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction
-- statement:
--   The objects the formalized statements of *Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction* (arXiv:1106.3786) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ev`: Real trace evaluation, source pp.31,42.
--   - `logMat`: Finite spectral log with kernel value zero; only weighted/compressed uses, pp.33,43,47.
--   - `Supports`: Range inclusion, equivalently reverse kernel inclusion for self-adjoint matrices; p.43.
--   - `Orthogonal`: Orthogonal supports for positive matrices, p.43.
--   - `signedRelativeEntropy`: Signed relative entropy via the negative accepted Umegaki entropy; p.47.
--   - `kleinDivergence`: Unnormalized Klein divergence, plus infinity at failed support inclusion; p.35.
--   - `renyi`: Extended Rényi log-overlap with the support convention at all real exponents; pp.44--45.
--   - `renyiReal`: Real representative for nonorthogonal states, p.45.
--   - `compressedExp`: Support-compressed exponential exp(A+log nu), zero off Ran nu; p.47. Outer projections remove the exponential's identity on the kernel.
--   - `pullback`: Trace-dual density for rho composed with Phi; pp.42,46.
--   - `RectangularKPositive`: k-positivity of the actual block amplification, pp.39--40.
--   - `kosakiCost`: Extended Kosaki cost. The 1/t multiplies rho(A A*); p.46.
--   - `kosakiMinimizer`: Constructed Kosaki minimizer, including the leading t; p.46.
--   - `tau`: Heisenberg evolution exp(itH) A exp(-itH), pp.52,71.
--   - `evolved`: Dual density evolution exp(-itH) rho exp(itH), pp.52,71.
--   - `complexTau`: Entire complex-time dynamics, pp.52--53.
--   - `perturbationCocycle`: Interaction-picture propagator for H+alpha V, pp.56--57.
--   - `KMS`: KMS condition with the source's -i beta sign, p.53 (2.24).
--   - `Reversal`: Anti-linear involutive star-automorphism, source p.71; no real-basis restriction.
--   - `Reverses`: TRI conditions for a specified reversal, p.71.
--   - `TRI`: Existence of a source reversal, p.71.
--   - `relativeHamiltonian`: Relative Hamiltonian for faithful densities, p.64.
--   - `entropyProduction`: Entropy production -i[H,log omega], p.72.
--   - `averagedProduction`: Source time average in integral form, with oriented interval integral, p.72.
--   - `kuboMori`: Kubo--Mori kuboMori, conjugate-linear in first slot, p.63.
--   - `pressure`: Finite-p and infinity pressure definitions, source p.74.
--   - `eigenvalues`: Distinct real eigenvalues; degeneracy lies in the projectors, pp.32,78.
--   - `modularLaw`: Spectral law of -log Delta_(rho|nu)/t in sqrt nu, p.78.
--   - `fcs`: Two-measurement law of entropy change (s'-s)/t, source p.79.
--   - `steady`: Cesàro stationary density constructed from H, source p.95.
--   - `AutomorphismDynamics`: Continuous group of complex-linear star-automorphisms, source p.52.
--   - `extendedGibbs`: Gibbs state at finite beta or normalized extremal spectral projection; pp.53--54.
--   - `FermionOccupation`: Finite occupation basis, including the empty subset (vacuum); pp.116--117. Increasing Slater determinants are orthonormal with the source's sqrt(n!) convention.
--   - `fockGamma`: Exterior-power matrix in the increasing occupation basis, direct-summed over sectors; source pp.116--118. This is the determinant of the corresponding equal-size minor.
--   - `creation`: Left wedge creation. Inserting mode j crosses the occupied modes smaller than j; source p.119. Duplicate occupations are excluded.
--   - `annihilation`: Annihilation is the adjoint and hence anti-linear in psi; source p.119.
--   - `dGamma`: Differential second quantization from the defining derivative of Gamma(exp(zA)); p.118 (6.5). It is not defined using the conclusion of Proposition6.2(9).
--   - `quasiFree`: Quasi-free finite many-body density, with normalization on Fock space only; p.124.
--   - `quasiFreeZ`: Partition function associated with the one-particle density T, source p.124.
--   - `fermiDirac`: Fermi--Dirac one-particle density, without trace-one normalization; p.126.
--   - `matrixCommutant`: Commutant inside all complex matrices, source pp.59,122.
--   - `amUpper`: Intrinsic p>=2 Araki--Masuda norm via relative modular powers and Hilbert--Schmidt norm; source p.65. The maximization is over ALL normalized states, including singular ones.
--   - `amNorm`: For 1<=p<2 the norm is defined by duality, NOT by Theorem2.25's conclusion; source p.66. The q= infinity endpoint occurs at p=1.
--   - `amCone`: Araki--Masuda cone, the image of the positive cone under the weighted map; p.66.
--   - `transfer`: The p-transfer group defined in the source, including p=infinity; p.76.
--   - `LpImplements`: The source implementation properties for a linear group; source pp.76--77.
--   - `lpGenerator`: Generator H xi - xi varsigma_omega^(i(1/2-1/p))(H), in matrix-unit coordinates; source p.77. Matrix units are orthonormal in Hilbert--Schmidt space.
--   - `FluxFamily`: Source parameter-dependent system with chosen flux decomposition; PDF p.85.
--   - `FluxTRI`: TRI includes oddness of the CHOSEN fluxes, source p.85 (3.17).
--   - `FluxC1`: Continuously differentiable parameter data for linear response; source p.87.
--   - `generalizedPressure`: Generalized pressure; current times are NEGATIVE as in (3.18), source p.86.
--   - `kineticCoefficient`: Finite-time kinetic coefficient; the time average includes 1/t, source p.87.
--   - `compactExtension`: Extension of the continuous compact-domain convex function by positive infinity; p.155.
--   - `subgradient`: Subgradient of the compact-domain extension, empty off its finite domain; p.155.
--   - `dualSubgradient`: Subgradient of the everywhere-finite dual function; p.155.
--   - `ScalarLD`: The source arbitrary unbounded positive real time set, with weight exactly t; p.156.
--   - `timeFilter`: Limit filter on the source real time index set, p.156.
--   - `ScalarHasLD`: Assumption LD on the finite interval, source p.156.
--   - `upperTailLog`: Normalized extended log-event mass; log0=-infinity, source p.156.
--   - `polydisk`: The open complex polydisk, source PDF p.163.
--   - `complexMixedPartial`: Every mixed derivative, with the empty list denoting the function itself; source p.163.
--   - `leftMatrix`: Left action on Hilbert--Schmidt matrix units, source p.59.
--   - `rightMatrix`: Right action R(A)xi=xi A*, source p.59. The dependence on A is conjugate-linear.
--   - `conjugateByJ`: Matrix of conjugation X -> J X J on Hilbert--Schmidt operators; Jxi=xi*, source p.60.
--   - `relativeModularMatrix`: Nonfaithful relative modular operator rho xi nu^(-1), where the inverse is zero on the kernel; source p.67. Indices identify Hilbert--Schmidt matrix units.
--   - `relativeModularMeasure`: Spectral measure of Delta itself in sqrt nu, not of log Delta or its time scaling; source pp.67,69.
--   - `ProjectionTest`: Projection tests accept rho on outcome one, source p.50.
--   - `optimalTestingError`: Minimal Bayesian error with prior p for rho, source p.50. The admissible set contains zero; normalized states bound errors in [0,1], so the real infimum has no empty/unbounded default in any theorem use.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, https://arxiv.org/abs/1106.3786v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_SpectralFilter
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-! Statements from arXiv:1106.3786v1. Natural logarithms, signed nonpositive relative
entropy, and support-restricted powers follow the source conventions. No infinite object is replaced
by unrelated matrices. Compilation and independent moderation are pending. -/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)
open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)
open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)
open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Real trace evaluation, source pp.31,42. -/
def ev (rho A : Mat I) : ℝ := QAlgorithms.effectProb A rho

/-- Finite spectral log with kernel value zero; only weighted/compressed uses, pp.33,43,47. -/
def logMat (A : Mat I) : Mat I := cfc Real.log A

/-- Range inclusion, equivalently reverse kernel inclusion for self-adjoint matrices; p.43. -/
def Supports (A B : Mat I) : Prop := ∀ v : I → ℂ, B.mulVec v = 0 → A.mulVec v = 0

/-- Orthogonal supports for positive matrices, p.43. -/
def Orthogonal (A B : Mat I) : Prop := A * B = 0

/-- Signed relative entropy via the negative accepted Umegaki entropy; p.47. -/
def signedRelativeEntropy (rho nu : Mat I) : EReal :=
  -QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy rho nu

/-- Unnormalized Klein divergence, plus infinity at failed support inclusion; p.35. -/
def kleinDivergence (A B : Mat I) : EReal :=
  if Supports A B then (ev A (logMat A - logMat B) : EReal) else ⊤

/-- Extended Rényi log-overlap with the support convention at all real exponents; pp.44--45. -/
def renyi (rho nu : Mat I) (a : ℝ) : EReal :=
  ENNReal.log (ENNReal.ofReal (ev (supportPower rho a) (supportPower nu (1 - a))))

/-- Real representative for nonorthogonal states, p.45. -/
def renyiReal (rho nu : Mat I) (a : ℝ) : ℝ :=
  Real.log (ev (supportPower rho a) (supportPower nu (1 - a)))

/-- Support-compressed exponential exp(A+log nu), zero off Ran nu; p.47.
Outer projections remove the exponential's identity on the kernel. -/
def compressedExp (A nu : Mat I) : Mat I :=
  support nu * NormedSpace.exp (support nu * A * support nu + logMat nu) * support nu

/-- Trace-dual density for rho composed with Phi; pp.42,46. -/
def pullback (Phi : Mat I →ₗ[ℂ] Mat J) (rho : Mat J) : Mat I :=
  fun i j => (rho * Phi (Matrix.single j i 1)).trace

/-- k-positivity of the actual block amplification, pp.39--40. -/
def RectangularKPositive (k : ℕ) (Phi : Mat I →ₗ[ℂ] Mat J) : Prop :=
  ∀ A : Mat (Fin k × I), A.PosSemidef →
    (QAlgorithms.idTensorSuperop Phi A).PosSemidef

/-- Extended Kosaki cost. The 1/t multiplies rho(A A*); p.46. -/
def kosakiCost (rho nu : Mat I) (a : ℝ) (A : ℝ → Mat I) : EReal :=
  ENNReal.log (ENNReal.ofReal (Real.sin (Real.pi * a) / Real.pi) *
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (t ^ (a - 1) * (ev rho (A t * (A t)ᴴ) / t +
        ev nu ((1 - A t)ᴴ * (1 - A t)))))

/-- Constructed Kosaki minimizer, including the leading t; p.46. -/
def kosakiMinimizer (rho nu : Mat I) (t : ℝ) : Mat I :=
  (t : ℂ) • ∫ s in Set.Ioi (0 : ℝ),
    NormedSpace.exp ((-(s : ℂ)) • rho) * nu *
      NormedSpace.exp ((-((s * t : ℝ) : ℂ)) • nu)

/-- Heisenberg evolution exp(itH) A exp(-itH), pp.52,71. -/
def tau (H : Mat I) (t : ℝ) (A : Mat I) : Mat I :=
  propagator H (-t) * A * propagator H t

/-- Dual density evolution exp(-itH) rho exp(itH), pp.52,71. -/
def evolved (H rho : Mat I) (t : ℝ) : Mat I := tau H (-t) rho

/-- Entire complex-time dynamics, pp.52--53. -/
def complexTau (H : Mat I) (z : ℂ) (A : Mat I) : Mat I :=
  NormedSpace.exp ((Complex.I * z) • H) * A * NormedSpace.exp ((-Complex.I * z) • H)

/-- Interaction-picture propagator for H+alpha V, pp.56--57. -/
def perturbationCocycle (H V : Mat I) (a z : ℂ) : Mat I :=
  NormedSpace.exp ((Complex.I * z) • (H + a • V)) * NormedSpace.exp ((-Complex.I * z) • H)

/-- KMS condition with the source's -i beta sign, p.53 (2.24). -/
def KMS (H rho : Mat I) (beta : ℝ) : Prop :=
  ∀ A B : Mat I, (rho * (A * B)).trace =
    (rho * (complexTau H (-Complex.I * (beta : ℂ)) B * A)).trace

/-- Anti-linear involutive star-automorphism, source p.71; no real-basis restriction. -/
structure Reversal (I : Type) [Fintype I] [DecidableEq I] where
  map : Mat I →ₗ[ℝ] Mat I
  conjugate_smul : ∀ (c : ℂ) A, map (c • A) = conj c • map A
  map_one : map 1 = 1
  map_mul : ∀ A B, map (A * B) = map A * map B
  map_star : ∀ A, map (Aᴴ) = (map A)ᴴ
  involutive : ∀ A, map (map A) = A

/-- TRI conditions for a specified reversal, p.71. -/
def Reverses (Theta : Reversal I) (H omega : Mat I) : Prop :=
  (∀ t A, tau H t (Theta.map A) = Theta.map (tau H (-t) A)) ∧
  (∀ A, (omega * Theta.map A).trace = (omega * Aᴴ).trace)

/-- Existence of a source reversal, p.71. -/
def TRI (H omega : Mat I) : Prop := ∃ Theta : Reversal I, Reverses Theta H omega

/-- Relative Hamiltonian for faithful densities, p.64. -/
def relativeHamiltonian (rho nu : Mat I) : Mat I := logMat rho - logMat nu

/-- Entropy production -i[H,log omega], p.72. -/
def entropyProduction (H omega : Mat I) : Mat I :=
  (-Complex.I) • (H * logMat omega - logMat omega * H)

/-- Source time average in integral form, with oriented interval integral, p.72. -/
def averagedProduction (H omega : Mat I) (t : ℝ) : Mat I :=
  (t⁻¹ : ℝ) • ∫ s in (0 : ℝ)..t, tau H s (entropyProduction H omega)

/-- Kubo--Mori kuboMori, conjugate-linear in first slot, p.63. -/
def kuboMori (omega A B : Mat I) : ℂ :=
  ∫ u in (0 : ℝ)..1,
    (supportPower omega (1 - u) * Aᴴ * supportPower omega u * B).trace

/-- Finite-p and infinity pressure definitions, source p.74. -/
def pressure (H omega : Mat I) (p : ℝ≥0∞) (t a : ℝ) : ℝ :=
  if p = ⊤ then Real.log ((NormedSpace.exp
    (((1 - a : ℝ) : ℂ) • logMat omega + (a : ℂ) • logMat (evolved H omega t))).trace.re)
  else Real.log ((supportPower
    (supportPower omega ((1 - a) / p.toReal) *
      supportPower (evolved H omega t) (2 * a / p.toReal) *
      supportPower omega ((1 - a) / p.toReal)) (p.toReal / 2)).trace.re)

/-- Distinct real eigenvalues; degeneracy lies in the projectors, pp.32,78. -/
def eigenvalues (A : Mat I) : Finset ℝ :=
  (Finset.univ : Finset (Fin (Fintype.card I))).image (QAlgorithms.ascEigenvalues A)

/-- Spectral law of -log Delta_(rho|nu)/t in sqrt nu, p.78. -/
def modularLaw (rho nu : Mat I) (t : ℝ) : Measure ℝ :=
  ∑ l ∈ eigenvalues rho, ∑ m ∈ eigenvalues nu,
    ENNReal.ofReal (m * (QAlgorithms.spectralProjector rho l *
      QAlgorithms.spectralProjector nu m).trace.re) •
        Measure.dirac ((Real.log m - Real.log l) / t)

/-- Two-measurement law of entropy change (s'-s)/t, source p.79. -/
def fcs (H omega : Mat I) (t : ℝ) : Measure ℝ :=
  ∑ l ∈ eigenvalues omega, ∑ m ∈ eigenvalues omega,
    ENNReal.ofReal ((propagator H t * omega * QAlgorithms.spectralProjector omega l *
      propagator H (-t) * QAlgorithms.spectralProjector omega m).trace.re) •
        Measure.dirac ((Real.log l - Real.log m) / t)

/-- Cesàro stationary density constructed from H, source p.95. -/
def steady (H omega : Mat I) : Mat I :=
  ∑ l ∈ eigenvalues H, QAlgorithms.spectralProjector H l * omega * QAlgorithms.spectralProjector H l

/-- Continuous group of complex-linear star-automorphisms, source p.52. -/
def AutomorphismDynamics (T : ℝ → Mat I →ₗ[ℂ] Mat I) : Prop :=
  (∀ A, T 0 A = A) ∧ (∀ t s A, T (t + s) A = T t (T s A)) ∧
  (∀ t, T t 1 = 1) ∧ (∀ t A B, T t (A * B) = T t A * T t B) ∧
  (∀ t A, T t (Aᴴ) = (T t A)ᴴ) ∧ (∀ A, Continuous (fun t => T t A))

/-- Gibbs state at finite beta or normalized extremal spectral projection; pp.53--54. -/
def extendedGibbs (H : Mat I) (beta : EReal) : Mat I :=
  if beta = ⊤ then
    let P := QAlgorithms.spectralProjector H (sInf (↑(eigenvalues H) : Set ℝ))
    P.trace⁻¹ • P
  else if beta = ⊥ then
    let P := QAlgorithms.spectralProjector H (sSup (↑(eigenvalues H) : Set ℝ))
    P.trace⁻¹ • P
  else QAlgorithms.gibbsState ((-(beta.toReal : ℂ)) • H)

/-! Sanity examples for definition conventions; no source theorem is proved. -/

example : (if 0 < (0 : ℝ) then (0 : ℝ) ^ (0 : ℝ) else 0) = 0 := by simp

example (rho : Mat I) : Supports rho rho := by intro v h; exact h

example : entropy (0 : Mat I) = 0 := by simp [entropy, cfc_zero]

example : pullback (0 : Mat I →ₗ[ℂ] Mat J) (0 : Mat J) = 0 := by
  ext i j
  simp [pullback]

example (H : Mat I) : averagedProduction H 0 0 = 0 := by simp [averagedProduction]

example (omega : Mat I) : relativeHamiltonian omega omega = 0 := by simp [relativeHamiltonian]

example (H A : Mat I) : tau H 0 A = A := by simp [tau, propagator]

example (H V : Mat I) (a : ℂ) : perturbationCocycle H V a 0 = 1 := by simp [perturbationCocycle]

/-- Finite occupation basis, including the empty subset (vacuum); pp.116--117.
Increasing Slater determinants are orthonormal with the source's sqrt(n!) convention. -/
abbrev FermionOccupation (n : ℕ) := Finset (Fin n)

/-- Exterior-power matrix in the increasing occupation basis, direct-summed over sectors;
source pp.116--118. This is the determinant of the corresponding equal-size minor. -/
def fockGamma {n : ℕ} (A : Mat (Fin n)) : Mat (FermionOccupation n) := fun S T =>
  if h : S.card = T.card then
    Matrix.det (fun i j : Fin S.card =>
      A (S.orderEmbOfFin rfl i) (T.orderEmbOfFin rfl (Fin.cast h j)))
  else 0

/-- Left wedge creation. Inserting mode j crosses the occupied modes smaller than j;
source p.119. Duplicate occupations are excluded. -/
def creation {n : ℕ} (psi : EuclideanSpace ℂ (Fin n)) : Mat (FermionOccupation n) :=
  fun S T => ∑ j : Fin n,
    if j ∉ T ∧ S = insert j T then psi j * (-1 : ℂ) ^ (T.filter (fun k => k < j)).card else 0

/-- Annihilation is the adjoint and hence anti-linear in psi; source p.119. -/
def annihilation {n : ℕ} (psi : EuclideanSpace ℂ (Fin n)) : Mat (FermionOccupation n) := (creation psi)ᴴ

/-- Differential second quantization from the defining derivative of Gamma(exp(zA)); p.118 (6.5).
It is not defined using the conclusion of Proposition6.2(9). -/
def dGamma {n : ℕ} (A : Mat (Fin n)) : Mat (FermionOccupation n) :=
  fderiv ℂ (fun z : ℂ => fockGamma (NormedSpace.exp (z • A))) 0 1

/-- Quasi-free finite many-body density, with normalization on Fock space only; p.124. -/
def quasiFree {n : ℕ} (T : Mat (Fin n)) : Mat (FermionOccupation n) :=
  let G := fockGamma (T * (1-T)⁻¹)
  G.trace⁻¹ • G

/-- Partition function associated with the one-particle density T, source p.124. -/
def quasiFreeZ {n : ℕ} (T : Mat (Fin n)) : ℝ := (fockGamma (T * (1-T)⁻¹)).trace.re

/-- Fermi--Dirac one-particle density, without trace-one normalization; p.126. -/
def fermiDirac {n : ℕ} (h : Mat (Fin n)) (beta mu : ℝ) : Mat (Fin n) :=
  (1 + NormedSpace.exp ((beta : ℂ) • (h - (mu : ℂ) • 1)))⁻¹

/-- Commutant inside all complex matrices, source pp.59,122. -/
def matrixCommutant (S : Set (Mat I)) : Set (Mat I) := {A | ∀ B ∈ S, A*B = B*A}

example {n : ℕ} (A : Mat (Fin n)) : fockGamma A ∅ ∅ = 1 := by
  haveI : IsEmpty (Fin (∅ : Finset (Fin n)).card) := by
    simp only [Finset.card_empty]
    infer_instance
  simp only [fockGamma, dif_pos rfl]
  exact Matrix.det_isEmpty

example {n : ℕ} : creation (0 : EuclideanSpace ℂ (Fin n)) = 0 := by
  ext S T
  simp [creation]

example (S : Set (Mat I)) : (1 : Mat I) ∈ matrixCommutant S := by
  intro B hB
  simp

/-- Intrinsic p>=2 Araki--Masuda norm via relative modular powers and Hilbert--Schmidt norm;
source p.65. The maximization is over ALL normalized states, including singular ones. -/
def amUpper (omega : Mat I) (p : ℝ≥0∞) (xi : Mat I) : ℝ :=
  sSup {v | ∃ nu : Mat I, QAlgorithms.IsDensityMatrix nu ∧
    v = QAlgorithms.frobNorm (supportPower nu (1/2-inverseExponent p) * xi *
      supportPower omega (inverseExponent p-1/2))}

/-- For 1<=p<2 the norm is defined by duality, NOT by Theorem2.25's conclusion;
source p.66. The q= infinity endpoint occurs at p=1. -/
def amNorm (omega : Mat I) (p : ℝ≥0∞) (xi : Mat I) : ℝ :=
  if 2 ≤ p then amUpper omega p xi
  else sSup {v | ∃ eta : Mat I, amUpper omega ((1-p⁻¹)⁻¹) eta ≤ 1 ∧
    v = ‖(xiᴴ * eta).trace‖}

/-- Araki--Masuda cone, the image of the positive cone under the weighted map; p.66. -/
def amCone (omega : Mat I) (p : ℝ≥0∞) : Set (Mat I) :=
  {xi | ∃ A : Mat I, A.PosSemidef ∧ xi = A * supportPower omega (1/2-inverseExponent p)}

/-- The p-transfer group defined in the source, including p=infinity; p.76. -/
def transfer (H omega : Mat I) (p : ℝ≥0∞) (t : ℝ) (xi : Mat I) : Mat I :=
  propagator H t * xi * supportPower omega (-1/2+inverseExponent p) *
    propagator H (-t) * supportPower omega (1/2-inverseExponent p)

/-- The source implementation properties for a linear group; source pp.76--77. -/
def LpImplements (H omega : Mat I) (p : ℝ≥0∞) (W : ℝ → Mat I → Mat I) : Prop :=
  (∀ t A B, W t (A+B) = W t A + W t B) ∧
  (∀ t (c : ℂ) A, W t (c • A) = c • W t A) ∧
  (∀ xi, W 0 xi = xi) ∧ (∀ t s xi, W (t+s) xi = W t (W s xi)) ∧
  (∀ t xi, amNorm omega p (W t xi) = amNorm omega p xi) ∧
  (∀ t xi, xi ∈ amCone omega p → W t xi ∈ amCone omega p) ∧
  (∀ t A xi, W (-t) (A * W t xi) = tau H t A * xi)

/-- Generator H xi - xi varsigma_omega^(i(1/2-1/p))(H), in matrix-unit coordinates;
source p.77. Matrix units are orthonormal in Hilbert--Schmidt space. -/
def lpGenerator (H omega : Mat I) (p : ℝ≥0∞) : Mat (I × I) := fun x y =>
  H x.1 y.1 * (if y.2 = x.2 then 1 else 0) -
    (if x.1 = y.1 then 1 else 0) *
      (supportPower omega (inverseExponent p-1/2) * H *
        supportPower omega (1/2-inverseExponent p)) y.2 x.2

/-- Source parameter-dependent system with chosen flux decomposition; PDF p.85. -/
structure FluxFamily (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) where
  H : (Fin n → ℝ) → Mat I
  omega : (Fin n → ℝ) → Mat I
  Phi : (Fin n → ℝ) → Fin n → Mat I
  H_self : ∀ X, (H X).IsHermitian
  omega_state : ∀ X, QAlgorithms.IsDensityMatrix (omega X)
  omega_faithful : ∀ X, (omega X).PosDef
  Phi_self : ∀ X j, (Phi X j).IsHermitian
  flux_relation : ∀ X, entropyProduction (H X) (omega X) = ∑ j, (X j : ℂ) • Phi X j
  equilibrium : ∀ t, evolved (H 0) (omega 0) t = omega 0

/-- TRI includes oddness of the CHOSEN fluxes, source p.85 (3.17). -/
def FluxTRI {n : ℕ} (F : FluxFamily I n) : Prop :=
  ∀ X, ∃ Theta : Reversal I, Reverses Theta (F.H X) (F.omega X) ∧
    ∀ j, Theta.map (F.Phi X j) = -F.Phi X j

/-- Continuously differentiable parameter data for linear response; source p.87. -/
def FluxC1 {n : ℕ} (F : FluxFamily I n) : Prop :=
  ContDiff ℝ 1 F.H ∧ ContDiff ℝ 1 F.omega ∧ ∀ j, ContDiff ℝ 1 (fun X => F.Phi X j)

/-- Generalized pressure; current times are NEGATIVE as in (3.18), source p.86. -/
def generalizedPressure {n : ℕ} (F : FluxFamily I n) (X : Fin n → ℝ) (t : ℝ)
    (Y : Fin n → ℝ) : ℝ :=
  Real.log ((NormedSpace.exp (logMat (F.omega X) +
    ∑ j, (Y j : ℂ) • ∫ s in (0 : ℝ)..t, tau (F.H X) (-s) (F.Phi X j))).trace.re)

/-- Finite-time kinetic coefficient; the time average includes 1/t, source p.87. -/
def kineticCoefficient {n : ℕ} (F : FluxFamily I n) (t : ℝ) (j k : Fin n) : ℝ :=
  fderiv ℝ (fun X => t⁻¹ * ∫ s in (0 : ℝ)..t,
    ev (F.omega X) (tau (F.H X) s (F.Phi X j))) 0 (Pi.single k 1)

/-- Extension of the continuous compact-domain convex function by positive infinity; p.155. -/
def compactExtension (a b : ℝ) (e : ℝ → ℝ) (s : ℝ) : EReal :=
  if s ∈ Set.Icc a b then (e s : EReal) else ⊤

/-- Subgradient of the compact-domain extension, empty off its finite domain; p.155. -/
def subgradient (a b : ℝ) (e : ℝ → ℝ) (s theta : ℝ) : Prop :=
  s ∈ Set.Icc a b ∧ ∀ u ∈ Set.Icc a b, e s + theta*(u-s) ≤ e u

/-- Subgradient of the everywhere-finite dual function; p.155. -/
def dualSubgradient (f : ℝ → ℝ) (theta s : ℝ) : Prop :=
  ∀ eta : ℝ, f theta + s*(eta-theta) ≤ f eta

/-- The source arbitrary unbounded positive real time set, with weight exactly t; p.156. -/
structure ScalarLD where
  times : Set ℝ
  times_positive : ∀ t ∈ times, 0 < t
  times_unbounded : ∀ R : ℝ, ∃ t ∈ times, R ≤ t
  experiment : times → FiniteExperiment

/-- Limit filter on the source real time index set, p.156. -/
def timeFilter (F : ScalarLD) : Filter F.times := Filter.comap Subtype.val atTop

/-- Assumption LD on the finite interval, source p.156. -/
def ScalarHasLD (F : ScalarLD) (a b : ℝ) (e : ℝ → ℝ) : Prop :=
  QAlgorithms.Papers.Independent.Claimed50.P15.HasLD
    { index := F.times
      index_positive := F.times_positive
      index_unbounded := F.times_unbounded
      experiment := F.experiment
      weight := fun t => t.val
      weight_positive := fun t => F.times_positive t.val t.property
      weight_tendsto := Filter.map_comap_le } a b e

/-- Normalized extended log-event mass; log0=-infinity, source p.156. -/
def upperTailLog (F : ScalarLD) (theta : ℝ) (t : F.times) : EReal :=
  (((t.val)⁻¹ : ℝ) : EReal) * ENNReal.log
    ((F.experiment t).measure {x | theta*t.val < (F.experiment t).observable x})

/-- The open complex polydisk, source PDF p.163. -/
def polydisk (n : ℕ) (epsilon : ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j‖ < epsilon}

/-- Every mixed derivative, with the empty list denoting the function itself; source p.163. -/
def complexMixedPartial {n : ℕ} : List (Fin n) → ((Fin n → ℂ) → ℂ) → ((Fin n → ℂ) → ℂ)
  | [], f => f
  | j :: js, f => fun z => fderiv ℂ (complexMixedPartial js f) z (Pi.single j 1)

example (a b s : ℝ) (e : ℝ → ℝ) (h : s ∉ Set.Icc a b) :
    compactExtension a b e s = ⊤ := by simp [compactExtension, h]

example (n : ℕ) (f : (Fin n → ℂ) → ℂ) : complexMixedPartial [] f = f := rfl

/-- Left action on Hilbert--Schmidt matrix units, source p.59. -/
def leftMatrix (A : Mat I) : Mat (I × I) := fun x y =>
  A x.1 y.1 * if x.2 = y.2 then 1 else 0

/-- Right action R(A)xi=xi A*, source p.59. The dependence on A is conjugate-linear. -/
def rightMatrix (A : Mat I) : Mat (I × I) := fun x y =>
  (if x.1 = y.1 then 1 else 0) * conj (A x.2 y.2)

/-- Matrix of conjugation X -> J X J on Hilbert--Schmidt operators; Jxi=xi*, source p.60. -/
def conjugateByJ (X : Mat (I × I)) : Mat (I × I) := fun x y =>
  conj (X (x.2,x.1) (y.2,y.1))

example (A : Mat I) (i j k l : I) :
    rightMatrix A (i,j) (k,l) = (if i = k then 1 else 0) * conj (A j l) := rfl

/-- Nonfaithful relative modular operator rho xi nu^(-1), where the inverse is zero
on the kernel; source p.67. Indices identify Hilbert--Schmidt matrix units. -/
def relativeModularMatrix (rho nu : Mat I) : Mat (I × I) := fun x y =>
  rho x.1 y.1 * supportPower nu (-1) y.2 x.2

/-- Spectral measure of Delta itself in sqrt nu, not of log Delta or its time scaling;
source pp.67,69. -/
def relativeModularMeasure (rho nu : Mat I) : Measure ℝ :=
  let D := relativeModularMatrix rho nu
  let v : I × I → ℂ := fun x => supportPower nu (1/2) x.1 x.2
  ∑ l ∈ eigenvalues D,
    ENNReal.ofReal ((∑ x, conj (v x) *
      ((QAlgorithms.spectralProjector D l).mulVec v) x).re) • Measure.dirac l

/-- Projection tests accept rho on outcome one, source p.50. -/
def ProjectionTest (P : Mat I) : Prop := P.IsHermitian ∧ P*P = P

/-- Minimal Bayesian error with prior p for rho, source p.50.
The admissible set contains zero; normalized states bound errors in [0,1], so the real
infimum has no empty/unbounded default in any theorem use. -/
def optimalTestingError (p : ℝ) (rho nu : Mat I) : ℝ :=
  sInf {v | ∃ P : Mat I, ProjectionTest P ∧ v = p*ev rho (1-P)+(1-p)*ev nu P}

example : ProjectionTest (0 : Mat I) := by simp [ProjectionTest, Matrix.IsHermitian]

example : supportPower (0 : Mat I) (0 : ℝ) = 0 := by simp [supportPower, cfc_zero]

example (A : Mat I) : schattenNorm ⊤ A = QAlgorithms.specNorm A := by
  simp [schattenNorm]

example (rho : Mat I) : relativeModularMatrix rho 0 = 0 := by
  ext x y
  simp [relativeModularMatrix, supportPower, cfc_zero]

end QAlgorithms.Papers.Independent.Next46.P23


