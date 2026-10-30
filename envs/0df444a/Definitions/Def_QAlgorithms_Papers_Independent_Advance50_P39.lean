-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39
-- name    : QAlgorithms_Papers_Independent_Advance50_P39
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:56:59.166361+00:00
-- url     : https://prove2.me/theorems/fc23efdf-8f18-4b6c-8918-181ad3c601dd
-- title:
--   Definitions for Role of quantum coherence in chromophoric energy transport
-- statement:
--   The objects the formalized statements of *Role of quantum coherence in chromophoric energy transport* (arXiv:0806.4725) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SiteMatrix`: PDF pp.1--2: single-excitation matrices in the site basis.
--   - `Superoperator`: PDF p.1: complex-linear superoperators.
--   - `TransportData`: PDF pp.1--2: finite constant transport data. H includes H_S and H_LS. Jump matrices absorb nonnegative rates. This is the intended trace-preserving Lindblad assumption, not a derivation of the specific phonon formula.
--   - `recombinationHamiltonian`: PDF p.2: H_recomb = hbar Gamma I.
--   - `trappingHamiltonian`: PDF p.2: H_trap = hbar diag(kappa).
--   - `phononGenerator`: PDF p.2, Eq. (4): intended trace-preserving phonon term, in canonical GKSL form. Printed Eq. (5) instead orders its loss products A_m A_n^dagger; using A_n^dagger A_m here is an explicit source correction pending independent moderation.
--   - `transportRemainder`: PDF pp.2--3: R is the coherent commutator plus the phonon term.
--   - `referenceGenerator`: PDF p.2: A = H_ref is the recombination-trapping anticommutator action.
--   - `transportGenerator`: PDF pp.1--2, Eqs. (1),(4): M=A+R, with no later renormalization.
--   - `transportState`: PDF pp.1--2: unnormalized surviving excitation block from fixed rho0. Uses the accepted constant-generator exponential semigroupEvolution. The frozen Information100.P32.trajectory instead iterates a discrete qubit collision channel and cannot represent this continuous-time, arbitrary-site transport state.
--   - `lossFlux`: PDF p.2, Eq. (6): (2/hbar) Re Tr(H rho).
--   - `efficiency`: PDF p.2, Eq. (6): trapping probability; integrability is a theorem conclusion.
--   - `deficiency`: PDF p.2: recombination probability; integrability is a theorem conclusion.
--   - `referenceInverse`: PDF pp.2--3: explicit inverse of A on matrix entries. The denominator 2 Gamma+kappa_i+kappa_j is positive; hbar cancels from A.
--   - `greenContribution`: PDF p.3, Eq. (9): -2/hbar Re Tr(H_recomb A^{-1} B M^{-1}rho0). The inverse is of the superoperator, never of rho0. Ring.inverse is totalized; the inverse-efficiency theorem concludes that M is a unit.
--   - `spatialCorrelation`: PDF pp.4--5: exp(-distance/radius), used for positive radius only.
--   - `ExcitonData`: PDF p.2: complete orthonormal bases U_mM=c_m(M), with possibly degenerate energies. Frequencies follow the printed E_M-E_N=hbar omega convention.
--   - `siteTransition`: PDF p.2 following Eq. (5): site-projector transition A_m(omega) in exciton coordinates.
--   - `bohrFrequencies`: PDF p.2: finite set of transition frequencies, including zero.
--   - `printedPhononAt`: PDF p.2, literal Eq. (5) at one frequency. The loss order A_m A_n^dagger is deliberately retained ONLY to state its zero perfectly correlated endpoint. This is not the physical phononGenerator used above.
--   - `printedPhonon`: PDF p.2: frequency sum of literal Eq. (5); no singular Bose formula is evaluated.
--   - `insertionIntegrand`: PDF p.5, Eq. (10): ordered pre-evolution, insertion and post-evolution.
--   - `averagedInsertion`: PDF p.5, Eq. (10): average insertion; interpreted only for t>0.
--   - `processScaledState`: PDF p.5: actual trajectory when one real multiplier varies and all others stay one. The initial matrix is fixed independently of the multiplier.
--   - `susceptibility`: PDF p.5: real coordinate derivative at multiplier one, with complex outputs.
--   - `positiveIndices`: PDF pp.5--6: strict positive sign class.
--   - `negativeIndices`: PDF pp.5--6: strict negative sign class.
--   - `normalizedContribution`: PDF p.6, Eq. (12): ratio within one sign class. Empty classes have no percentage interpretation; the theorem requires a nonempty strict sign class.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, https://arxiv.org/abs/0806.4725v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

/-! Statements from arXiv:0806.4725v2. New definitions are local to this paper; accepted matrix operations are imported.
Only theorem statements contain sorry. Compilation and independent moderation
are pending. Generic transport uses the intended trace-preserving Lindblad model;
the literal defective Eq. (5) is retained only for its zero endpoint. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--2: single-excitation matrices in the site basis. -/
abbrev SiteMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- PDF p.1: complex-linear superoperators. -/
abbrev Superoperator (n : ℕ) := Module.End ℂ (SiteMatrix n)

example {n : ℕ} (A B X : SiteMatrix n) : sandwich A B X = A * (X * B) := rfl

/-- PDF pp.1--2: finite constant transport data. H includes H_S and H_LS.
Jump matrices absorb nonnegative rates. This is the intended trace-preserving
Lindblad assumption, not a derivation of the specific phonon formula. -/
structure TransportData (n : ℕ) where
  sites_positive : 0 < n
  hbar : ℝ
  hbar_positive : 0 < hbar
  gamma : ℝ
  gamma_positive : 0 < gamma
  kappa : Fin n → ℝ
  kappa_nonnegative : ∀ i, 0 ≤ kappa i
  hamiltonian : SiteMatrix n
  hamiltonian_hermitian : hamiltonian.IsHermitian
  jumpCount : ℕ
  jump : Fin jumpCount → SiteMatrix n

/-- PDF p.2: H_recomb = hbar Gamma I. -/
def recombinationHamiltonian {n : ℕ} (D : TransportData n) : SiteMatrix n :=
  (D.hbar * D.gamma : ℂ) • (1 : SiteMatrix n)

/-- PDF p.2: H_trap = hbar diag(kappa). -/
def trappingHamiltonian {n : ℕ} (D : TransportData n) : SiteMatrix n :=
  Matrix.diagonal (fun i => (D.hbar * D.kappa i : ℂ))

example {n : ℕ} (D : TransportData n) (i : Fin n) :
    trappingHamiltonian D i i = (D.hbar * D.kappa i : ℂ) := by
  simp [trappingHamiltonian]

/-- PDF p.2, Eq. (4): intended trace-preserving phonon term, in canonical GKSL
form. Printed Eq. (5) instead orders its loss products A_m A_n^dagger; using
A_n^dagger A_m here is an explicit source correction pending independent moderation. -/
def phononGenerator {n : ℕ} (D : TransportData n) : Superoperator n :=
  ∑ j, (sandwich (D.jump j) (D.jump j)ᴴ - (1 / 2 : ℂ) •
    (LinearMap.mulLeft ℂ ((D.jump j)ᴴ * D.jump j) +
      LinearMap.mulRight ℂ ((D.jump j)ᴴ * D.jump j)))

/-- PDF pp.2--3: R is the coherent commutator plus the phonon term. -/
def transportRemainder {n : ℕ} (D : TransportData n) : Superoperator n :=
  (-Complex.I / (D.hbar : ℂ)) •
    (LinearMap.mulLeft ℂ D.hamiltonian - LinearMap.mulRight ℂ D.hamiltonian) +
      phononGenerator D

/-- PDF p.2: A = H_ref is the recombination-trapping anticommutator action. -/
def referenceGenerator {n : ℕ} (D : TransportData n) : Superoperator n :=
  (-(D.hbar : ℂ)⁻¹) •
    (LinearMap.mulLeft ℂ (recombinationHamiltonian D + trappingHamiltonian D) +
      LinearMap.mulRight ℂ (recombinationHamiltonian D + trappingHamiltonian D))

/-- PDF pp.1--2, Eqs. (1),(4): M=A+R, with no later renormalization. -/
def transportGenerator {n : ℕ} (D : TransportData n) : Superoperator n :=
  referenceGenerator D + transportRemainder D

/-- PDF pp.1--2: unnormalized surviving excitation block from fixed rho0.
Uses the accepted constant-generator exponential semigroupEvolution. The frozen
Information100.P32.trajectory instead iterates a discrete qubit collision channel
and cannot represent this continuous-time, arbitrary-site transport state. -/
def transportState {n : ℕ} (G : Superoperator n) (rho0 : SiteMatrix n) (t : ℝ) :
    SiteMatrix n := semigroupEvolution G t rho0

example {n : ℕ} (G : Superoperator n) (rho0 : SiteMatrix n) :
    transportState G rho0 0 = rho0 := by
  change (NormedSpace.exp ((0 : ℂ) • LinearMap.toContinuousLinearMap G)) rho0 = rho0
  have hzero : (0 : ℂ) • LinearMap.toContinuousLinearMap G = 0 :=
    zero_smul ℂ (LinearMap.toContinuousLinearMap G)
  rw [hzero, NormedSpace.exp_zero]
  rfl

/-- PDF p.2, Eq. (6): (2/hbar) Re Tr(H rho). -/
def lossFlux {n : ℕ} (D : TransportData n) (H X : SiteMatrix n) : ℝ :=
  (2 / D.hbar) * (H * X).trace.re

/-- PDF p.2, Eq. (6): trapping probability; integrability is a theorem conclusion. -/
def efficiency {n : ℕ} (D : TransportData n) (rho0 : SiteMatrix n) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    lossFlux D (trappingHamiltonian D) (transportState (transportGenerator D) rho0 t)

/-- PDF p.2: recombination probability; integrability is a theorem conclusion. -/
def deficiency {n : ℕ} (D : TransportData n) (rho0 : SiteMatrix n) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    lossFlux D (recombinationHamiltonian D) (transportState (transportGenerator D) rho0 t)

example {n : ℕ} (D : TransportData n) (H : SiteMatrix n) :
    lossFlux D H 0 = 0 := by simp [lossFlux]

/-- PDF pp.2--3: explicit inverse of A on matrix entries. The denominator
2 Gamma+kappa_i+kappa_j is positive; hbar cancels from A. -/
def referenceInverse {n : ℕ} (D : TransportData n) (X : SiteMatrix n) : SiteMatrix n :=
  fun i j => -(X i j) / ((2 * D.gamma + D.kappa i + D.kappa j : ℝ) : ℂ)

example {n : ℕ} (D : TransportData n) : referenceInverse D 0 = 0 := by
  ext i j
  simp [referenceInverse]

/-- PDF p.3, Eq. (9): -2/hbar Re Tr(H_recomb A^{-1} B M^{-1}rho0).
The inverse is of the superoperator, never of rho0. Ring.inverse is totalized;
the inverse-efficiency theorem concludes that M is a unit. -/
def greenContribution {n : ℕ} (D : TransportData n) (B : Superoperator n)
    (rho0 : SiteMatrix n) : ℝ :=
  -(2 / D.hbar) * (recombinationHamiltonian D *
    referenceInverse D (B (Ring.inverse (transportGenerator D) rho0))).trace.re

/-- PDF pp.4--5: exp(-distance/radius), used for positive radius only. -/
def spatialCorrelation (distance radius : ℝ) : ℝ := Real.exp (-distance / radius)

example (radius : ℝ) : spatialCorrelation 0 radius = 1 := by
  simp [spatialCorrelation]

/-- PDF p.2: complete orthonormal bases U_mM=c_m(M), with possibly degenerate
energies. Frequencies follow the printed E_M-E_N=hbar omega convention. -/
structure ExcitonData (n : ℕ) where
  sites_positive : 0 < n
  hbar : ℝ
  hbar_positive : 0 < hbar
  basisChange : Matrix.unitaryGroup (Fin n) ℂ
  energy : Fin n → ℝ

/-- PDF p.2 following Eq. (5): site-projector transition A_m(omega) in exciton coordinates. -/
def siteTransition {n : ℕ} (D : ExcitonData n) (m : Fin n) (omega : ℝ) : SiteMatrix n :=
  fun a b => if D.energy a - D.energy b = D.hbar * omega then
    star ((D.basisChange : SiteMatrix n) m a) * (D.basisChange : SiteMatrix n) m b else 0

/-- PDF p.2: finite set of transition frequencies, including zero. -/
def bohrFrequencies {n : ℕ} (D : ExcitonData n) : Finset ℝ :=
  Finset.univ.image (fun ab : Fin n × Fin n => (D.energy ab.1 - D.energy ab.2) / D.hbar)

example {n : ℕ} (D : ExcitonData n) (m a b : Fin n) (omega : ℝ)
    (h : D.energy a - D.energy b ≠ D.hbar * omega) :
    siteTransition D m omega a b = 0 := by simp [siteTransition, h]

/-- PDF p.2, literal Eq. (5) at one frequency. The loss order A_m A_n^dagger
is deliberately retained ONLY to state its zero perfectly correlated endpoint.
This is not the physical phononGenerator used above. -/
def printedPhononAt {n : ℕ} (D : ExcitonData n) (C : Matrix (Fin n) (Fin n) ℝ)
    (g : ℝ → ℝ) (omega : ℝ) (X : SiteMatrix n) : SiteMatrix n :=
  ∑ m, ∑ k, (g omega * C m k : ℂ) •
    (siteTransition D m omega * X * (siteTransition D k omega)ᴴ - (1 / 2 : ℂ) •
      (siteTransition D m omega * (siteTransition D k omega)ᴴ * X +
        X * siteTransition D m omega * (siteTransition D k omega)ᴴ))

/-- PDF p.2: frequency sum of literal Eq. (5); no singular Bose formula is evaluated. -/
def printedPhonon {n : ℕ} (D : ExcitonData n) (C : Matrix (Fin n) (Fin n) ℝ)
    (g : ℝ → ℝ) (X : SiteMatrix n) : SiteMatrix n :=
  ∑ omega ∈ bohrFrequencies D, printedPhononAt D C g omega X

example {n : ℕ} (D : ExcitonData n) (g : ℝ → ℝ) (omega : ℝ) (X : SiteMatrix n) :
    printedPhononAt D 0 g omega X = 0 := by simp [printedPhononAt]

/-- PDF p.5, Eq. (10): ordered pre-evolution, insertion and post-evolution. -/
def insertionIntegrand {n : ℕ} (G B : Superoperator n) (rho0 : SiteMatrix n)
    (t s : ℝ) : SiteMatrix n := semigroupEvolution G (t - s) (B (semigroupEvolution G s rho0))

/-- PDF p.5, Eq. (10): average insertion; interpreted only for t>0. -/
def averagedInsertion {n : ℕ} (G B : Superoperator n) (rho0 : SiteMatrix n)
    (t : ℝ) : SiteMatrix n :=
  (t⁻¹ : ℂ) • ∫ s in (0 : ℝ)..t, insertionIntegrand G B rho0 t s

example {n : ℕ} (G B : Superoperator n) (rho0 : SiteMatrix n) (t s : ℝ) :
    insertionIntegrand G B rho0 t s = semigroupEvolution G (t - s) (B (semigroupEvolution G s rho0)) := rfl

/-- PDF p.5: actual trajectory when one real multiplier varies and all others
stay one. The initial matrix is fixed independently of the multiplier. -/
def processScaledState {n r : ℕ} (parts : Fin r → Superoperator n)
    (rho0 : SiteMatrix n) (k : Fin r) (lambda t : ℝ) : SiteMatrix n :=
  transportState (∑ j, ((if j = k then lambda else 1 : ℝ) : ℂ) • parts j) rho0 t

/-- PDF p.5: real coordinate derivative at multiplier one, with complex outputs. -/
def susceptibility {n r : ℕ} (parts : Fin r → Superoperator n)
    (rho0 : SiteMatrix n) (k : Fin r) (t : ℝ) : SiteMatrix n :=
  deriv (fun lambda : ℝ => processScaledState parts rho0 k lambda t) 1

example {n r : ℕ} (parts : Fin r → Superoperator n) (rho0 : SiteMatrix n)
    (k : Fin r) (lambda : ℝ) : processScaledState parts rho0 k lambda 0 = rho0 := by
  change (NormedSpace.exp ((0 : ℂ) • LinearMap.toContinuousLinearMap
    (∑ j, ((if j = k then lambda else 1 : ℝ) : ℂ) • parts j))) rho0 = rho0
  have hzero : (0 : ℂ) • LinearMap.toContinuousLinearMap
      (∑ j, ((if j = k then lambda else 1 : ℝ) : ℂ) • parts j) = 0 :=
    zero_smul ℂ (LinearMap.toContinuousLinearMap
      (∑ j, ((if j = k then lambda else 1 : ℝ) : ℂ) • parts j))
  rw [hzero, NormedSpace.exp_zero]
  rfl

/-- PDF pp.5--6: strict positive sign class. -/
def positiveIndices {r : ℕ} (eta : Fin r → ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun k => 0 < eta k)

/-- PDF pp.5--6: strict negative sign class. -/
def negativeIndices {r : ℕ} (eta : Fin r → ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun k => eta k < 0)

/-- PDF p.6, Eq. (12): ratio within one sign class. Empty classes have no
percentage interpretation; the theorem requires a nonempty strict sign class. -/
def normalizedContribution {r : ℕ} (eta : Fin r → ℝ) (s : Finset (Fin r)) (k : Fin r) : ℝ :=
  eta k / ∑ j ∈ s, eta j

example : normalizedContribution (fun _ : Fin 1 => (-2 : ℝ)) Finset.univ 0 = 1 := by
  norm_num [normalizedContribution]

end QAlgorithms.Papers.Independent.Advance50.P39


