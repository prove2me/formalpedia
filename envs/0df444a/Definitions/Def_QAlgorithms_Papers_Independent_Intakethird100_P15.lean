-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P15
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P15
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:02:33.725143+00:00
-- url     : https://prove2.me/theorems/53fb9705-63cf-4abd-b073-fabab2bc1837
-- title:
--   Definitions for A Quantum Fluctuation Theorem
-- statement:
--   The objects the formalized statements of *A Quantum Fluctuation Theorem* (arXiv:cond-mat/0007360) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RealSpectralHamiltonian`: PDF p.2, (1): a spectral presentation of a self-adjoint Hamiltonian real in `b`. The operator is multiplication by `energy` on {f : L2 | energy * f belongs to L2}, transported through `transform`. Real basis images specify the SAME conjugation for all Hamiltonians; no boundedness or pure-point condition is imposed here.
--   - `IsSpectralStep`: PDF p.2, (2): the spectral meaning of exp(+i tau H / hbar). This is an actual spectral-integral specification of a unitary, not a reversal axiom.
--   - `chronologicalEvolution`: PDF p.2, (2): chronological list action, the first list entry acting first.
--   - `sliceTime`: Midpoint of a uniform slicing of `cycles` periods, at the symmetry origin. Using n+1 slices avoids any natural division by zero.
--   - `CyclicDrive`: PDF p.2, (1)--(3): real, periodic, reflection-symmetric drive at its symmetry origin, evolved for a natural number of full cycles. `hamiltonian` is spectral data for the actual time-dependent Hamiltonian. Representations of identical Hamiltonians are chosen consistently. `slices` are specified by the positive-sign exponential in (2); `evolution_limit` asserts its strong limit is the given unitary.
--   - `IsInitialEnergyBasis`: PDF pp.2--3, (4): the complete `b` basis diagonalizes the initial Hamiltonian. The spectral support equation entails that each basis vector lies in its maximal domain and has eigenvalue `energy i`, including all eigenvalue multiplicities.
--   - `heatTrace`: PDF p.3, (5): the scalar heat trace, only used with a summability guard.
--   - `HasFiniteHeatTraces`: PDF p.4 after (13): finite heat trace at EVERY positive inverse temperature.
--   - `spectralGibbsWeight`: PDF p.3: normalized canonical probability on a possibly infinite spectral basis. This extends Information100.P44.gibbsWeight, whose domain is only Fin d; the finite specialization is checked below. Heat-trace summability guards all uses.
--   - `preparedWorkLaw`: PDF p.3, (8): atomic work law for specified initial weights. The pair is (initial, final); work is FINAL minus INITIAL, for the same observable.
--   - `workLaw`: PDF p.3, (8): the actual canonical two-measurement law.
--   - `qTerm`: PDF pp.3--4, (10): one term of the UNNORMALIZED spectral trace. It equals exp(lambda epsilon_g) |U_ga|^2 exp(-(lambda+beta)epsilon_a).
--   - `generatingTrace`: PDF p.3, (10)--(11): the spectral trace Q, not Q/Z. All theorems using its values explicitly assert convergence in their domain.
--   - `CommonTraceDomain`: PDF p.3, (11): the three series whose values occur in the KMS-like identity. Unconditional complex summability excludes the default value of a divergent tsum.
--   - `bathObservedEnergy`: PDF pp.5--6, (22)--(23): product-basis spectrum of H_bath tensor I + I tensor O.
--   - `bathPreparation`: PDF pp.5--6: independent canonical bath and system-O preparation. The system probabilities are determined by O and beta, rather than freely chosen.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, https://arxiv.org/abs/cond-mat/0007360v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

/-!
# Kurchan, A Quantum Fluctuation Theorem (cond-mat/0007360v2)

The measurable spectral representation below represents a real self-adjoint Hamiltonian
as multiplication by a real function, on its maximal multiplication domain. It permits
unbounded operators and continuous intermediate spectra. Only the measured observable
has a countable complete eigenbasis. No time-reversal identity is assumed of the drive.
The strong-limit hypothesis is the well-defined infinitesimal-slicing evolution of (2).
New spectral interfaces are local to this paper. Generic transition probabilities,
measure reflection and extended expectation are imported from the pinned accepted
library. The finite Gibbs definition is imported and matched by the countable
spectral extension below; a finite-dimensional replacement would lose source scope.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P15

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Information100.P37 (transition)
open QAlgorithms.Papers.Independent.Support21.P03 (reflectedLaw)
open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation)
open scoped ENNReal Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

/-- PDF p.2, (1): a spectral presentation of a self-adjoint Hamiltonian real in `b`.
The operator is multiplication by `energy` on {f : L2 | energy * f belongs to L2},
transported through `transform`. Real basis images specify the SAME conjugation
for all Hamiltonians; no boundedness or pure-point condition is imposed here. -/
structure RealSpectralHamiltonian (b : HilbertBasis ι ℂ E) where
  measure : Measure Ω
  energy : Ω → ℝ
  energy_measurable : Measurable energy
  transform : E ≃ₗᵢ[ℂ] Lp ℂ 2 measure
  real_basis : ∀ i, ∀ᵐ x ∂measure, (transform (b i) x).im = 0

/-- PDF p.2, (2): the spectral meaning of exp(+i tau H / hbar).
This is an actual spectral-integral specification of a unitary, not a reversal axiom. -/
def IsSpectralStep (b : HilbertBasis ι ℂ E) (H : RealSpectralHamiltonian (Ω := Ω) b)
    (tau hbar : ℝ) (V : E ≃ₗᵢ[ℂ] E) : Prop :=
  ∀ x y : E, inner ℂ x (V y) =
    ∫ s, star (H.transform x s) *
      Complex.exp (Complex.I * ((tau / hbar * H.energy s : ℝ) : ℂ)) *
      H.transform y s ∂H.measure

/-- PDF p.2, (2): chronological list action, the first list entry acting first. -/
def chronologicalEvolution (L : List (E ≃ₗᵢ[ℂ] E)) : E ≃ₗᵢ[ℂ] E :=
  L.foldl (fun A B => A.trans B) (LinearIsometryEquiv.refl ℂ E)

/-- Midpoint of a uniform slicing of `cycles` periods, at the symmetry origin.
Using n+1 slices avoids any natural division by zero. -/
noncomputable def sliceTime (period : ℝ) (cycles n : ℕ) (r : Fin (n + 1)) : ℝ :=
  ((r.val : ℝ) + 1 / 2) * ((cycles : ℝ) * period / ((n + 1 : ℕ) : ℝ))

/-- PDF p.2, (1)--(3): real, periodic, reflection-symmetric drive at its symmetry
origin, evolved for a natural number of full cycles. `hamiltonian` is spectral data
for the actual time-dependent Hamiltonian. Representations of identical Hamiltonians
are chosen consistently. `slices` are specified by the positive-sign exponential
in (2); `evolution_limit` asserts its strong limit is the given unitary. -/
structure CyclicDrive (b : HilbertBasis ι ℂ E) where
  period : ℝ
  period_pos : 0 < period
  hbar : ℝ
  hbar_pos : 0 < hbar
  cycles : ℕ
  hamiltonian : ℝ → RealSpectralHamiltonian (Ω := Ω) b
  periodic : ∀ t, hamiltonian (t + period) = hamiltonian t
  reflection : ∀ t, hamiltonian (-t) = hamiltonian t
  slices : ∀ n : ℕ, Fin (n + 1) → E ≃ₗᵢ[ℂ] E
  slices_spec : ∀ n r, IsSpectralStep b
    (hamiltonian (sliceTime period cycles n r))
    ((cycles : ℝ) * period / ((n + 1 : ℕ) : ℝ)) hbar (slices n r)
  evolution : E ≃ₗᵢ[ℂ] E
  evolution_limit : ∀ x : E,
    Tendsto (fun n => chronologicalEvolution (List.ofFn (slices n)) x)
      atTop (𝓝 (evolution x))

/-- PDF pp.2--3, (4): the complete `b` basis diagonalizes the initial Hamiltonian.
The spectral support equation entails that each basis vector lies in its maximal
domain and has eigenvalue `energy i`, including all eigenvalue multiplicities. -/
def IsInitialEnergyBasis (b : HilbertBasis ι ℂ E)
    (d : CyclicDrive (Ω := Ω) b) (energy : ι → ℝ) : Prop :=
  ∀ i, ∀ᵐ s ∂(d.hamiltonian 0).measure,
    ((d.hamiltonian 0).energy s : ℂ) * (d.hamiltonian 0).transform (b i) s =
      (energy i : ℂ) * (d.hamiltonian 0).transform (b i) s

/-- PDF p.3, (5): the scalar heat trace, only used with a summability guard. -/
noncomputable def heatTrace (energy : ι → ℝ) (t : ℝ) : ℝ :=
  ∑' i, Real.exp (-t * energy i)

/-- PDF p.4 after (13): finite heat trace at EVERY positive inverse temperature. -/
def HasFiniteHeatTraces (energy : ι → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → Summable (fun i => Real.exp (-t * energy i))

/-- PDF p.3: normalized canonical probability on a possibly infinite spectral basis.
This extends Information100.P44.gibbsWeight, whose domain is only Fin d; the
finite specialization is checked below. Heat-trace summability guards all uses. -/
noncomputable def spectralGibbsWeight (energy : ι → ℝ) (beta : ℝ) (i : ι) : ℝ :=
  Real.exp (-beta * energy i) / heatTrace energy beta

/-- PDF p.3, (8): atomic work law for specified initial weights.
The pair is (initial, final); work is FINAL minus INITIAL, for the same observable. -/
noncomputable def preparedWorkLaw (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy weights : ι → ℝ) : Measure ℝ :=
  Measure.sum (fun p : ι × ι =>
    ENNReal.ofReal (weights p.1 * transition (fun g a => inner ℂ (b g) (U (b a))) p.2 p.1) •
      Measure.dirac (energy p.2 - energy p.1))

/-- PDF p.3, (8): the actual canonical two-measurement law. -/
noncomputable def workLaw (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy : ι → ℝ) (beta : ℝ) : Measure ℝ :=
  preparedWorkLaw b U energy (spectralGibbsWeight energy beta)

/-- PDF pp.3--4, (10): one term of the UNNORMALIZED spectral trace.
It equals exp(lambda epsilon_g) |U_ga|^2 exp(-(lambda+beta)epsilon_a). -/
noncomputable def qTerm (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy : ι → ℝ) (beta : ℝ) (z : ℂ) (p : ι × ι) : ℂ :=
  Complex.exp (z * ((energy p.2 - energy p.1 : ℝ) : ℂ)) *
    (transition (fun g a => inner ℂ (b g) (U (b a))) p.2 p.1 * Real.exp (-beta * energy p.1) : ℝ)

/-- PDF p.3, (10)--(11): the spectral trace Q, not Q/Z.
All theorems using its values explicitly assert convergence in their domain. -/
noncomputable def generatingTrace (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy : ι → ℝ) (beta : ℝ) (z : ℂ) : ℂ :=
  ∑' p : ι × ι, qTerm b U energy beta z p

/-- PDF p.3, (11): the three series whose values occur in the KMS-like identity.
Unconditional complex summability excludes the default value of a divergent tsum. -/
def CommonTraceDomain (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy : ι → ℝ) (beta : ℝ) (z : ℂ) : Prop :=
  Summable (qTerm b U energy beta z) ∧
  Summable (qTerm b U energy beta (-z - (beta : ℂ))) ∧
  Summable (qTerm b U energy beta (-star z - (beta : ℂ)))

/-- PDF pp.5--6, (22)--(23): product-basis spectrum of H_bath tensor I + I tensor O. -/
def bathObservedEnergy {B S : Type*} (bathEnergy : B → ℝ) (systemO : S → ℝ)
    (p : B × S) : ℝ :=
  bathEnergy p.1 + systemO p.2

/-- PDF pp.5--6: independent canonical bath and system-O preparation.
The system probabilities are determined by O and beta, rather than freely chosen. -/
noncomputable def bathPreparation {B S : Type*} (bathEnergy : B → ℝ)
    (systemO : S → ℝ) (beta : ℝ) (p : B × S) : ℝ :=
  spectralGibbsWeight bathEnergy beta p.1 * spectralGibbsWeight systemO beta p.2

/-! Sanity examples: conventions and domains, not proofs of the paper's results. -/

example : chronologicalEvolution ([] : List (E ≃ₗᵢ[ℂ] E)) =
    LinearIsometryEquiv.refl ℂ E := rfl

example (period : ℝ) (n : ℕ) (r : Fin (n + 1)) : sliceTime period 0 n r = 0 := by
  simp [sliceTime]

example (energy : ι → ℝ) (beta : ℝ) (i : ι) :
    spectralGibbsWeight energy beta i = Real.exp (-beta * energy i) / heatTrace energy beta := rfl

example {n : ℕ} (energy : Fin n → ℝ) (beta : ℝ) (i : Fin n) :
    spectralGibbsWeight energy beta i =
      QAlgorithms.Papers.Independent.Information100.P44.gibbsWeight energy beta i := by
  simp [spectralGibbsWeight, heatTrace, tsum_fintype,
    QAlgorithms.Papers.Independent.Information100.P44.gibbsWeight]

example (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E) (en : ι → ℝ)
    (beta : ℝ) (p : ι × ι) :
    qTerm b U en beta 0 p =
      (transition (fun g a => inner ℂ (b g) (U (b a))) p.2 p.1 * Real.exp (-beta * en p.1) : ℝ) := by
  simp [qTerm]

example (P : Measure ℝ) : extendedExpectation P (fun _ => 0) = 0 := by
  simp [extendedExpectation]

example {B S : Type*} (eb : B → ℝ) (o : S → ℝ) (a g : B × S) :
    bathObservedEnergy eb o g - bathObservedEnergy eb o a =
      (eb g.1 + o g.2) - (eb a.1 + o a.2) := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P15


