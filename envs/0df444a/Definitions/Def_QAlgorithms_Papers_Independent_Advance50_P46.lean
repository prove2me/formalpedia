-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46
-- name    : QAlgorithms_Papers_Independent_Advance50_P46
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T22:06:46.398816+00:00
-- url     : https://prove2.me/theorems/91e933a0-883f-4b16-8359-b6776eee4927
-- title:
--   Definitions for Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions
-- statement:
--   The objects the formalized statements of *Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions* (arXiv:1810.00863) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `zetaAlpha`: PDF pp.11,17, (3.1): the endpoint alpha=1 is prescribed separately.
--   - `formGround`: PDF p.7: bottom of a positive observable, using finite unit-vector form energies. Density of the form domain makes this set nonempty on a nonzero Hilbert space.
--   - `diagonalMagnitude`: PDF p.10: alpha-ECD for diagonal positive spectral observables, including N,M. This definition is used only for the explicit bosonic channels, never to restrict an arbitrary self-adjoint Hamiltonian to pure point spectrum.
--   - `realSpectrumMeanEnergy`: PDF pp.27,43: extended spectral energy, used for arbitrary (also infinite-energy) initial states. All energy lists supplied to this definition are nonnegative.
--   - `numberEigenvalue`: PDF p.27: the number spectrum, with the vacuum at n=0.
--   - `amplifierEnergy`: PDF p.28: M=aa*=N+I, whose bottom is 1.
--   - `coefficientKrausTerm`: PDF p.27: coefficient action of the accepted bounded Kraus matrices. On trace class the scalar series converge absolutely, and the Kraus sum converges in trace norm. The source theorems below include the latter convergence explicitly.
--   - `TraceSums`: PDF p.27: unconditional trace-norm summation, not coefficientwise convergence.
--   - `attenuatorTerm`: PDF p.27: attenuation uses amplitude exp(-t/2), as fixed by the Kraus series and generator there and the photon-number law on p.43. The conflicting amplitude exp(-t) of (1.2) is deferred, not asserted for this channel.
--   - `attenuatorTimeKernel`: PDF p.27: time adapter for the frozen vacuum attenuator; amplitude exp(-t/2). On trace class this is the countable Kraus sum, including t=0.
--   - `amplifierTerm`: PDF pp.27--28: quantum-limited amplifier with amplitude gain exp(t/2). Its generator is a* rho a - {N+I,rho}/2. No Latt-I identity is used.
--   - `amplifierTimeKernel`: PDF pp.27--28: time adapter for the frozen full amplifier coefficient kernel. The accepted intensity gain is exp(t), hence amplitude gain exp(t/2).
--   - `bosonicCoefficient`: PDF pp.27--28: common explicit bosonic Holder coefficient.
--   - `schattenPower`: PDF pp.35--36: Schatten-q power on self-adjoint trace-class arrays, defined by all finite coordinate compressions using the frozen finite Schatten norm. For self-adjoint differences this equals the |x|^q functional calculus. The extended supremum is finite for q>=1 on trace class.
--   - `traceClassSchattenQNorm`: PDF p.35: real Schatten norm, used only for q>1 and trace-class self-adjoint inputs, where finiteness precedes conversion to a real number mathematically.
--   - `tsallisEntropy`: PDF p.35, Definition 7.1: the q-Tsallis entropy.
--   - `signedRenyiEntropy`: PDF p.35, Definition 7.1: the source's positive-sign q-Renyi convention, which is the negative of the more usual entropy convention.
--   - `semiboundedGroundEnergy`: PDF pp.36--38: exact bottom energy of the spectral Hamiltonian. Use the frozen nonnegative-spectrum ground after subtracting H.lower, then add that shift back. Physical indices are nonempty; signed semibounded spectra are retained.
--   - `spectralThermalTrace`: PDF pp.15,36: extended thermal partition function, counting multiplicities.
--   - `IsEquilibrium`: PDF p.36, (7.3): actual equilibrium equation with convergent signed sums. These conditions specify the object; no estimate or asymptotic is assumed.
--   - `betaAtEnergy`: PDF p.36: beta(E) is constructed from (7.3), not a freely hypothesized function. Gibbs and E above the ground guarantee existence and uniqueness; Remark 2 below includes that assertion, excluding use of the zero fallback.
--   - `gibbsCoefficients`: PDF pp.35--37: Gibbs density in a complete energy eigenbasis. Gibbs spectra are discrete; choosing this basis loses no systems covered by the Gibbs hypothesis. Density and finiteness are concluded below, not made assumptions about a free state.
--   - `equilibriumEntropyNats`: PDF pp.36--38: actual spectral von Neumann entropy of the Gibbs density.
--   - `pairCountUp`: PDF pp.15,37, (7.5): sum over ordered spectral pairs, including multiplicity. The real sum has finite support under the Gibbs hypothesis at each cutoff.
--   - `pairCountDown`: PDF p.37, (7.5): the same ordered pair set and inclusive boundary. Signed semibounded spectra are permitted for Theorem 3; this is a convergent signed sum.
--   - `HasPairRatio`: PDF p.38: the actual ratio tends to the finite real xi>1.
--   - `entropyExponent`: PDF p.38: eta=(xi-1)^(-1).
--   - `entropyRemainder`: PDF pp.16,38,42: one Hamiltonian-specific remainder, shared by every pair of states or channels. Only its restriction to x>max(ground,1) is used as an asymptotic factor; finite errors use the exact Gibbs envelope.
--   - `oscillatorHamiltonian`: PDF p.37: Hosc=N+1/2, distinct from the coordinate oscillator -Delta+x^2.
--   - `continuityR`: PDF pp.15,47: r_epsilon(t) on its stated positive time interval.
--   - `discreteLaw`: PDF pp.43--44: discrete Borel law; coincident atoms and zero weights allowed.
--   - `borelBarycenterEnergy`: PDF p.43: energy of the actual ensemble barycenter, not of each signal.
--   - `countableProductHolevoCapacity`: PDF p.44, D_E and (7.17): countably discrete ensembles and STRICT average energy constraint. The supremum is extended before any finiteness theorem.
--   - `constrainedPurificationCapacity`: PDF p.42, (7.15): actual purification-based channel mutual information, maximized over input states only; no output entropy premise.
--   - `spectralEnergyMagnitude`: PDF p.10, ordinary ECD with a positive Gibbs Hamiltonian in its eigenbasis. The input need not commute with the Hamiltonian; off-diagonal blocks are retained.
--   - `BanachContractionSemigroup`: PDF pp.7--8,22: C0 contraction semigroup on a Banach space. Real scalars also cover the underlying real space of a complex Banach space.
--   - `GeneratorGraph`: PDF p.8: the entire generator graph is computed by the right derivative.
--   - `laplaceResolvent`: PDF p.8, (2.3): Laplace-transform resolvent at lambda>0. Contractivity ensures Bochner integrability. Only positive lambda is used in the seminorm.
--   - `resolventSeminorm`: PDF pp.17,22: extended resolvent seminorm. The identity A(lambda I-A)^(-1)=lambda(lambda I-A)^(-1)-I avoids totalizing A off its domain.
--   - `favardSeminorm`: PDF p.17, Definition 4.1: extended Favard seminorm, infinity retained.
--   - `favardSpace`: PDF p.17: the actual Favard space.
--   - `thermalEnvelope`: PDF pp.36,42: maximal entropy at an energy threshold. Above the ground this is exactly the entropy of the actual Gibbs state. At an attained ground it is log of the ground eigenspace dimension; the extended supremum also handles empty constraints. This retains all finite-error endpoints without dividing by log(1).
--   - `ThermalAsymptotic`: PDF pp.38,42: the single spectral remainder tends to zero, and the exact Gibbs envelope has the displayed asymptotic factor wherever that factor is used. This is a conclusion of the relevant theorems, never a hypothesis.
--   - `holevoModulus`: PDF pp.16,44,48: exact Gibbs version of the common product/Holevo modulus. The o(1) in the printed statement is recovered by ThermalAsymptotic at the specific argument E/(epsilon*t), not uniformly over moving time parameters.
--   - `assistedModulus`: PDF pp.47--48: exact Gibbs version of the EAC/QMI modulus.
--   - `blockSiteCoefficients`: PDF p.47: k-th marginal of a correlated n-copy input. The sum is over all coordinates OTHER than k; no product-state restriction is imposed.
--   - `blockInputEnergy`: PDF p.47: the actual maximum of the n marginal energies, as an extended finite supremum. The theorem requires n>=1 and proves/assumes finiteness exactly where the source does, before real conversion.
--   - `correlatedOutput`: PDF pp.42,47: actual n-copy channel output with the correlated reference retained, using the accepted full channel tensor power.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, https://arxiv.org/abs/1810.00863v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

/-!
Becker--Datta, arXiv:1810.00863v3. Natural logarithms throughout.
Countably infinite complete orthonormal coordinates represent the physical systems.
Product indices describe completed Hilbert tensor products, including entangled states.
Only reviewed accepted modules are imported. Deferred nodes are recorded in HARD.md.
Compilation is pending the batch handoff; no compilation claim is made here.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

namespace Spectral

export QAlgorithms.Papers.Independent.Frontier18.P01
  (Hamiltonian Channel homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond
   mutualInformation CountableStateEnsemble Barycenter)

end Spectral

namespace Ensembles

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients HasAverage ensembleHolevo)

end Ensembles

namespace Forms

export QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation)

end Forms

attribute [local instance] Classical.propDecidable Classical.decEq

/-! Imported-definition adapters: energyMagnitude is the frozen countably stabilized
positive-form norm. On differences of trace-class channels finite-reference
CPTP compression (replace the tail by one reference basis state) converges in
trace norm and preserves the entire input marginal, hence its energy bound,
so its value agrees with Definition 2.3's supremum over finite ancillas.
The local time kernels reuse accepted channels and only change parameter/coordinates.
The remaining extensions (real-spectrum energy, countable Schatten norm, signed
spectral ground, extended thermal partition trace, nats Gibbs entropy, Borel
barycenter energy and constrained capacities) have domains or meanings different
from the same-name frozen objects; ASSESSMENT.json records each comparison. -/

/-- PDF pp.11,17, (3.1): the endpoint alpha=1 is prescribed separately. -/
def zetaAlpha (alpha : ℝ) : ℝ :=
  if alpha = 1 then 1 else
    (2 * alpha / (1 - alpha)) ^ (1 - alpha) +
      2 * (2 * alpha / (1 - alpha)) ^ (-alpha)

/-- PDF p.7: bottom of a positive observable, using finite unit-vector form energies.
Density of the form domain makes this set nonempty on a nonzero Hilbert space. -/
def formGround {I : Type} (F : Forms.PositiveObservable I) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ u : Hilbert I, ‖u‖ = 1 ∧ F.form u = ENNReal.ofReal r}

/-- PDF p.10: alpha-ECD for diagonal positive spectral observables, including N,M.
This definition is used only for the explicit bosonic channels, never to restrict
an arbitrary self-adjoint Hamiltonian to pure point spectrum. -/
def diagonalMagnitude (energy : ℕ → ℝ) (alpha E : ℝ)
    (T : Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ rho : {rho : State (ℕ × Fin n) //
    (∑' j : ℕ, ENNReal.ofReal
      ((energy j) ^ (2 * alpha) * (Spectral.traceSecond rho.coefficients j j).re)) ≤
      ENNReal.ofReal (E ^ (2 * alpha))},
    traceSize (tensorApply T rho.val.coefficients)

/-- PDF pp.27,43: extended spectral energy, used for arbitrary (also infinite-energy)
initial states. All energy lists supplied to this definition are nonnegative. -/
def realSpectrumMeanEnergy {I : Type} (energy : I → ℝ) (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ∑' j : I, ENNReal.ofReal (energy j * (X j j).re)

/-- PDF p.27: the number spectrum, with the vacuum at n=0. -/
def numberEigenvalue (n : ℕ) : ℝ := n

/-- PDF p.28: M=aa*=N+I, whose bottom is 1. -/
def amplifierEnergy (n : ℕ) : ℝ := (n : ℝ) + 1

/-- PDF p.27: coefficient action of the accepted bounded Kraus matrices.
On trace class the scalar series converge absolutely, and the Kraus sum converges
in trace norm. The source theorems below include the latter convergence explicitly. -/
def coefficientKrausTerm (K : ℕ → Matrix ℕ ℕ ℂ) (X : Matrix ℕ ℕ ℂ)
    (ell : ℕ) : Matrix ℕ ℕ ℂ :=
  fun m n => ∑' i : ℕ, ∑' j : ℕ, K ell m i * X i j * star (K ell n j)

/-- PDF p.27: unconditional trace-norm summation, not coefficientwise convergence. -/
def TraceSums {I : Type} (f : ℕ → Matrix I I ℂ) (X : Matrix I I ℂ) : Prop :=
  IsTraceClass X ∧ (∀ n, IsTraceClass (f n)) ∧
    Tendsto (fun s : Finset ℕ => traceSize ((∑ i ∈ s, f i) - X)) atTop (𝓝 0)

/-- PDF p.27: attenuation uses amplitude exp(-t/2), as fixed by the Kraus series
and generator there and the photon-number law on p.43. The conflicting amplitude
exp(-t) of (1.2) is deferred, not asserted for this channel. -/
def attenuatorTerm (t : ℝ) (X : Matrix ℕ ℕ ℂ) : ℕ → Matrix ℕ ℕ ℂ :=
  coefficientKrausTerm
    (QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorMatrix (Real.exp (-t / 2))) X

/-- PDF p.27: time adapter for the frozen vacuum attenuator; amplitude exp(-t/2).
On trace class this is the countable Kraus sum, including t=0. -/
def attenuatorTimeKernel (t : ℝ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  QAlgorithms.Papers.Independent.Bridge50.P23.vacuumAttenuator
    (Real.exp (-t / 2) : ℂ) X

/-- PDF pp.27--28: quantum-limited amplifier with amplitude gain exp(t/2).
Its generator is a* rho a - {N+I,rho}/2. No Latt-I identity is used. -/
def amplifierTerm (t : ℝ) (X : Matrix ℕ ℕ ℂ) : ℕ → Matrix ℕ ℕ ℂ :=
  coefficientKrausTerm
    (QAlgorithms.Papers.Independent.Dependency50.P39.amplifierMatrix (Real.exp (t / 2))) X

/-- PDF pp.27--28: time adapter for the frozen full amplifier coefficient kernel.
The accepted intensity gain is exp(t), hence amplitude gain exp(t/2). -/
def amplifierTimeKernel (t : ℝ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  QAlgorithms.Papers.Independent.Bridge50.P28.quantumLimitedAmplifierKernel (Real.exp t) X

/-- PDF pp.27--28: common explicit bosonic Holder coefficient. -/
def bosonicCoefficient (alpha : ℝ) : ℝ :=
  4 * zetaAlpha alpha * (1 - alpha) ^ (1 - alpha) * alpha ^ alpha

/-- PDF pp.35--36: Schatten-q power on self-adjoint trace-class arrays, defined
by all finite coordinate compressions using the frozen finite Schatten norm.
For self-adjoint differences this equals the |x|^q functional calculus.
The extended supremum is finite for q>=1 on trace class. -/
def schattenPower {I : Type} (q : ℝ) (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ s : Finset I, ENNReal.ofReal
    ((QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal q)
      (X.submatrix (fun i : s => i.val) (fun i : s => i.val))) ^ q)

/-- PDF p.35: real Schatten norm, used only for q>1 and trace-class self-adjoint
inputs, where finiteness precedes conversion to a real number mathematically. -/
def traceClassSchattenQNorm {I : Type} (q : ℝ) (X : Matrix I I ℂ) : ℝ :=
  (schattenPower q X).toReal ^ (1 / q)

/-- PDF p.35, Definition 7.1: the q-Tsallis entropy. -/
def tsallisEntropy {I : Type} (q : ℝ) (rho : State I) : ℝ :=
  (1 - (traceClassSchattenQNorm q rho.coefficients) ^ q) / (q - 1)

/-- PDF p.35, Definition 7.1: the source's positive-sign q-Renyi convention,
which is the negative of the more usual entropy convention. -/
def signedRenyiEntropy {I : Type} (q : ℝ) (rho : State I) : ℝ :=
  q / (q - 1) * Real.log (traceClassSchattenQNorm q rho.coefficients)

/-- PDF pp.36--38: exact bottom energy of the spectral Hamiltonian. Use the frozen
nonnegative-spectrum ground after subtracting H.lower, then add that shift back.
Physical indices are nonempty; signed semibounded spectra are retained. -/
def semiboundedGroundEnergy {I : Type} (H : Spectral.Hamiltonian I) : ℝ :=
  QAlgorithms.Papers.Independent.Support50.P18.spectralGround
    (fun i => ⟨H.energy i - H.lower, sub_nonneg.mpr (H.bounded_below i)⟩) + H.lower

/-- PDF pp.15,36: extended thermal partition function, counting multiplicities. -/
def spectralThermalTrace {I : Type} (H : Spectral.Hamiltonian I) (beta : ℝ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.exp (-beta * H.energy i))

/-- PDF p.36, (7.3): actual equilibrium equation with convergent signed sums.
These conditions specify the object; no estimate or asymptotic is assumed. -/
def IsEquilibrium {I : Type} (H : Spectral.Hamiltonian I) (E beta : ℝ) : Prop :=
  0 < beta ∧ 0 < (spectralThermalTrace H beta).toReal ∧
    Summable (fun i => Real.exp (-beta * H.energy i)) ∧
    Summable (fun i => H.energy i * Real.exp (-beta * H.energy i)) ∧
    (∑' i, H.energy i * Real.exp (-beta * H.energy i)) = E * (spectralThermalTrace H beta).toReal

/-- PDF p.36: beta(E) is constructed from (7.3), not a freely hypothesized
function. Gibbs and E above the ground guarantee existence and uniqueness;
Remark 2 below includes that assertion, excluding use of the zero fallback. -/
def betaAtEnergy {I : Type} (H : Spectral.Hamiltonian I) (E : ℝ) : ℝ :=
  if h : ∃ beta, IsEquilibrium H E beta then Classical.choose h else 0

/-- PDF pp.35--37: Gibbs density in a complete energy eigenbasis. Gibbs spectra
are discrete; choosing this basis loses no systems covered by the Gibbs hypothesis.
Density and finiteness are concluded below, not made assumptions about a free state. -/
def gibbsCoefficients {I : Type} (H : Spectral.Hamiltonian I) (E : ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i =>
    (Real.exp (-betaAtEnergy H E * H.energy i) / (spectralThermalTrace H (betaAtEnergy H E)).toReal : ℂ))

/-- PDF pp.36--38: actual spectral von Neumann entropy of the Gibbs density. -/
def equilibriumEntropyNats {I : Type} (H : Spectral.Hamiltonian I) (E : ℝ) : ℝ :=
  (Spectral.homogeneousEntropy (gibbsCoefficients H E)).toReal

/-- PDF pp.15,37, (7.5): sum over ordered spectral pairs, including multiplicity.
The real sum has finite support under the Gibbs hypothesis at each cutoff. -/
def pairCountUp {I : Type} (H : Spectral.Hamiltonian I) (L : ℝ) : ℝ :=
  ∑' p : I × I, if H.energy p.1 + H.energy p.2 ≤ L then (H.energy p.1) ^ 2 else 0

/-- PDF p.37, (7.5): the same ordered pair set and inclusive boundary. Signed
semibounded spectra are permitted for Theorem 3; this is a convergent signed sum. -/
def pairCountDown {I : Type} (H : Spectral.Hamiltonian I) (L : ℝ) : ℝ :=
  ∑' p : I × I, if H.energy p.1 + H.energy p.2 ≤ L then
    H.energy p.1 * H.energy p.2 else 0

/-- PDF p.38: the actual ratio tends to the finite real xi>1. -/
def HasPairRatio {I : Type} (H : Spectral.Hamiltonian I) (xi : ℝ) : Prop :=
  1 < xi ∧ Tendsto (fun L => pairCountUp H L / pairCountDown H L) atTop (𝓝 xi)

/-- PDF p.38: eta=(xi-1)^(-1). -/
def entropyExponent (xi : ℝ) : ℝ := 1 / (xi - 1)

/-- PDF pp.16,38,42: one Hamiltonian-specific remainder, shared by every pair of
states or channels. Only its restriction to x>max(ground,1) is used as an
asymptotic factor; finite errors use the exact Gibbs envelope. -/
def entropyRemainder {I : Type} (H : Spectral.Hamiltonian I) (xi x : ℝ) : ℝ :=
  equilibriumEntropyNats H x / (entropyExponent xi * Real.log x) - 1

/-- PDF p.37: Hosc=N+1/2, distinct from the coordinate oscillator -Delta+x^2. -/
def oscillatorHamiltonian : Spectral.Hamiltonian ℕ where
  energy := fun n => (n : ℝ) + 1 / 2
  lower := 1 / 2
  bounded_below := by
    intro n
    change (1 / 2 : ℝ) ≤ (n : ℝ) + 1 / 2
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

/-- PDF pp.15,47: r_epsilon(t) on its stated positive time interval. -/
def continuityR (epsilon t : ℝ) : ℝ := (1 + t / 2) / (1 - epsilon * t)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- PDF pp.43--44: discrete Borel law; coincident atoms and zero weights allowed. -/
def discreteLaw {I : Type} (e : Spectral.CountableStateEnsemble I) : Measure (State I) :=
  Measure.sum (fun n => e.weight n • Measure.dirac (e.state n))

/-- PDF p.43: energy of the actual ensemble barycenter, not of each signal. -/
def borelBarycenterEnergy {I : Type} (F : Forms.PositiveObservable I)
    (mu : Ensembles.GeneralizedEnsemble I) : ℝ≥0∞ :=
  Forms.closedFormExpectation F (Ensembles.averageCoefficients mu)

/-- PDF p.44, D_E and (7.17): countably discrete ensembles and STRICT average
energy constraint. The supremum is extended before any finiteness theorem. -/
def countableProductHolevoCapacity {I J : Type} (Phi : Spectral.Channel I J)
    (F : Forms.PositiveObservable I) (E : ℝ) : ℝ≥0∞ :=
  ⨆ e : Spectral.CountableStateEnsemble I,
    ⨆ rho : {rho : State I // Spectral.Barycenter e rho.coefficients ∧
      Forms.closedFormExpectation F rho.coefficients < ENNReal.ofReal E},
      ∑' n, e.weight n * Spectral.generalizedRelativeEntropy
        (Phi.val (e.state n).coefficients) (Phi.val rho.val.coefficients)

/-- PDF p.42, (7.15): actual purification-based channel mutual information,
maximized over input states only; no output entropy premise. -/
def constrainedPurificationCapacity {I J : Type} (Phi : Spectral.Channel I J)
    (H : Spectral.Hamiltonian I) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State I // H.meanEnergy rho ≤ (E : EReal)},
    Spectral.mutualInformation rho.val.coefficients Phi.val

/-- PDF p.10, ordinary ECD with a positive Gibbs Hamiltonian in its eigenbasis.
The input need not commute with the Hamiltonian; off-diagonal blocks are retained. -/
def spectralEnergyMagnitude {I J : Type} (H : Spectral.Hamiltonian I) (E : ℝ)
    (T : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ rho : {rho : State (I × Fin n) //
    (∑' j : I, ENNReal.ofReal
      (H.energy j * (Spectral.traceSecond rho.coefficients j j).re)) ≤ ENNReal.ofReal E},
    traceSize (tensorApply T rho.val.coefficients)

/-- PDF pp.7--8,22: C0 contraction semigroup on a Banach space. Real scalars
also cover the underlying real space of a complex Banach space. -/
structure BanachContractionSemigroup (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  maps : ℝ≥0 → X →L[ℝ] X
  initial : maps 0 = ContinuousLinearMap.id ℝ X
  compose : ∀ s t, maps (s + t) = (maps s).comp (maps t)
  contraction : ∀ t x, ‖maps t x‖ ≤ ‖x‖
  continuous : ∀ x, Continuous (fun t : ℝ≥0 => maps t x)

/-- PDF p.8: the entire generator graph is computed by the right derivative. -/
def GeneratorGraph {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : BanachContractionSemigroup X) (x y : X) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (T.maps t.toNNReal x - x)) (𝓝[>] 0) (𝓝 y)

/-- PDF p.8, (2.3): Laplace-transform resolvent at lambda>0. Contractivity
ensures Bochner integrability. Only positive lambda is used in the seminorm. -/
def laplaceResolvent {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (T : BanachContractionSemigroup X) (lambda : ℝ) (x : X) : X :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lambda * t) • T.maps t.toNNReal x

/-- PDF pp.17,22: extended resolvent seminorm. The identity
A(lambda I-A)^(-1)=lambda(lambda I-A)^(-1)-I avoids totalizing A off its domain. -/
def resolventSeminorm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (T : BanachContractionSemigroup X) (alpha : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ lambda : {r : ℝ // 0 < r}, ENNReal.ofReal
    (lambda.val ^ alpha * ‖lambda.val • laplaceResolvent T lambda.val x - x‖)

/-- PDF p.17, Definition 4.1: extended Favard seminorm, infinity retained. -/
def favardSeminorm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : BanachContractionSemigroup X) (alpha : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ t : {r : ℝ // 0 < r}, ENNReal.ofReal (‖T.maps t.val.toNNReal x - x‖ / t.val ^ alpha)

/-- PDF p.17: the actual Favard space. -/
def favardSpace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : BanachContractionSemigroup X) (alpha : ℝ) : Set X :=
  {x | favardSeminorm T alpha x < ⊤}

/-! Sanity examples concern complete definitions, not proofs of source theorems. -/

example : zetaAlpha 1 = 1 := by simp [zetaAlpha]

example : numberEigenvalue 0 = 0 ∧ amplifierEnergy 0 = 1 := by
  norm_num [numberEigenvalue, amplifierEnergy]

example : oscillatorHamiltonian.energy 0 = 1 / 2 := by
  simp [oscillatorHamiltonian]

example : continuityR 0 0 = 1 ∧ g 0 = 0 := by
  norm_num [continuityR, g]

example (H : Spectral.Hamiltonian ℕ) : spectralThermalTrace H 0 = ⊤ := by
  simp [spectralThermalTrace]

example {I : Type} (H : Spectral.Hamiltonian I) (x : ℝ) :
    entropyRemainder H 2 x = equilibriumEntropyNats H x / Real.log x - 1 := by
  norm_num [entropyRemainder, entropyExponent]

example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : BanachContractionSemigroup X) (alpha : ℝ) : favardSeminorm T alpha 0 = 0 := by
  simp [favardSeminorm]

/-- PDF pp.36,42: maximal entropy at an energy threshold. Above the ground this
is exactly the entropy of the actual Gibbs state. At an attained ground it is
log of the ground eigenspace dimension; the extended supremum also handles empty
constraints. This retains all finite-error endpoints without dividing by log(1). -/
def thermalEnvelope {I : Type} (H : Spectral.Hamiltonian I) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State I // H.meanEnergy rho ≤ (E : EReal)},
    Spectral.homogeneousEntropy rho.val.coefficients

/-- PDF pp.38,42: the single spectral remainder tends to zero, and the exact
Gibbs envelope has the displayed asymptotic factor wherever that factor is used.
This is a conclusion of the relevant theorems, never a hypothesis. -/
def ThermalAsymptotic {I : Type} (H : Spectral.Hamiltonian I) (xi : ℝ) : Prop :=
  Tendsto (entropyRemainder H xi) atTop (𝓝 (0 : ℝ)) ∧
  ∀ x : ℝ, max (semiboundedGroundEnergy H) 1 < x →
    (thermalEnvelope H x).toReal =
      entropyExponent xi * Real.log x * (1 + entropyRemainder H xi x)

/-- PDF pp.16,44,48: exact Gibbs version of the common product/Holevo modulus.
The o(1) in the printed statement is recovered by ThermalAsymptotic at the
specific argument E/(epsilon*t), not uniformly over moving time parameters. -/
def holevoModulus {I : Type} (H : Spectral.Hamiltonian I) (E epsilon t : ℝ) : ℝ :=
  epsilon * (2 * t + continuityR epsilon t) *
    (thermalEnvelope H (E / (epsilon * t))).toReal +
    2 * g (epsilon * continuityR epsilon t) + 2 * Real.binEntropy (epsilon * t)

/-- PDF pp.47--48: exact Gibbs version of the EAC/QMI modulus. -/
def assistedModulus {I : Type} (H : Spectral.Hamiltonian I) (E epsilon t : ℝ) : ℝ :=
  2 * epsilon * (2 * t + continuityR epsilon t) *
    (thermalEnvelope H (E / (epsilon * t))).toReal +
    2 * g (epsilon * continuityR epsilon t) + 4 * Real.binEntropy (epsilon * t)

/-- PDF p.47: k-th marginal of a correlated n-copy input. The sum is over
all coordinates OTHER than k; no product-state restriction is imposed. -/
def blockSiteCoefficients {I : Type} {n : ℕ} (k : Fin n)
    (X : Matrix (Fin n → I) (Fin n → I) ℂ) : Matrix I I ℂ :=
  fun i j => ∑' rest : {l : Fin n // l ≠ k} → I,
    X (fun l => if h : l = k then i else rest ⟨l, h⟩)
      (fun l => if h : l = k then j else rest ⟨l, h⟩)

/-- PDF p.47: the actual maximum of the n marginal energies, as an extended
finite supremum. The theorem requires n>=1 and proves/assumes finiteness exactly
where the source does, before real conversion. -/
def blockInputEnergy {I R : Type} {n : ℕ} (F : Forms.PositiveObservable I)
    (rho : State ((Fin n → I) × R)) : ℝ≥0∞ :=
  ⨆ k : Fin n, Forms.closedFormExpectation F
    (blockSiteCoefficients k (Spectral.traceSecond rho.coefficients))

/-- PDF pp.42,47: actual n-copy channel output with the correlated reference
retained, using the accepted full channel tensor power. -/
def correlatedOutput {I J R : Type} {n : ℕ} (Phi : Spectral.Channel I J)
    (rho : State ((Fin n → I) × R)) : Matrix ((Fin n → J) × R) ((Fin n → J) × R) ℂ :=
  tensorApply (QAlgorithms.Papers.Independent.Claimed50.P35.traceClassChannelPower Phi.val n)
    rho.coefficients

example {I : Type} (H : Spectral.Hamiltonian I) (xi : ℝ)
    (h : ThermalAsymptotic H xi) :
    Tendsto (entropyRemainder H xi) atTop (𝓝 (0 : ℝ)) := h.1

example {I : Type} (H : Spectral.Hamiltonian I) :
    holevoModulus H 0 0 0 = 0 := by
  simp [holevoModulus, g, Real.binEntropy]

end QAlgorithms.Papers.Independent.Advance50.P46


