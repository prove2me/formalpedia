-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31
-- name    : QAlgorithms_Papers_Independent_Advance50_P31
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:06:50.964682+00:00
-- url     : https://prove2.me/theorems/a7a9885d-db1f-4bdf-b635-f4d10a32aa4f
-- title:
--   Definitions for Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions
-- statement:
--   The objects the formalized statements of *Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions* (arXiv:quant-ph/0512200) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bitEntropyWeight`: PDF pp.3,8: continuous bit-entropy weight, including zero.
--   - `boseEntropy`: PDF p.8, Eq.(51): entropy of a geometric occupation law of mean x.
--   - `fermiEntropy`: PDF pp.11--12: entropy of a spin-resolved Bernoulli occupation. This is the correction of Eq.(60) determined by Eqs.(56),(58),(59).
--   - `BoseConfig`: PDF pp.5,8: all finite-particle Fock configurations over countably many modes; there is no common bound on particle number or on occupied mode indices.
--   - `FermiConfig`: PDF p.11, Eq.(58): every spin-resolved occupation is zero or one.
--   - `boseNumber`: PDF p.8: eigenvalue of the total particle-number operator.
--   - `boseEnergy`: PDF p.8: noninteracting many-particle energy.
--   - `fermiNumber`: PDF p.11: sum over spin-resolved occupations.
--   - `fermiEnergy`: PDF p.11: all g spin states at spatial mode i have the same energy eps i.
--   - `IsFockDensity`: PDF pp.3,6: positive trace-one states. Positivity includes self-adjointness.
--   - `fockEntropyBits`: PDF p.3, Eq.(4): full extended von Neumann entropy in bits, using continuous functional calculus of -x log_2 x. On densities the diagonal weights are nonnegative; the extended sum preserves infinite entropy.
--   - `fockMean`: PDF p.6, Eqs.(36),(37): diagonal expectation, with absolute convergence required by Moment below. Negative bounded-below single-particle energies are allowed.
--   - `Moment`: PDF pp.5--8: finite absolute moment; prevents a divergent real tsum becoming zero.
--   - `FockEnsembleData`: PDF pp.2--3: countably supported ensembles, including finite ensembles via zero weights.
--   - `fockAverage`: PDF p.3: the actual average input operator; for normalized ensembles this series converges in operator norm as well as trace norm.
--   - `IsFockEnsemble`: PDF pp.2--3: normalization of each state and the message probability law.
--   - `FockAdmissible`: PDF pp.6--8: equality constraints on the average ensemble state. N=none is the photon model with no particle-number constraint. No constraint is messagewise.
--   - `fockHolevoBits`: PDF pp.3,7, Eq.(40): Holevo quantity for the identity channel. On the Gibbs constraint shell every average entropy is finite, a consequence of the capacity theorem, so the extended subtraction does not conceal infinity minus infinity there.
--   - `fockClassicalCapacity`: PDF p.7, Eq.(42), and p.8, Eq.(48): supremum of Holevo information over all admissible ensembles; this is not defined as the candidate Gibbs entropy.
--   - `IsFockPOVM`: PDF pp.2--3: all countable-outcome POVMs, normalized weakly on the whole Hilbert space. Countable outcomes suffice for the accessible-information supremum; the attaining Fock measurement is itself countable.
--   - `effectProbability`: PDF p.2: Born probability tr(M rho), with the source's noiseless output rho.
--   - `relativeTermBits`: PDF p.2: classical relative-entropy summand. The +q-p form is nonnegative and has the same total as p log_2(p/q) for normalized distributions.
--   - `countableMutualInformationBits`: PDF p.2, Eq.(1): countable classical mutual information from the actual joint law and the product of its marginals. Extended nonnegative summands avoid divergent signed real sums.
--   - `fockMeasuredInformation`: PDF pp.2--3: mutual information for one specified measurement.
--   - `fockMeasurement`: PDF pp.7--8: computational Fock measurement, with one outcome for every configuration.
--   - `fockAccessibleInformation`: PDF p.3, Eq.(2): optimize the actual measured mutual information.
--   - `singleCopyCapacity`: PDF p.3, Eq.(5): single-copy capacity, allowing arbitrary admissible ensembles.
--   - `fockGibbsWeight`: PDF pp.5,8,11: Gibbs weight on the complete number-state basis.
--   - `fockPartition`: PDF pp.5,8,11: partition sum, used only with GibbsRegular.
--   - `fockGibbsProbability`: PDF pp.5,8,11: normalized grand-canonical probability law.
--   - `countableShannonBits`: PDF p.7, Eq.(44), p.8, Eq.(50), p.11, Eq.(56): Shannon entropy of a NORMALIZED probability law, rather than entropy of mean occupations.
--   - `GibbsRegular`: PDF pp.5--8: the normalizable, finite-moment, finite-entropy Gibbs domain. These conditions do not assert optimality, attainment, or the mode-entropy formula.
--   - `fockEnsemble`: PDF pp.7,8,11: the constructed orthogonal number-state ensemble.
--   - `fockGibbsMean`: PDF pp.7--8: actual Gibbs mean, not a free value tied by an optimality assumption.
--   - `ThermalAttainment`: PDF pp.7,8,11: full attainment claim, both Holevo and single-copy accessible information, plus the explicit entropy formula. Both capacities are optimized independently above; average-state entropy finiteness is a conclusion.
--   - `trapExponent`: PDF p.14, Eq.(86): power-law trap exponent a=d/gamma+d/2.
--   - `densityOfStates`: PDF p.14, Eq.(86): semiclassical density, on positive energies only. A is the common positive normalization from phase space, including the mass and trap scale.
--   - `powerLawPhaseSpaceEnergy`: PDF p.14, Eqs.(83),(85): the actual classical single-particle energy on momentum-position phase space, with ordinary Euclidean Lebesgue volume. The first component is momentum and the second is position.
--   - `boltzmannMoment`: PDF pp.12--14, Eqs.(63),(86): continuum Boltzmann moment S_k.
--   - `weightedMoment`: PDF pp.13--14, Eq.(77): D_k has beta*energy, not k*beta*energy.
--   - `continuumOccupation`: PDF pp.12--15: spinless continuum occupations at fugacity z=exp(beta*mu). The Boolean selects fermions; false selects bosons.
--   - `continuumNumber`: PDF pp.12--15: excited-state particle-number integral. For bosons a>1 is used at z=1; all retained comparison theorems satisfy this restriction.
--   - `continuumEntropy`: PDF pp.12--15: continuum entropy at a specified fugacity, in bits.
--   - `boseFugacity`: PDF pp.9,14--15: Bose fugacity solved from fixed mean N. The supremum clips at one in the condensed regime. The uncounted ground condensate has zero entropy in this continuum thermodynamic model. This is not finite-trap exact thermodynamics. The defining set contains zero and lies in [0,1] for positive A,a,beta,N with a>1.
--   - `fermiFugacity`: PDF pp.12--15: Fermi fugacity is solved separately at the same mean N. On positive A,a,beta,N the set is nonempty, bounded below, and its infimum is the unique positive solution. No equality of the Bose and Fermi energies is imposed.
--   - `thermodynamicCapacity`: PDF pp.12--15: the explicit CLASSICAL thermodynamic capacity curve in the continuum model used in Sections IX--X, evaluated at its fixed-N equilibrium. It is not a definition of an operational quantum capacity.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, https://arxiv.org/abs/quant-ph/0512200v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Sen(De) et al., arXiv:quant-ph/0512200v3. Discrete noiseless classical
capacities and continuum thermodynamic comparisons are separate models.
All entropy units are bits. The quantum operational assertions and numerical
observations deferred in HARD.md are deliberately absent.

The nuclear trace-class predicate and basis trace are imported from the pinned
accepted Dependency50.P13 module, as authorized by the independent-paper workflow.
The remaining Fock definitions distinguish countable labels, bit units, and
average-state equality constraints from finite-dimensional or natural-log
quantities in the accepted library. No finite Fock cutoff, fixed particle-number
sector, or entropy value is used to define classical capacity. The channel is the identity on states.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

/-- PDF pp.3,8: continuous bit-entropy weight, including zero. -/
def bitEntropyWeight (x : ℝ) : ℝ := -x * Real.logb 2 x

/-- PDF p.8, Eq.(51): entropy of a geometric occupation law of mean x. -/
def boseEntropy (x : ℝ) : ℝ := (1 + x) * Real.logb 2 (1 + x) + bitEntropyWeight x

/-- PDF pp.11--12: entropy of a spin-resolved Bernoulli occupation. This is the
correction of Eq.(60) determined by Eqs.(56),(58),(59). -/
def fermiEntropy (x : ℝ) : ℝ := bitEntropyWeight x + bitEntropyWeight (1 - x)

example : bitEntropyWeight 0 = 0 := by simp [bitEntropyWeight]

example : fermiEntropy 1 = 0 := by simp [fermiEntropy, bitEntropyWeight]

example : boseEntropy 0 = 0 := by simp [boseEntropy, bitEntropyWeight]

/-- PDF pp.5,8: all finite-particle Fock configurations over countably many modes;
there is no common bound on particle number or on occupied mode indices. -/
abbrev BoseConfig := ℕ →₀ ℕ

/-- PDF p.11, Eq.(58): every spin-resolved occupation is zero or one. -/
abbrev FermiConfig (g : ℕ) :=
  {n : (ℕ × Fin g) →₀ ℕ // ∀ i, n i ≤ 1}

/-- PDF p.8: eigenvalue of the total particle-number operator. -/
def boseNumber (n : BoseConfig) : ℝ := n.sum (fun _ v => (v : ℝ))

/-- PDF p.8: noninteracting many-particle energy. -/
def boseEnergy (eps : ℕ → ℝ) (n : BoseConfig) : ℝ :=
  n.sum (fun i v => eps i * (v : ℝ))

/-- PDF p.11: sum over spin-resolved occupations. -/
def fermiNumber {g : ℕ} (n : FermiConfig g) : ℝ :=
  n.val.sum (fun _ v => (v : ℝ))

/-- PDF p.11: all g spin states at spatial mode i have the same energy eps i. -/
def fermiEnergy {g : ℕ} (eps : ℕ → ℝ) (n : FermiConfig g) : ℝ :=
  n.val.sum (fun i v => eps i.1 * (v : ℝ))

example : boseNumber 0 = 0 := by simp [boseNumber]

example (eps : ℕ → ℝ) : boseEnergy eps 0 = 0 := by simp [boseEnergy]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} [Countable I]

/-- PDF pp.3,6: positive trace-one states. Positivity includes self-adjointness. -/
def IsFockDensity (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) : Prop :=
  IsTraceClass rho ∧ rho.adjoint = rho ∧
    (∀ x, 0 ≤ (inner ℂ x (rho x)).re) ∧ operatorTrace b rho = 1

/-- PDF p.3, Eq.(4): full extended von Neumann entropy in bits, using continuous
functional calculus of -x log_2 x. On densities the diagonal weights are nonnegative;
the extended sum preserves infinite entropy. -/
def fockEntropyBits (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (inner ℂ (b i) ((cfc bitEntropyWeight rho) (b i))).re

/-- PDF p.6, Eqs.(36),(37): diagonal expectation, with absolute convergence required
by Moment below. Negative bounded-below single-particle energies are allowed. -/
def fockMean (b : HilbertBasis I ℂ H) (v : I → ℝ) (rho : H →L[ℂ] H) : ℝ :=
  ∑' i, v i * (inner ℂ (b i) (rho (b i))).re

/-- PDF pp.5--8: finite absolute moment; prevents a divergent real tsum becoming zero. -/
def Moment (b : HilbertBasis I ℂ H) (v : I → ℝ) (rho : H →L[ℂ] H) : Prop :=
  Summable (fun i => v i * (inner ℂ (b i) (rho (b i))).re)

/-- PDF pp.2--3: countably supported ensembles, including finite ensembles via zero weights. -/
structure FockEnsembleData (I H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] where
  p : I → ℝ
  rho : I → H →L[ℂ] H

/-- PDF p.3: the actual average input operator; for normalized ensembles this series
converges in operator norm as well as trace norm. -/
def fockAverage (e : FockEnsembleData I H) : H →L[ℂ] H := ∑' i, (e.p i : ℂ) • e.rho i

/-- PDF pp.2--3: normalization of each state and the message probability law. -/
def IsFockEnsemble (b : HilbertBasis I ℂ H) (e : FockEnsembleData I H) : Prop :=
  (∀ i, 0 ≤ e.p i) ∧ Summable e.p ∧ (∑' i, e.p i) = 1 ∧
    (∀ i, IsFockDensity b (e.rho i))

/-- PDF pp.6--8: equality constraints on the average ensemble state. N=none is
the photon model with no particle-number constraint. No constraint is messagewise. -/
def FockAdmissible (b : HilbertBasis I ℂ H) (energy number : I → ℝ)
    (E : ℝ) (N : Option ℝ) (e : FockEnsembleData I H) : Prop :=
  IsFockEnsemble b e ∧ IsFockDensity b (fockAverage e) ∧
  Moment b energy (fockAverage e) ∧ fockMean b energy (fockAverage e) = E ∧
  match N with
  | none => True
  | some n => Moment b number (fockAverage e) ∧ fockMean b number (fockAverage e) = n

/-- PDF pp.3,7, Eq.(40): Holevo quantity for the identity channel. On the Gibbs
constraint shell every average entropy is finite, a consequence of the capacity theorem,
so the extended subtraction does not conceal infinity minus infinity there. -/
def fockHolevoBits (b : HilbertBasis I ℂ H) (e : FockEnsembleData I H) : ℝ≥0∞ :=
  fockEntropyBits b (fockAverage e) - ∑' i, ENNReal.ofReal (e.p i) * fockEntropyBits b (e.rho i)

/-- PDF p.7, Eq.(42), and p.8, Eq.(48): supremum of Holevo information over all
admissible ensembles; this is not defined as the candidate Gibbs entropy. -/
def fockClassicalCapacity (b : HilbertBasis I ℂ H) (energy number : I → ℝ)
    (E : ℝ) (N : Option ℝ) : ℝ≥0∞ :=
  ⨆ e : {e : FockEnsembleData I H // FockAdmissible b energy number E N e}, fockHolevoBits b e.val

/-- PDF pp.2--3: all countable-outcome POVMs, normalized weakly on the whole Hilbert
space. Countable outcomes suffice for the accessible-information supremum; the
attaining Fock measurement is itself countable. -/
def IsFockPOVM (M : I → H →L[ℂ] H) : Prop :=
  (∀ i, (M i).adjoint = M i ∧ ∀ x, 0 ≤ (inner ℂ x (M i x)).re) ∧
  ∀ x y, Summable (fun i => inner ℂ x (M i y)) ∧
    (∑' i, inner ℂ x (M i y)) = inner ℂ x y

/-- PDF p.2: Born probability tr(M rho), with the source's noiseless output rho. -/
def effectProbability (b : HilbertBasis I ℂ H) (M rho : H →L[ℂ] H) : ℝ :=
  (operatorTrace b (M.comp rho)).re

/-- PDF p.2: classical relative-entropy summand. The +q-p form is nonnegative
and has the same total as p log_2(p/q) for normalized distributions. -/
def relativeTermBits (p q : ℝ) : ℝ≥0∞ :=
  if p = 0 then ENNReal.ofReal (q / Real.log 2)
  else if q = 0 then ⊤
  else ENNReal.ofReal ((p * Real.log (p / q) - p + q) / Real.log 2)

/-- PDF p.2, Eq.(1): countable classical mutual information from the actual joint
law and the product of its marginals. Extended nonnegative summands avoid divergent
signed real sums. -/
def countableMutualInformationBits (r : I × I → ℝ) : ℝ≥0∞ :=
  ∑' ij, relativeTermBits (r ij)
    ((∑' j, r (ij.1, j)) * (∑' i, r (i, ij.2)))

/-- PDF pp.2--3: mutual information for one specified measurement. -/
def fockMeasuredInformation (b : HilbertBasis I ℂ H) (e : FockEnsembleData I H)
    (M : I → H →L[ℂ] H) : ℝ≥0∞ :=
  countableMutualInformationBits (fun ij => e.p ij.1 * effectProbability b (M ij.2) (e.rho ij.1))

/-- PDF pp.7--8: computational Fock measurement, with one outcome for every configuration. -/
def fockMeasurement (b : HilbertBasis I ℂ H) (i : I) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ (b i) (b i)

/-- PDF p.3, Eq.(2): optimize the actual measured mutual information. -/
def fockAccessibleInformation (b : HilbertBasis I ℂ H) (e : FockEnsembleData I H) : ℝ≥0∞ :=
  ⨆ M : {M : I → H →L[ℂ] H // IsFockPOVM M},
    fockMeasuredInformation b e M.val

/-- PDF p.3, Eq.(5): single-copy capacity, allowing arbitrary admissible ensembles. -/
def singleCopyCapacity (b : HilbertBasis I ℂ H) (energy number : I → ℝ)
    (E : ℝ) (N : Option ℝ) : ℝ≥0∞ :=
  ⨆ e : {e : FockEnsembleData I H // FockAdmissible b energy number E N e}, fockAccessibleInformation b e.val

/-- PDF pp.5,8,11: Gibbs weight on the complete number-state basis. -/
def fockGibbsWeight (energy number : I → ℝ) (beta mu : ℝ) (i : I) : ℝ :=
  Real.exp (-beta * (energy i - mu * number i))

/-- PDF pp.5,8,11: partition sum, used only with GibbsRegular. -/
def fockPartition (energy number : I → ℝ) (beta mu : ℝ) : ℝ :=
  ∑' i, fockGibbsWeight energy number beta mu i

/-- PDF pp.5,8,11: normalized grand-canonical probability law. -/
def fockGibbsProbability (energy number : I → ℝ) (beta mu : ℝ) (i : I) : ℝ :=
  fockGibbsWeight energy number beta mu i / fockPartition energy number beta mu

/-- PDF p.7, Eq.(44), p.8, Eq.(50), p.11, Eq.(56): Shannon entropy of a
NORMALIZED probability law, rather than entropy of mean occupations. -/
def countableShannonBits (p : I → ℝ) : ℝ≥0∞ := ∑' i, ENNReal.ofReal (bitEntropyWeight (p i))

/-- PDF pp.5--8: the normalizable, finite-moment, finite-entropy Gibbs domain.
These conditions do not assert optimality, attainment, or the mode-entropy formula. -/
def GibbsRegular (energy number : I → ℝ) (beta mu : ℝ) : Prop :=
  Summable (fockGibbsWeight energy number beta mu) ∧
  0 < fockPartition energy number beta mu ∧
  Summable (fun i => energy i * fockGibbsProbability energy number beta mu i) ∧
  Summable (fun i => number i * fockGibbsProbability energy number beta mu i) ∧
  countableShannonBits (fockGibbsProbability energy number beta mu) < ⊤

/-- PDF pp.7,8,11: the constructed orthogonal number-state ensemble. -/
def fockEnsemble (b : HilbertBasis I ℂ H) (energy number : I → ℝ)
    (beta mu : ℝ) : FockEnsembleData I H where
  p := fockGibbsProbability energy number beta mu
  rho := fun i => InnerProductSpace.rankOne ℂ (b i) (b i)

example (beta mu : ℝ) :
    fockGibbsProbability (fun _ : Unit => 0) (fun _ : Unit => 0) beta mu () = 1 := by
  simp [fockGibbsProbability, fockPartition, fockGibbsWeight, tsum_fintype]

/-- PDF pp.7--8: actual Gibbs mean, not a free value tied by an optimality assumption. -/
def fockGibbsMean (energy number v : I → ℝ) (beta mu : ℝ) : ℝ :=
  ∑' i, v i * fockGibbsProbability energy number beta mu i

/-- PDF pp.7,8,11: full attainment claim, both Holevo and single-copy accessible
information, plus the explicit entropy formula. Both capacities are optimized
independently above; average-state entropy finiteness is a conclusion. -/
def ThermalAttainment (b : HilbertBasis I ℂ H) (energy number : I → ℝ)
    (beta mu : ℝ) (N : Option ℝ) (modeEntropy : ℝ≥0∞) : Prop :=
  let E := fockGibbsMean energy number energy beta mu
  let e := fockEnsemble b energy number beta mu
  let S := countableShannonBits e.p
  FockAdmissible b energy number E N e ∧
  IsFockPOVM (fockMeasurement b) ∧ fockMeasuredInformation b e (fockMeasurement b) = S ∧
  fockEntropyBits b (fockAverage e) = S ∧ fockHolevoBits b e = S ∧ fockAccessibleInformation b e = S ∧
  fockClassicalCapacity b energy number E N = S ∧
  singleCopyCapacity b energy number E N = S ∧ S = modeEntropy ∧
  ∀ other : FockEnsembleData I H, FockAdmissible b energy number E N other →
    fockEntropyBits b (fockAverage other) ≤ S

example (x y : H) : InnerProductSpace.rankOne ℂ x x y = (inner ℂ x y) • x := rfl

example : relativeTermBits 0 0 = 0 := by simp [relativeTermBits]

/-- PDF p.14, Eq.(86): power-law trap exponent a=d/gamma+d/2. -/
def trapExponent (d : ℕ) (gamma : ℝ) : ℝ := (d : ℝ) / gamma + (d : ℝ) / 2

/-- PDF p.14, Eq.(86): semiclassical density, on positive energies only. A is the
common positive normalization from phase space, including the mass and trap scale. -/
def densityOfStates (A a energy : ℝ) : ℝ := A * energy ^ (a - 1)

/-- PDF p.14, Eqs.(83),(85): the actual classical single-particle energy on
momentum-position phase space, with ordinary Euclidean Lebesgue volume.
The first component is momentum and the second is position. -/
def powerLawPhaseSpaceEnergy (d : ℕ) (gamma m : ℝ)
    (w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖w.1‖ ^ 2 / (2 * m) + ‖w.2‖ ^ gamma

example (d : ℕ) (gamma m : ℝ) (hgamma : 0 < gamma) :
    powerLawPhaseSpaceEnergy d gamma m (0, 0) = 0 := by
  simp [powerLawPhaseSpaceEnergy, Real.zero_rpow hgamma.ne']

/-- PDF pp.12--14, Eqs.(63),(86): continuum Boltzmann moment S_k. -/
def boltzmannMoment (A a beta : ℝ) (k : ℕ) : ℝ :=
  ∫ e in Set.Ioi (0 : ℝ), densityOfStates A a e * Real.exp (-(k : ℝ) * beta * e)

/-- PDF pp.13--14, Eq.(77): D_k has beta*energy, not k*beta*energy. -/
def weightedMoment (A a beta : ℝ) (k : ℕ) : ℝ :=
  ∫ e in Set.Ioi (0 : ℝ), beta * e * densityOfStates A a e *
    Real.exp (-(k : ℝ) * beta * e)

/-- PDF pp.12--15: spinless continuum occupations at fugacity z=exp(beta*mu).
The Boolean selects fermions; false selects bosons. -/
def continuumOccupation (fermion : Bool) (beta z energy : ℝ) : ℝ :=
  z / (Real.exp (beta * energy) + if fermion then z else -z)

/-- PDF pp.12--15: excited-state particle-number integral. For bosons a>1 is
used at z=1; all retained comparison theorems satisfy this restriction. -/
def continuumNumber (fermion : Bool) (A a beta z : ℝ) : ℝ :=
  ∫ e in Set.Ioi (0 : ℝ), densityOfStates A a e * continuumOccupation fermion beta z e

/-- PDF pp.12--15: continuum entropy at a specified fugacity, in bits. -/
def continuumEntropy (fermion : Bool) (A a beta z : ℝ) : ℝ :=
  ∫ e in Set.Ioi (0 : ℝ), densityOfStates A a e *
    (if fermion then fermiEntropy (continuumOccupation true beta z e)
     else boseEntropy (continuumOccupation false beta z e))

/-- PDF pp.9,14--15: Bose fugacity solved from fixed mean N. The supremum clips
at one in the condensed regime. The uncounted ground condensate has zero entropy
in this continuum thermodynamic model. This is not finite-trap exact thermodynamics.
The defining set contains zero and lies in [0,1] for positive A,a,beta,N with a>1. -/
def boseFugacity (A a beta N : ℝ) : ℝ :=
  sSup {z : ℝ | 0 ≤ z ∧ z ≤ 1 ∧ continuumNumber false A a beta z ≤ N}

/-- PDF pp.12--15: Fermi fugacity is solved separately at the same mean N. On
positive A,a,beta,N the set is nonempty, bounded below, and its infimum is the
unique positive solution. No equality of the Bose and Fermi energies is imposed. -/
def fermiFugacity (A a beta N : ℝ) : ℝ :=
  sInf {z : ℝ | 0 ≤ z ∧ N ≤ continuumNumber true A a beta z}

/-- PDF pp.12--15: the explicit CLASSICAL thermodynamic capacity curve in the
continuum model used in Sections IX--X, evaluated at its fixed-N equilibrium.
It is not a definition of an operational quantum capacity. -/
def thermodynamicCapacity (fermion : Bool) (A a kB N T : ℝ) : ℝ :=
  let beta := (kB * T)⁻¹
  let z := if fermion then fermiFugacity A a beta N else boseFugacity A a beta N
  continuumEntropy fermion A a beta z

example (beta e : ℝ) : continuumOccupation false beta 0 e = 0 := by
  simp [continuumOccupation]

example (A a beta : ℝ) : continuumNumber true A a beta 0 = 0 := by
  simp [continuumNumber, continuumOccupation]

end QAlgorithms.Papers.Independent.Advance50.P31


