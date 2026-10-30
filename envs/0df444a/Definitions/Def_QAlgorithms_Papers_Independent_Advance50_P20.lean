-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P20
-- name    : QAlgorithms_Papers_Independent_Advance50_P20
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:27:24.180784+00:00
-- url     : https://prove2.me/theorems/46538520-cd15-40f7-8b3f-ad267ba3a19d
-- title:
--   Definitions for Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels
-- statement:
--   The objects the formalized statements of *Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels* (arXiv:1604.07859) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhotonFamily`: PDF pp.3--4, Table I: the three canonical oscillator families. Distinct from the frozen Complexity.Family of finite qubit circuit families.
--   - `PhotonParameter`: PDF p.4, Table I: the amplitude parameter domain for each oscillator family. The frozen predicates named Admissible concern different objects.
--   - `conjugatorScale`: PDF p.6, Eq.(19): d_k, whose denominator never vanishes.
--   - `amplifierUnitaryMatrix`: PDF p.5, Eq.(11): all four indices of the squeeze unitary, independently of the environment photon number. The delta conditions are natural equalities.
--   - `attenuatorUnitaryMatrix`: PDF p.5, Eq.(15): the fixed beamsplitter, with the printed reflected-port minus sign. In particular U|0,1> = -sqrt(1-k^2)|1,0>+k|0,1>.
--   - `conjugatorUnitaryMatrix`: PDF p.6, Eq.(19), extended continuously to k=0: replace the reciprocal sqrt(1+k^(-2)) factor by k/sqrt(1+k^2). All exponents are nonnegative on the finite summation ranges. At zero this is the unsigned mode swap.
--   - `dilationMatrix`: PDF pp.5--6, Eqs.(11),(15),(19): the source's independent dilation data.
--   - `dilationUnitary`: PDF pp.2,4--6: choose the unique specified unitary, up to its fixed matrix. The identity fallback is never presumed to have the source coefficients: DilationRealized is concluded in every theorem using this selection.
--   - `DilationRealized`: PDF pp.2,4--6: realization of the specified full infinite matrix.
--   - `numberDensity`: PDF pp.2--4: the normalized environment number projector.
--   - `photonChannel`: PDF pp.2--4, Eq.(1): the channel is defined by the fixed unitary and product environment |n><n|, before any Kraus representation is asserted.
--   - `photonComplement`: PDF p.9, Eq.(31): trace the system in the very same pure-environment dilation.
--   - `amplifierG`: PDF p.5, Eq.(13). Icc represents the actual valid inclusive summation range.
--   - `attenuatorG`: PDF p.6, Eq.(17). n+r-ell is formed as a single nonnegative difference, not as the truncated expression (n-ell)+r.
--   - `conjugatorG`: PDF p.7, Eq.(21), with the reciprocal-free k=0 extension. The original negative powers mean powers of the inverse, not natural-number subtraction.
--   - `krausEntry`: PDF pp.5--7, Eqs.(14),(18),(22): real row-m,column-j Kraus coefficients. Natural equalities impose support before any factorial of a difference is used.
--   - `photonKrausMatrix`: PDF pp.5--7: the displayed bounded-operator Kraus coefficients on full Fock space. Distinct from Bridge50.P30.krausMatrix, a finite-channel population matrix.
--   - `photonKraus`: PDF pp.5--7: bounded Kraus realization; matrix realization is a conclusion.
--   - `KrausRealized`: PDF pp.5--7: all coefficient realizations, independently of normalization.
--   - `TraceSeries`: PDF pp.2,7,14: unconditional trace-norm convergence on genuine trace class. The extended norm is infinity outside its nuclear domain, never default zero.
--   - `FockDiagonal`: PDF pp.7,12, Eq.(36): vanishing off-diagonal number-basis entries.
--   - `fockDephase`: PDF p.12, Eq.(37): complete Fock dephasing, on full trace class.
--   - `fockOutputIndex`: PDF pp.7--8, Eqs.(23),(25),(26): output number of the ell-th term. All uses are restricted by FockIndexValid, including zero coefficients.
--   - `FockIndexValid`: PDF pp.7--8: exactly the displayed summation ranges.
--   - `fockWeight`: PDF pp.7--8: the squared coefficients in Eqs.(23),(25),(26). The scalar coefficient, factorial and g factors are explicitly defined above.
--   - `CommonAttainedMinimum`: PDF pp.9--10, Corollary 9: an attained common minimum, with a normalized pure minimizing input, and a lower bound on every normalized input.
--   - `canonicalThermalChannel`: PDF pp.13--14, Eq.(44): noisy channel from the same canonical coupling. The imported thermalKernel is the full mean-N density array. Unlike the frozen Claimed50.P35.noisyChannel (additive displacement noise after A/B), this construction includes all three canonical couplings and their fixed environment.
--   - `canonicalArgument`: PDF pp.13--14, Eq.(43): source phase-space argument in standard D(z) axes.
--   - `quantumLimitedNoise`: PDF pp.13--14: quantum-limited scalar noise in complex coordinates, with vacuum chi(z)=exp(-|z|^2/2). Extra thermal noise is 2*N times this value.
--   - `addedThermalWeight`: PDF pp.14--15: normalized photon-added thermal probabilities, after shifting j to j+n. Addition is postselected state preparation, not a CPTP map.
--   - `addedPurificationCoefficient`: PDF pp.14--15: add n photons on the first purification mode, then normalize.
--   - `addedPurification`: PDF pp.14--15: the full square-summable pure environment. Its Hilbert realization and unit norm are conclusions of the construction theorem.
--   - `addedThermalEnvironment`: PDF pp.14--15: mixed photon-added thermal environment, all four regimes.
--   - `liftedCouplingMatrix`: PDF pp.14--15: U on system and first environment, identity on untouched second environment, on the completed three-mode space.
--   - `pureAddedNoisyChannel`: PDF pp.14--15, Fig.16: couple the pure normalized preparation, trace both modes.
--   - `mixedAddedNoisyChannel`: PDF pp.14--15, Fig.17: first trace the unused mode, then couple the mixed PATS.
--   - `quadraticEntry`: PDF pp.18--19, Eqs.(49)--(52): corrected closed quadratic coefficient. Printed (49) has (ell-n+j)! squared; changed to (ell+n-j)! squared. Printed (52) omits the factorial on j+ell-ell'; changed to k!. Both corrections follow the unexpanded products in (49),(51) and (14),(18),(22). No independence or extremality is part of this definition.
--   - `activationInput`: PDF pp.10--11: first constructive input, with exact normalized weights.
--   - `activationAmplitude`: PDF pp.10--11: the parameter is sqrt((3/2)^2-1), fixed by Fig.12 and the complementary gain 3/2; the Table III caption drops a square.
--   - `FullFockPrivateAchievable`: PDF pp.10--11, operational private capacity convention: arbitrary mixed block inputs and CPTP decoding, no assistance or energy constraint. Both maximal message error and half trace-norm secrecy tend to zero, with one common Eve state per code. These standard strong criteria define the same asymptotic rate. All code data precede the message quantifier, and block lengths are positive. Frozen Dependency50.P48.PrivateAchievable and Support50.P07.FullTracePrivateAchievable use finite receiver/environment types; this is a distinct full Fock-space interface.
--   - `fullFockPrivateCapacity`: PDF pp.10--11: nonnegative operational private rates, infinity retained. Unlike Information100.P67.privateCapacity, this uses full Fock trace-class codes and an extended nonnegative supremum.
--   - `JointPhaseIndex`: PDF p.3, Eq.(5): full finite-mode phase space; S is the printed S inverse.
--   - `jointWeyl`: PDF p.3, Eqs.(5)--(7): joint Weyl coordinates for independent registers.
--   - `GaussianCoupling`: PDF p.3, Eqs.(5)--(7): Gaussian-unitary Weyl implementation. Allows affine means via a real linear phase; no Gaussian assumption on the environment state. The Weyl law is a definition of the unitary's Gaussian action, not the channel factorization which Proposition 1 proves.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, https://arxiv.org/abs/1604.07859v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

/-!
Sabapathy--Winter, arXiv:1604.07859v4. Full oscillator Hilbert spaces, no
photon cutoff. The channels are fixed-unitary partial traces, independently of
the proposed Kraus families. Every choice-based realization is a conclusion.
The source's open conjectures and defective universal assertions are deferred.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P20

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne productCoeff traceSize)
open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad HasFockMatrix operatorOfMatrix KrausComplete
    CoherentRealized IsClassical husimiQ)
open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff IsKrausRepresentation)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation unitaryCoeff conjugateKernel partialRight partialLeft dilationReceiver weakComplement
    boundedUnitaryConjugation traceClassTensorPower operationalTraceClassCapacity)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (InterleavedPhase ScaledWeylRepresentation physicalCommutationMatrix
    weylTraceCharacteristic LinearBosonic)

-- Accepted extended bit entropy and mean-photon thermal coefficients.
open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits thermalKernel)
open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, Table I: the three canonical oscillator families.
Distinct from the frozen Complexity.Family of finite qubit circuit families. -/
inductive PhotonFamily where
  | amplifier | attenuator | conjugator
  deriving DecidableEq

/-- PDF p.4, Table I: the amplitude parameter domain for each oscillator family.
The frozen predicates named Admissible concern different objects. -/
def PhotonParameter (c : PhotonFamily) (k : ℝ) : Prop :=
  match c with
  | .amplifier => 1 ≤ k
  | .attenuator => 0 ≤ k ∧ k ≤ 1
  | .conjugator => 0 ≤ k

/-- PDF p.6, Eq.(19): d_k, whose denominator never vanishes. -/
def conjugatorScale (k : ℝ) : ℝ := (Real.sqrt (1 + k ^ 2))⁻¹

/-- PDF p.5, Eq.(11): all four indices of the squeeze unitary, independently
of the environment photon number. The delta conditions are natural equalities. -/
def amplifierUnitaryMatrix (k : ℝ) (out inp : ℕ × ℕ) : ℂ :=
  let m := out.1; let ell := out.2; let j := inp.1; let n := inp.2
  (k⁻¹ * Real.sqrt (((j.factorial : ℝ) * ell.factorial) /
    ((m.factorial : ℝ) * n.factorial)) *
    ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (m + 1),
      if j = r + t ∧ ell + r + t = n + m then
        (Nat.choose n r : ℝ) * (Nat.choose m t : ℝ) * (-1 : ℝ) ^ r *
          k⁻¹ ^ (n + t - r) * Real.sqrt (1 - k⁻¹ ^ 2) ^ (m + r - t)
      else 0 : ℝ)

/-- PDF p.5, Eq.(15): the fixed beamsplitter, with the printed reflected-port
minus sign. In particular U|0,1> = -sqrt(1-k^2)|1,0>+k|0,1>. -/
def attenuatorUnitaryMatrix (k : ℝ) (out inp : ℕ × ℕ) : ℂ :=
  let m := out.1; let ell := out.2; let j := inp.1; let n := inp.2
  (Real.sqrt (((m.factorial : ℝ) * ell.factorial) /
    ((j.factorial : ℝ) * n.factorial)) *
    ∑ r ∈ Finset.range (j + 1), ∑ t ∈ Finset.range (n + 1),
      if ell = r + t ∧ m + r + t = j + n then
        (Nat.choose j r : ℝ) * (Nat.choose n t : ℝ) * (-1 : ℝ) ^ (n - t) *
          k ^ (j - r + t) * Real.sqrt (1 - k ^ 2) ^ (r + n - t)
      else 0 : ℝ)

/-- PDF p.6, Eq.(19), extended continuously to k=0: replace the reciprocal
sqrt(1+k^(-2)) factor by k/sqrt(1+k^2). All exponents are nonnegative on
the finite summation ranges. At zero this is the unsigned mode swap. -/
def conjugatorUnitaryMatrix (k : ℝ) (out inp : ℕ × ℕ) : ℂ :=
  let m := out.1; let ell := out.2; let j := inp.1; let n := inp.2
  (conjugatorScale k * Real.sqrt (((n.factorial : ℝ) * ell.factorial) /
    ((m.factorial : ℝ) * j.factorial)) *
    ∑ r ∈ Finset.range (m + 1), ∑ t ∈ Finset.range (j + 1),
      if n = r + t ∧ ell + r + t = j + m then
        (Nat.choose m r : ℝ) * (Nat.choose j t : ℝ) *
          conjugatorScale k ^ (j + r - t) * (-1 : ℝ) ^ t *
          (k * conjugatorScale k) ^ (m - r + t)
      else 0 : ℝ)

/-- PDF pp.5--6, Eqs.(11),(15),(19): the source's independent dilation data. -/
def dilationMatrix (c : PhotonFamily) (k : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  match c with
  | .amplifier => amplifierUnitaryMatrix k
  | .attenuator => attenuatorUnitaryMatrix k
  | .conjugator => conjugatorUnitaryMatrix k

/-- PDF pp.2,4--6: choose the unique specified unitary, up to its fixed matrix.
The identity fallback is never presumed to have the source coefficients:
DilationRealized is concluded in every theorem using this selection. -/
def dilationUnitary (c : PhotonFamily) (k : ℝ) : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ) :=
  if h : ∃ U : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ),
      unitaryCoeff U = dilationMatrix c k then Classical.choose h
  else LinearIsometryEquiv.refl ℂ (Hilbert (ℕ × ℕ))

/-- PDF pp.2,4--6: realization of the specified full infinite matrix. -/
def DilationRealized (c : PhotonFamily) (k : ℝ) : Prop :=
  unitaryCoeff (dilationUnitary c k) = dilationMatrix c k

/-- PDF pp.2--4: the normalized environment number projector. -/
def numberDensity (n : ℕ) : Matrix ℕ ℕ ℂ := Matrix.single n n 1

/-- PDF pp.2--4, Eq.(1): the channel is defined by the fixed unitary and
product environment |n><n|, before any Kraus representation is asserted. -/
def photonChannel (c : PhotonFamily) (k : ℝ) (n : ℕ) : Operation ℕ ℕ :=
  dilationReceiver (dilationUnitary c k) (numberDensity n)

/-- PDF p.9, Eq.(31): trace the system in the very same pure-environment dilation. -/
def photonComplement (c : PhotonFamily) (k : ℝ) (n : ℕ) : Operation ℕ ℕ :=
  weakComplement (dilationUnitary c k) (numberDensity n)

/-- PDF p.5, Eq.(13). Icc represents the actual valid inclusive summation range. -/
def amplifierG (n j m : ℕ) (k : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc (j - m) (min n j),
    (Nat.choose n r : ℝ) * (Nat.choose m (j - r) : ℝ) * (-1 : ℝ) ^ r *
      k⁻¹ ^ (n + j - 2 * r) * Real.sqrt (1 - k⁻¹ ^ 2) ^ (m + 2 * r - j)

/-- PDF p.6, Eq.(17). n+r-ell is formed as a single nonnegative difference,
not as the truncated expression (n-ell)+r. -/
def attenuatorG (n ell j : ℕ) (k : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc (ell - n) (min ell j),
    (Nat.choose j r : ℝ) * (Nat.choose n (ell - r) : ℝ) * (-1 : ℝ) ^ (n + r - ell) *
      k ^ (j + ell - 2 * r) * Real.sqrt (1 - k ^ 2) ^ (2 * r + n - ell)

/-- PDF p.7, Eq.(21), with the reciprocal-free k=0 extension. The original
negative powers mean powers of the inverse, not natural-number subtraction. -/
def conjugatorG (n j m : ℕ) (k : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc (n - j) (min n m),
    (Nat.choose m r : ℝ) * (Nat.choose j (n - r) : ℝ) *
      (k * conjugatorScale k) ^ (m + n - 2 * r) * (-1 : ℝ) ^ (n - r) *
      conjugatorScale k ^ (j + 2 * r - n)

/-- PDF pp.5--7, Eqs.(14),(18),(22): real row-m,column-j Kraus coefficients.
Natural equalities impose support before any factorial of a difference is used. -/
def krausEntry (c : PhotonFamily) (k : ℝ) (n ell m j : ℕ) : ℝ :=
  match c with
  | .amplifier => if m + n = j + ell then
      k⁻¹ * Real.sqrt (((j.factorial : ℝ) * ell.factorial) /
        ((m.factorial : ℝ) * n.factorial)) * amplifierG n j m k else 0
  | .attenuator => if m + ell = j + n then
      Real.sqrt (((m.factorial : ℝ) * ell.factorial) /
        ((j.factorial : ℝ) * n.factorial)) * attenuatorG n ell j k else 0
  | .conjugator => if m + j = n + ell then
      conjugatorScale k * Real.sqrt (((n.factorial : ℝ) * ell.factorial) /
        ((m.factorial : ℝ) * j.factorial)) * conjugatorG n j m k else 0

/-- PDF pp.5--7: the displayed bounded-operator Kraus coefficients on full Fock space.
Distinct from Bridge50.P30.krausMatrix, a finite-channel population matrix. -/
def photonKrausMatrix (c : PhotonFamily) (k : ℝ) (n ell : ℕ) : Matrix ℕ ℕ ℂ :=
  fun m j => (krausEntry c k n ell m j : ℂ)

/-- PDF pp.5--7: bounded Kraus realization; matrix realization is a conclusion. -/
def photonKraus (c : PhotonFamily) (k : ℝ) (n ell : ℕ) : FockOperator :=
  operatorOfMatrix (photonKrausMatrix c k n ell)

/-- PDF pp.5--7: all coefficient realizations, independently of normalization. -/
def KrausRealized (c : PhotonFamily) (k : ℝ) (n : ℕ) : Prop :=
  ∀ ell, HasFockMatrix (photonKraus c k n ell) (photonKrausMatrix c k n ell)

/-- PDF pp.2,7,14: unconditional trace-norm convergence on genuine trace class.
The extended norm is infinity outside its nuclear domain, never default zero. -/
def TraceSeries {I J : Type} (f : I → Matrix J J ℂ) (Y : Matrix J J ℂ) : Prop :=
  IsTraceClass Y ∧ (∀ i, IsTraceClass (f i)) ∧
    Tendsto (fun s : Finset I => traceSize (Y - ∑ i ∈ s, f i)) atTop (nhds 0)

/-- PDF pp.7,12, Eq.(36): vanishing off-diagonal number-basis entries. -/
def FockDiagonal (X : Matrix ℕ ℕ ℂ) : Prop := ∀ i j, i ≠ j → X i j = 0

/-- PDF p.12, Eq.(37): complete Fock dephasing, on full trace class. -/
def fockDephase (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  fun i j => if i = j then X i i else 0

/-- PDF pp.7--8, Eqs.(23),(25),(26): output number of the ell-th term.
All uses are restricted by FockIndexValid, including zero coefficients. -/
def fockOutputIndex (c : PhotonFamily) (n j ell : ℕ) : ℕ :=
  match c with
  | .amplifier => j + ell - n
  | .attenuator => j + n - ell
  | .conjugator => n + ell - j

/-- PDF pp.7--8: exactly the displayed summation ranges. -/
def FockIndexValid (c : PhotonFamily) (n j ell : ℕ) : Prop :=
  match c with
  | .amplifier => n ≤ j + ell
  | .attenuator => ell ≤ j + n
  | .conjugator => j ≤ n + ell

/-- PDF pp.7--8: the squared coefficients in Eqs.(23),(25),(26).
The scalar coefficient, factorial and g factors are explicitly defined above. -/
def fockWeight (c : PhotonFamily) (k : ℝ) (n j ell : ℕ) : ℝ :=
  if FockIndexValid c n j ell then
    krausEntry c k n ell (fockOutputIndex c n j ell) j ^ 2 else 0

/-- PDF pp.9--10, Corollary 9: an attained common minimum, with a normalized
pure minimizing input, and a lower bound on every normalized input. -/
def CommonAttainedMinimum (E F : Operation ℕ ℕ) : Prop :=
  ∃ h : ℝ≥0∞, ∃ rho : PureState ℕ,
    entropyBits (E rho.val.coefficients) = h ∧
    entropyBits (F rho.val.coefficients) = h ∧
    ∀ sigma : State ℕ,
      h ≤ entropyBits (E sigma.coefficients) ∧ h ≤ entropyBits (F sigma.coefficients)

/-- PDF pp.13--14, Eq.(44): noisy channel from the same canonical coupling.
The imported thermalKernel is the full mean-N density array. Unlike the frozen
Claimed50.P35.noisyChannel (additive displacement noise after A/B), this
construction includes all three canonical couplings and their fixed environment. -/
def canonicalThermalChannel (c : PhotonFamily) (k N : ℝ) : Operation ℕ ℕ :=
  dilationReceiver (dilationUnitary c k) (thermalKernel N)

/-- PDF pp.13--14, Eq.(43): source phase-space argument in standard D(z) axes. -/
def canonicalArgument (c : PhotonFamily) (k : ℝ) (z : ℂ) : ℂ :=
  match c with
  | .amplifier => (k : ℂ) * z
  | .attenuator => (k : ℂ) * z
  | .conjugator => -(k : ℂ) * star z

/-- PDF pp.13--14: quantum-limited scalar noise in complex coordinates, with
vacuum chi(z)=exp(-|z|^2/2). Extra thermal noise is 2*N times this value. -/
def quantumLimitedNoise (c : PhotonFamily) (k : ℝ) : ℝ :=
  match c with
  | .amplifier => k ^ 2 - 1
  | .attenuator => 1 - k ^ 2
  | .conjugator => 1 + k ^ 2

/-- PDF pp.14--15: normalized photon-added thermal probabilities, after shifting
j to j+n. Addition is postselected state preparation, not a CPTP map. -/
def addedThermalWeight (N : ℝ) (n j : ℕ) : ℝ :=
  (Nat.choose (j + n) n : ℝ) * N ^ j / (1 + N) ^ (j + n + 1)

/-- PDF pp.14--15: add n photons on the first purification mode, then normalize. -/
def addedPurificationCoefficient (N : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℂ :=
  if p.1 = p.2 + n then (Real.sqrt (addedThermalWeight N n p.2) : ℂ) else 0

/-- PDF pp.14--15: the full square-summable pure environment. Its Hilbert
realization and unit norm are conclusions of the construction theorem. -/
def addedPurification (N : ℝ) (n : ℕ) : Hilbert (ℕ × ℕ) :=
  if h : ∃ v : Hilbert (ℕ × ℕ), ∀ p, v p = addedPurificationCoefficient N n p then
    Classical.choose h else 0

/-- PDF pp.14--15: mixed photon-added thermal environment, all four regimes. -/
def addedThermalEnvironment (N : ℝ) (n : ℕ) : Matrix ℕ ℕ ℂ :=
  fun i j => if i = j ∧ n ≤ i then (addedThermalWeight N n (i - n) : ℂ) else 0

/-- PDF pp.14--15: U on system and first environment, identity on untouched
second environment, on the completed three-mode space. -/
def liftedCouplingMatrix (c : PhotonFamily) (k : ℝ) :
    Matrix (ℕ × (ℕ × ℕ)) (ℕ × (ℕ × ℕ)) ℂ :=
  fun p q => if p.2.2 = q.2.2 then
    unitaryCoeff (dilationUnitary c k) (p.1, p.2.1) (q.1, q.2.1) else 0

/-- PDF pp.14--15, Fig.16: couple the pure normalized preparation, trace both modes. -/
def pureAddedNoisyChannel (c : PhotonFamily) (k N : ℝ) (n : ℕ) : Operation ℕ ℕ :=
  fun X => partialRight (conjugateKernel (liftedCouplingMatrix c k)
    (productCoeff X (rankOne (addedPurification N n))))

/-- PDF pp.14--15, Fig.17: first trace the unused mode, then couple the mixed PATS. -/
def mixedAddedNoisyChannel (c : PhotonFamily) (k N : ℝ) (n : ℕ) : Operation ℕ ℕ :=
  dilationReceiver (dilationUnitary c k) (addedThermalEnvironment N n)

/-- PDF pp.18--19, Eqs.(49)--(52): corrected closed quadratic coefficient.
Printed (49) has (ell-n+j)! squared; changed to (ell+n-j)! squared.
Printed (52) omits the factorial on j+ell-ell'; changed to k!.
Both corrections follow the unexpanded products in (49),(51) and (14),(18),(22).
No independence or extremality is part of this definition. -/
def quadraticEntry (c : PhotonFamily) (k : ℝ) (n ell ell2 j h : ℕ) : ℝ :=
  match c with
  | .amplifier =>
      if n ≤ j + ell ∧ h + ell2 = j + ell then
        let m := j + ell - n
        k⁻¹ ^ 2 * Real.sqrt
          (((j.factorial : ℝ) * h.factorial * ell.factorial * ell2.factorial) /
            ((m.factorial : ℝ) ^ 2 * (n.factorial : ℝ) ^ 2)) *
          amplifierG n h m k * amplifierG n j m k
      else 0
  | .attenuator =>
      if ell ≤ j + n ∧ h + ell = j + ell2 then
        let m := j + n - ell
        Real.sqrt (((m.factorial : ℝ) ^ 2 * ell.factorial * ell2.factorial) /
          ((j.factorial : ℝ) * h.factorial * (n.factorial : ℝ) ^ 2)) *
          attenuatorG n ell j k * attenuatorG n ell2 h k
      else 0
  | .conjugator =>
      if j ≤ n + ell ∧ h ≤ n + ell2 ∧ h + ell = j + ell2 then
        let m := n + ell - j
        conjugatorScale k ^ 2 * Real.sqrt
          (((n.factorial : ℝ) ^ 2 * ell.factorial * ell2.factorial) /
            ((m.factorial : ℝ) ^ 2 * j.factorial * h.factorial)) *
          conjugatorG n h m k * conjugatorG n j m k
      else 0

/-- PDF pp.10--11: first constructive input, with exact normalized weights. -/
def activationInput : Matrix ℕ ℕ ℂ :=
  (3 / 5 : ℂ) • numberDensity 0 + (2 / 5 : ℂ) • numberDensity 1

/-- PDF pp.10--11: the parameter is sqrt((3/2)^2-1), fixed by Fig.12 and the
complementary gain 3/2; the Table III caption drops a square. -/
def activationAmplitude : ℝ := Real.sqrt ((3 / 2 : ℝ) ^ 2 - 1)

/-- PDF pp.10--11, operational private capacity convention: arbitrary mixed
block inputs and CPTP decoding, no assistance or energy constraint. Both maximal
message error and half trace-norm secrecy tend to zero, with one common Eve
state per code. These standard strong criteria define the same asymptotic rate.
All code data precede the message quantifier, and block lengths are positive.
Frozen Dependency50.P48.PrivateAchievable and Support50.P07.FullTracePrivateAchievable
use finite receiver/environment types; this is a distinct full Fock-space interface. -/
def FullFockPrivateAchievable (E Ec : Operation ℕ ℕ) (R : NNReal) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ delta : ℝ, 0 < delta →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ M : ℕ, 0 < M ∧
      ∃ inputs : Fin M → State (Fin n → ℕ),
      ∃ Dec : Operation (Fin n → ℕ) (Fin M),
        IsTraceClassChannel Dec ∧
        (R : ℝ) - delta ≤ Real.logb 2 M / (n : ℝ) ∧
        ∃ sigma : State (Fin n → ℕ), ∀ m : Fin M,
          1 - eps ≤ (Dec (traceClassTensorPower E n (inputs m).coefficients) m m).re ∧
          traceSize (traceClassTensorPower Ec n (inputs m).coefficients - sigma.coefficients) / 2 ≤
            ENNReal.ofReal eps

/-- PDF pp.10--11: nonnegative operational private rates, infinity retained.
Unlike Information100.P67.privateCapacity, this uses full Fock trace-class
codes and an extended nonnegative supremum. -/
def fullFockPrivateCapacity (E Ec : Operation ℕ ℕ) : ℝ≥0∞ :=
  ⨆ R : {R : NNReal // FullFockPrivateAchievable E Ec R}, (R.val : ℝ≥0∞)

/-- PDF p.3, Eq.(5): full finite-mode phase space; S is the printed S inverse. -/
abbrev JointPhaseIndex (s t : ℕ) := (Fin s × Fin 2) ⊕ (Fin t × Fin 2)

/-- PDF p.3, Eqs.(5)--(7): joint Weyl coordinates for independent registers. -/
def jointWeyl {s t : ℕ}
    (W : ScaledWeylRepresentation (Fin s → ℕ) s 1)
    (V : ScaledWeylRepresentation (Fin t → ℕ) t 1)
    (z : JointPhaseIndex s t → ℝ) :
    Matrix ((Fin s → ℕ) × (Fin t → ℕ)) ((Fin s → ℕ) × (Fin t → ℕ)) ℂ :=
  productCoeff (operatorCoeff (W.operator (z ∘ Sum.inl)))
    (operatorCoeff (V.operator (z ∘ Sum.inr)))

/-- PDF p.3, Eqs.(5)--(7): Gaussian-unitary Weyl implementation. Allows affine
means via a real linear phase; no Gaussian assumption on the environment state.
The Weyl law is a definition of the unitary's Gaussian action, not the channel
factorization which Proposition 1 proves. -/
def GaussianCoupling {s t : ℕ}
    (W : ScaledWeylRepresentation (Fin s → ℕ) s 1)
    (V : ScaledWeylRepresentation (Fin t → ℕ) t 1)
    (U : Hilbert ((Fin s → ℕ) × (Fin t → ℕ)) ≃ₗᵢ[ℂ]
      Hilbert ((Fin s → ℕ) × (Fin t → ℕ)))
    (S : Matrix (JointPhaseIndex s t) (JointPhaseIndex s t) ℝ)
    (d : JointPhaseIndex s t → ℝ) : Prop :=
  let J := Matrix.fromBlocks (physicalCommutationMatrix s 1) 0 0
    (physicalCommutationMatrix t 1)
  S.transpose * J * S = J ∧ ∀ z,
    boundedUnitaryConjugation U.symm (jointWeyl W V z) =
      Complex.exp (Complex.I * ((dotProduct d z : ℝ) : ℂ)) • jointWeyl W V (S.mulVec z)

/-! Sanity examples pin endpoints, signs and the full coefficient conventions. -/

example : PhotonParameter .amplifier 1 := by norm_num [PhotonParameter]

example : PhotonParameter .attenuator 0 := by norm_num [PhotonParameter]

example : conjugatorScale 0 = 1 := by norm_num [conjugatorScale]

example (n : ℕ) : numberDensity n n n = 1 := by simp [numberDensity]

example : attenuatorUnitaryMatrix 0 (1, 0) (0, 1) = -1 := by
  norm_num [attenuatorUnitaryMatrix, Finset.sum_range_succ]

example : thermalProbability 0 0 = 1 := by norm_num [thermalProbability]

example : addedThermalWeight 0 0 0 = 1 := by norm_num [addedThermalWeight]

example (X : Matrix ℕ ℕ ℂ) : fockDephase (fockDephase X) = fockDephase X := by
  funext i j
  by_cases h : i = j <;> simp [fockDephase, h]

example : conjugatorUnitaryMatrix 0 (1, 0) (0, 1) = 1 := by
  norm_num [conjugatorUnitaryMatrix, conjugatorScale, Finset.sum_range_succ]

example : amplifierG 0 0 0 1 = 1 := by
  norm_num [amplifierG]

example : attenuatorG 0 0 0 0 = 1 := by
  norm_num [attenuatorG]

example : conjugatorG 0 0 0 0 = 1 := by
  norm_num [conjugatorG, conjugatorScale]

example (k : ℝ) : krausEntry .conjugator k 0 0 1 0 = 0 := by
  simp [krausEntry]

example (N : ℝ) : addedThermalWeight N 0 0 = thermalProbability N 0 := by
  simp [addedThermalWeight, thermalProbability, add_comm]

example : activationInput 0 0 = (3 / 5 : ℂ) := by
  norm_num [activationInput, numberDensity]

end QAlgorithms.Papers.Independent.Advance50.P20


