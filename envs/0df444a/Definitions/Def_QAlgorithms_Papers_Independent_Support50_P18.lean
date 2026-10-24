-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18
-- name    : QAlgorithms_Papers_Independent_Support50_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:05:33.365791+00:00
-- url     : https://prove2.me/theorems/b86f4c1e-4c3a-4405-99fa-34d09d5d36ef
-- title:
--   Definitions for Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use
-- statement:
--   The objects the formalized statements of *Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use* (arXiv:1609.07044) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `logPowerLevel`: PDF p.8, Lemma 2: n+1 enumerates k=1,2,... . The first term is finite.
--   - `logPowerPartition`: PDF p.8, Lemma 2: a divergent partition sum is infinity, not zero.
--   - `OscillatorParameters`: Section 4.2, PDF p.9: positive physical parameters and at least one mode. This is a parameter record, not Frontier30.P07.Oscillator (the one-mode Hilbert space).
--   - `OscillatorParameters.quantum`: PDF p.9: the positive mode energy quanta hbar omega_i.
--   - `OscillatorParameters.level`: PDF p.9: eigenvalues of the actual Fock Hamiltonian, including the vacuum.
--   - `OscillatorParameters.domain`: PDF p.9: maximal dense domain of the self-adjoint diagonal Hamiltonian.
--   - `OscillatorParameters.apply`: PDF p.9: the Hamiltonian acts by its number-basis eigenvalues.
--   - `OscillatorParameters.ground`: PDF p.9: E0=(1/2) sum_i hbar omega_i.
--   - `OscillatorParameters.geometricMean`: PDF p.9, (23): geometric mean of the mode energy quanta.
--   - `OscillatorParameters.meanEnergy`: PDF pp.5,9: extended mean energy on positive trace-class arrays. The nonnegative series equals the increasing spectral-cutoff supremum.
--   - `OscillatorParameters.entropyMaximum`: PDF pp.7,9, (18): supremum of actual entropies over the energy ball.
--   - `OscillatorParameters.entropyUpper`: PDF p.9, (23): explicit oscillator entropy majorant.
--   - `OscillatorParameters.allocations`: PDF p.9: all admissible allocations, with equality of total energy.
--   - `OscillatorParameters.allocationEntropy`: PDF p.9: sum of single-mode entropies for a fixed allocation.
--   - `AFWConstants`: PDF pp.7--9: the four state-independent nonnegative constants (16),(17).
--   - `OscillatorParameters.finiteMarginalEnergy`: PDF p.9: finite energy of the actual oscillator marginal; R is arbitrary.
--   - `OscillatorParameters.EntropyControlled`: PDF pp.7,9: both inequalities (16),(17), exactly on finite-energy states. f accepts coefficient arrays, with values outside the source domain unconstrained. Actual matrix mixtures are used; normalization is not an additional premise.
--   - `OscillatorParameters.continuityBound`: PDF p.9, (24): ell and the logarithm are OUTSIDE sqrt(2 epsilon).
--   - `nuclearStateDistance`: PDF pp.5,9: normalized-state adapter to the imported full trace distance. The frozen QAlgorithms.traceDistance requires finite matrices and returns a real; the imported extendedHalfTraceDistance covers arbitrary nuclear coefficients.
--   - `SubsystemBasis`: PDF pp.9--10: complete basis for a selected multipartite subsystem.
--   - `ComplementBasis`: PDF pp.9--10: complete basis for the complementary subsystem.
--   - `joinBasis`: PDF pp.9--10: full basis coordinate reconstructed from its two factors.
--   - `subsystemMarginal`: PDF p.10: actual subsystem marginal, using the accepted completed partial trace.
--   - `entropyCombination`: PDF pp.9--10, (25): the prescribed finite real combination, on its domain of finite marginal entropies with nonzero coefficients. No infinite value is projected in the theorem.
--   - `spectralGround`: PDF p.5: infimum of the unit-vector energies, in a complete eigenbasis.
--   - `Condition22`: PDF p.8, (22): extended partition trace and a right-hand limit. Neither summability nor finite entropy is assumed separately.
--   - `TraceUniformContinuousOn`: Trace-distance uniform continuity on a specified state set (PDF pp.5,17--18). This epsilon-delta definition avoids imposing a coefficient uniformity.
--   - `marginalMutualInformation`: PDF p.4: genuine mutual information of a joint state, defined by relative entropy.
--   - `extendedConditionalEntropy`: PDF p.11, (28): finite-A-entropy conditional entropy, without infinity subtraction.
--   - `outputMutualInformation`: PDF p.17, (48): mutual information after the actual reference-amplified channel.
--   - `entropyModulus`: PDF p.8, (21): the real modulus, used only with proved finite F_H.
--   - `EnergyContinuity`: PDF pp.17--18: finite-valued uniform continuity and the quantitative bound, on one FIXED energy ball. This is a conclusion package, never a hypothesis.
--   - `countableRelativeEntanglementNats`: PDF p.14, (38): relative entropy distance to the actual trace-norm closed convex hull of product states. Empty infima retain infinity. The frozen P54 relativeEntanglement is finite-dimensional and in bits; this interface is in nats on arbitrary countable systems and cannot use that finite-dimensional function.
--   - `bipartiteTensorPower`: PDF pp.14,16: n copies, regrouped as A^n:B^n, without restricting other states of that tensor-power system to be products.
--   - `regularizedCountableEntanglementNats`: PDF p.14, (39): regularization as the extended infimum of ER(rho^n)/n, equivalent to the actual limit by subadditivity. Only positive block lengths are used; a divergent value remains infinity. The frozen P54 regularization is finite-dimensional and in bits, so it does not represent this domain.
--   - `additiveEnergy`: PDF p.16: additive tensor-power Hamiltonian eigenvalues.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, https://arxiv.org/abs/1609.07044v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

/-!
Statements from Shirokov, arXiv:1609.07044v5. Pinned accepted nuclear states,
trace norm and extended spectral entropies are reused. Product coordinates
represent completed Hilbert tensor products. General Hamiltonians, including
continuous spectra, are deferred rather than replaced by diagonal observables.
The oscillator uses its full Fock basis and includes zero-point energy.
Compilation is pending the separate batch handoff.
-/

noncomputable section

open Filter
open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-! The imported g is (x+1) log(x+1)-x log x (PDF p.9), equal to
(1+x) h2(x/(1+x)) for x>=0. Every use below has a nonnegative argument. -/

example : g 0 = 0 := by
  simp [QAlgorithms.Papers.Independent.Claimed50.P39.g]

/-- PDF p.8, Lemma 2: n+1 enumerates k=1,2,... . The first term is finite. -/
def logPowerLevel (q : ℝ) (n : ℕ) : ℝ := (Real.log (n + 1 : ℝ)) ^ q

/-- PDF p.8, Lemma 2: a divergent partition sum is infinity, not zero. -/
def logPowerPartition (q lambda : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (Real.exp (-lambda * logPowerLevel q n))

example : logPowerLevel 2 0 = 0 := by simp [logPowerLevel]

example (q lambda : ℝ) : logPowerPartition q lambda =
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (-lambda * logPowerLevel q n)) := rfl

/-- Section 4.2, PDF p.9: positive physical parameters and at least one mode.
This is a parameter record, not Frontier30.P07.Oscillator (the one-mode Hilbert space). -/
structure OscillatorParameters (ell : ℕ) where
  modes_pos : 0 < ell
  hbar : ℝ≥0
  hbar_pos : 0 < hbar
  omega : Fin ell → ℝ≥0
  omega_pos : ∀ i, 0 < omega i

/-- PDF p.9: the positive mode energy quanta hbar omega_i. -/
def OscillatorParameters.quantum {ell : ℕ} (O : OscillatorParameters ell) (i : Fin ell) : ℝ≥0 :=
  O.hbar * O.omega i

/-- PDF p.9: eigenvalues of the actual Fock Hamiltonian, including the vacuum. -/
def OscillatorParameters.level {ell : ℕ} (O : OscillatorParameters ell) (n : Fin ell → ℕ) : ℝ≥0 :=
  ∑ i, O.quantum i * ((n i : ℝ≥0) + 1 / 2)

/-- PDF p.9: maximal dense domain of the self-adjoint diagonal Hamiltonian. -/
def OscillatorParameters.domain {ell : ℕ} (O : OscillatorParameters ell) : Set (Hilbert (Fin ell → ℕ)) :=
  {u | Memℓp (fun n => (O.level n : ℂ) * u n) 2}

/-- PDF p.9: the Hamiltonian acts by its number-basis eigenvalues. -/
def OscillatorParameters.apply {ell : ℕ} (O : OscillatorParameters ell) (u : O.domain) :
    Hilbert (Fin ell → ℕ) :=
  ⟨fun n => (O.level n : ℂ) * u.val n, u.property⟩

/-- PDF p.9: E0=(1/2) sum_i hbar omega_i. -/
def OscillatorParameters.ground {ell : ℕ} (O : OscillatorParameters ell) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (O.quantum i : ℝ)

/-- PDF p.9, (23): geometric mean of the mode energy quanta. -/
def OscillatorParameters.geometricMean {ell : ℕ} (O : OscillatorParameters ell) : ℝ :=
  (∏ i, (O.quantum i : ℝ)) ^ (1 / (ell : ℝ))

/-- PDF pp.5,9: extended mean energy on positive trace-class arrays.
The nonnegative series equals the increasing spectral-cutoff supremum. -/
def OscillatorParameters.meanEnergy {ell : ℕ} (O : OscillatorParameters ell)
    (X : Matrix (Fin ell → ℕ) (Fin ell → ℕ) ℂ) : ℝ≥0∞ :=
  coefficientEnergy O.level X

/-- PDF pp.7,9, (18): supremum of actual entropies over the energy ball. -/
def OscillatorParameters.entropyMaximum {ell : ℕ} (O : OscillatorParameters ell) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State (Fin ell → ℕ) //
    O.meanEnergy rho.coefficients ≤ ENNReal.ofReal E}, extendedEntropyNats rho.val.coefficients

/-- PDF p.9, (23): explicit oscillator entropy majorant. -/
def OscillatorParameters.entropyUpper {ell : ℕ} (O : OscillatorParameters ell) (E : ℝ) : ℝ :=
  (ell : ℝ) * Real.log ((E + O.ground) / ((ell : ℝ) * O.geometricMean)) + ell

/-- PDF p.9: all admissible allocations, with equality of total energy. -/
def OscillatorParameters.allocations {ell : ℕ} (O : OscillatorParameters ell) (E : ℝ) : Set (Fin ell → ℝ) :=
  {e | (∑ i, e i) = E ∧ ∀ i, (O.quantum i : ℝ) / 2 ≤ e i}

/-- PDF p.9: sum of single-mode entropies for a fixed allocation. -/
def OscillatorParameters.allocationEntropy {ell : ℕ} (O : OscillatorParameters ell) (e : Fin ell → ℝ) : ℝ :=
  ∑ i, g (e i / (O.quantum i : ℝ) - 1 / 2)

example {ell : ℕ} (O : OscillatorParameters ell) (u : O.domain) (n : Fin ell → ℕ) :
    O.apply u n = (O.level n : ℂ) * u.val n := rfl

example {ell : ℕ} (O : OscillatorParameters ell) :
    O.meanEnergy (0 : Matrix (Fin ell → ℕ) (Fin ell → ℕ) ℂ) = 0 := by
  simp [OscillatorParameters.meanEnergy, coefficientEnergy]

example {ell : ℕ} (O : OscillatorParameters ell) (e : Fin ell → ℝ) (E : ℝ) :
    e ∈ O.allocations E ↔ (∑ i, e i) = E ∧ ∀ i, (O.quantum i : ℝ) / 2 ≤ e i := Iff.rfl

/-- PDF pp.7--9: the four state-independent nonnegative constants (16),(17). -/
structure AFWConstants where
  a : ℝ≥0
  b : ℝ≥0
  cMinus : ℝ≥0
  cPlus : ℝ≥0

/-- PDF p.9: finite energy of the actual oscillator marginal; R is arbitrary. -/
def OscillatorParameters.finiteMarginalEnergy {ell : ℕ} {R : Type} (O : OscillatorParameters ell)
    (rho : State ((Fin ell → ℕ) × R)) : Prop :=
  O.meanEnergy (traceSecond rho.coefficients) < ⊤

/-- PDF pp.7,9: both inequalities (16),(17), exactly on finite-energy states.
f accepts coefficient arrays, with values outside the source domain unconstrained.
Actual matrix mixtures are used; normalization is not an additional premise. -/
def OscillatorParameters.EntropyControlled {ell : ℕ} {R : Type} (O : OscillatorParameters ell)
    (C : AFWConstants) (f : Matrix ((Fin ell → ℕ) × R) ((Fin ell → ℕ) × R) ℂ → ℝ) : Prop :=
  (∀ rho sigma : State ((Fin ell → ℕ) × R),
    O.finiteMarginalEnergy rho → O.finiteMarginalEnergy sigma →
    ∀ p : ℝ, 0 < p → p < 1 →
      -(C.a : ℝ) * Real.binEntropy p ≤
        f (convexOperatorMixture p rho.coefficients sigma.coefficients) -
          p * f rho.coefficients - (1 - p) * f sigma.coefficients ∧
      f (convexOperatorMixture p rho.coefficients sigma.coefficients) -
          p * f rho.coefficients - (1 - p) * f sigma.coefficients ≤
        (C.b : ℝ) * Real.binEntropy p) ∧
  (∀ rho : State ((Fin ell → ℕ) × R), O.finiteMarginalEnergy rho →
    -(((C.cMinus : ℝ≥0∞) * extendedEntropyNats (traceSecond rho.coefficients)).toEReal) ≤
        (f rho.coefficients : EReal) ∧
      (f rho.coefficients : EReal) ≤
        ((C.cPlus : ℝ≥0∞) * extendedEntropyNats (traceSecond rho.coefficients)).toEReal)

/-- PDF p.9, (24): ell and the logarithm are OUTSIDE sqrt(2 epsilon). -/
def OscillatorParameters.continuityBound {ell : ℕ} (O : OscillatorParameters ell)
    (C : AFWConstants) (E eps : ℝ) : ℝ :=
  ((C.cMinus : ℝ) + C.cPlus) * Real.sqrt (2 * eps) *
    (ell : ℝ) * (Real.log ((E / eps + O.ground) /
      ((ell : ℝ) * O.geometricMean)) + 1) +
    ((C.a : ℝ) + C.b) * g (Real.sqrt (2 * eps))

/-- PDF pp.5,9: normalized-state adapter to the imported full trace distance.
The frozen QAlgorithms.traceDistance requires finite matrices and returns a real;
the imported extendedHalfTraceDistance covers arbitrary nuclear coefficients. -/
def nuclearStateDistance {I : Type} (rho sigma : State I) : ℝ≥0∞ :=
  extendedHalfTraceDistance rho.coefficients sigma.coefficients

example {I : Type} (rho sigma : State I) : nuclearStateDistance rho sigma =
    traceSize (rho.coefficients - sigma.coefficients) / 2 := rfl

example : (AFWConstants.mk 0 0 0 0).a = 0 := rfl

/-- PDF pp.9--10: complete basis for a selected multipartite subsystem. -/
abbrev SubsystemBasis {n : ℕ} (I : Fin n → Type) (S : Finset (Fin n)) :=
  (i : {i : Fin n // i ∈ S}) → I i.val

/-- PDF pp.9--10: complete basis for the complementary subsystem. -/
abbrev ComplementBasis {n : ℕ} (I : Fin n → Type) (S : Finset (Fin n)) :=
  (i : {i : Fin n // i ∉ S}) → I i.val

/-- PDF pp.9--10: full basis coordinate reconstructed from its two factors. -/
def joinBasis {n : ℕ} {I : Fin n → Type} {S : Finset (Fin n)}
    (x : SubsystemBasis I S) (r : ComplementBasis I S) : (i : Fin n) → I i :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else r ⟨i, h⟩

/-- PDF p.10: actual subsystem marginal, using the accepted completed partial trace. -/
def subsystemMarginal {n : ℕ} {I : Fin n → Type} (S : Finset (Fin n))
    (X : Matrix ((i : Fin n) → I i) ((i : Fin n) → I i) ℂ) :
    Matrix (SubsystemBasis I S) (SubsystemBasis I S) ℂ :=
  traceSecond (fun a b : SubsystemBasis I S × ComplementBasis I S =>
    X (joinBasis a.1 a.2) (joinBasis b.1 b.2))

/-- PDF pp.9--10, (25): the prescribed finite real combination, on its domain
of finite marginal entropies with nonzero coefficients. No infinite value is projected in the theorem. -/
def entropyCombination {n m : ℕ} {I : Fin n → Type}
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℝ)
    (X : Matrix ((i : Fin n) → I i) ((i : Fin n) → I i) ℂ) : ℝ :=
  ∑ k, c k * (extendedEntropyNats (subsystemMarginal (S k) X)).toReal

example {n : ℕ} {I : Fin n → Type} (S : Fin 0 → Finset (Fin n))
    (c : Fin 0 → ℝ) (X : Matrix ((i : Fin n) → I i) ((i : Fin n) → I i) ℂ) :
    entropyCombination S c X = 0 := by simp [entropyCombination]

example {n : ℕ} {I : Fin n → Type} {S : Finset (Fin n)}
    (x : SubsystemBasis I S) (r : ComplementBasis I S)
    (i : Fin n) (h : i ∈ S) : joinBasis x r i = x ⟨i, h⟩ := by
  simp [joinBasis, h]

/-- PDF p.5: infimum of the unit-vector energies, in a complete eigenbasis. -/
def spectralGround {I : Type} (energy : I → ℝ≥0) : ℝ :=
  sInf (Set.range (fun i => (energy i : ℝ)))

/-- PDF p.8, (22): extended partition trace and a right-hand limit.
Neither summability nor finite entropy is assumed separately. -/
def Condition22 {I : Type} (energy : I → ℝ≥0) : Prop :=
  Tendsto (fun lambda : ℝ =>
    (∑' i, ENNReal.ofReal (Real.exp (-lambda * (energy i : ℝ)))) ^ lambda)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ≥0∞))

/-- Trace-distance uniform continuity on a specified state set (PDF pp.5,17--18).
This epsilon-delta definition avoids imposing a coefficient uniformity. -/
def TraceUniformContinuousOn {I : Type} (A : Set (State I)) (f : State I → ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
    ∀ rho ∈ A, ∀ sigma ∈ A, nuclearStateDistance rho sigma < ENNReal.ofReal delta →
      |f rho - f sigma| < eta

/-- PDF p.4: genuine mutual information of a joint state, defined by relative entropy. -/
def marginalMutualInformation {I J : Type}
    (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  extendedRelativeEntropyNats X
    (QAlgorithms.Papers.Independent.Dependency50.P33.productCoeff
      (traceSecond X) (QAlgorithms.Papers.Independent.Frontier18.P01.traceFirst X))

/-- PDF p.11, (28): finite-A-entropy conditional entropy, without infinity subtraction. -/
def extendedConditionalEntropy {I J : Type}
    (X : Matrix (I × J) (I × J) ℂ) : ℝ :=
  (extendedEntropyNats (traceSecond X)).toReal - (marginalMutualInformation X).toReal

/-- PDF p.17, (48): mutual information after the actual reference-amplified channel. -/
def outputMutualInformation {I J R : Type}
    (Phi : QAlgorithms.Papers.Independent.Frontier18.P01.Channel I J)
    (X : Matrix (I × R) (I × R) ℂ) : ℝ≥0∞ :=
  marginalMutualInformation
    (QAlgorithms.Papers.Independent.Dependency50.P33.tensorApply Phi.val X)

/-- PDF p.8, (21): the real modulus, used only with proved finite F_H. -/
def entropyModulus (F : ℝ → ℝ≥0∞) (C D E eps : ℝ) : ℝ :=
  C * Real.sqrt (2 * eps) * (F (E / eps)).toReal + D * g (Real.sqrt (2 * eps))

/-- PDF pp.17--18: finite-valued uniform continuity and the quantitative bound,
on one FIXED energy ball. This is a conclusion package, never a hypothesis. -/
def EnergyContinuity {I : Type} (energyOn : Matrix I I ℂ → ℝ≥0∞)
    (f : Matrix I I ℂ → ℝ≥0∞) (E : ℝ) (bound : ℝ → ℝ) : Prop :=
  (∀ rho : State I, energyOn rho.coefficients ≤ ENNReal.ofReal E → f rho.coefficients < ⊤) ∧
  TraceUniformContinuousOn {rho | energyOn rho.coefficients ≤ ENNReal.ofReal E}
    (fun rho => (f rho.coefficients).toReal) ∧
  ∀ (rho sigma : State I) (eps : ℝ),
    energyOn rho.coefficients ≤ ENNReal.ofReal E →
    energyOn sigma.coefficients ≤ ENNReal.ofReal E →
    0 < eps → eps ≤ 1 / 2 → nuclearStateDistance rho sigma ≤ ENNReal.ofReal eps →
      |(f rho.coefficients).toReal - (f sigma.coefficients).toReal| ≤ bound eps

example {I : Type} (energy : I → ℝ≥0) :
    coefficientEnergy energy (0 : Matrix I I ℂ) = 0 := by simp [coefficientEnergy]

example {I : Type} (f : State I → ℝ) : TraceUniformContinuousOn ∅ f := by
  intro eta heta
  exact ⟨1, by norm_num, by simp⟩

example {I : Type} (energy : I → ℝ≥0) (E : ℝ) : entropySupremum energy E =
    ⨆ rho : {rho : State I // coefficientEnergy energy rho.coefficients ≤ ENNReal.ofReal E},
      extendedEntropyNats rho.val.coefficients := rfl

/-- PDF p.14, (38): relative entropy distance to the actual trace-norm closed
convex hull of product states. Empty infima retain infinity. The frozen P54
relativeEntanglement is finite-dimensional and in bits; this interface is in nats
on arbitrary countable systems and cannot use that finite-dimensional function. -/
def countableRelativeEntanglementNats {I J : Type}
    (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  ⨅ omega : {omega : State (I × J) //
    QAlgorithms.Papers.Independent.Dependency50.P33.IsSeparable omega.coefficients},
    extendedRelativeEntropyNats X omega.val.coefficients

/-- PDF pp.14,16: n copies, regrouped as A^n:B^n, without restricting other
states of that tensor-power system to be products. -/
def bipartiteTensorPower {I J : Type} (n : ℕ)
    (X : Matrix (I × J) (I × J) ℂ) :
    Matrix ((Fin n → I) × (Fin n → J)) ((Fin n → I) × (Fin n → J)) ℂ :=
  fun a b => ∏ k, X (a.1 k, a.2 k) (b.1 k, b.2 k)

/-- PDF p.14, (39): regularization as the extended infimum of ER(rho^n)/n,
equivalent to the actual limit by subadditivity. Only positive block lengths
are used; a divergent value remains infinity. The frozen P54 regularization
is finite-dimensional and in bits, so it does not represent this domain. -/
def regularizedCountableEntanglementNats {I J : Type}
    (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  ⨅ n : ℕ, countableRelativeEntanglementNats (bipartiteTensorPower (n + 1) X) / (n + 1 : ℝ≥0∞)

/-- PDF p.16: additive tensor-power Hamiltonian eigenvalues. -/
def additiveEnergy {I : Type} (energy : I → ℝ≥0) (n : ℕ) (a : Fin n → I) : ℝ≥0 :=
  ∑ k, energy (a k)

example {I J : Type} (X : Matrix (I × J) (I × J) ℂ)
    (a b : (Fin 0 → I) × (Fin 0 → J)) : bipartiteTensorPower 0 X a b = 1 := by
  simp [bipartiteTensorPower]

example {I : Type} (energy : I → ℝ≥0) (a : Fin 0 → I) : additiveEnergy energy 0 a = 0 := by
  simp [additiveEnergy]

end QAlgorithms.Papers.Independent.Support50.P18


