-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07
-- name    : QAlgorithms_Papers_Independent_Claimed50_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:08:41.191046+00:00
-- url     : https://prove2.me/theorems/ecf80581-a59d-4698-984b-fb8a28d05ab2
-- title:
--   Definitions for Uniform finite-dimensional approximation of basic capacities of energy-constrained channels
-- statement:
--   The objects the formalized statements of *Uniform finite-dimensional approximation of basic capacities of energy-constrained channels* (arXiv:1707.05641) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `boundedCoefficients`: PDF p.16, Lemma 4: coefficients of an ACTUAL bounded operator on l2(I). The countable basis labels used below cover every separable system.
--   - `weightedTrace`: PDF p.16: trace of K X, used for bounded K and trace-class X only. The inner sum is an l2 pairing and the outer diagonal sum is the trace-class trace, so neither series uses the default of a divergent real sum.
--   - `projectionReplacement`: Lemma 4, PDF p.16: Pi(X)=P X P+Tr((1-P)X) tau on the entire trace class. P is self-adjoint and idempotent in the theorem. No support restriction is imposed on tau. The action on arrays outside trace class is unused.
--   - `truncationTail`: Lemma 5, PDF p.16: Tr((I-P_m)rho) in the ordered Hamiltonian eigenbasis. On normalized positive trace-class states the nonnegative diagonal series is summable with sum one; this real subseries is always finite. Index m is the FIRST excluded eigenvector, not the last retained eigenvector.
--   - `oscillatorGround`: Equation (24), PDF p.9: oscillator ground energy, including zero-point energy.
--   - `oscillatorGeometricMean`: Equation (24), PDF p.9: geometric mean of the positive mode energy scales.
--   - `oscillatorLevels`: PDF pp.9,20: full Fock spectrum; source n_i>=1 becomes occupation n_i-1>=0. Positivity of hbar and omega makes the ofReal conversion exact.
--   - `oscillatorEntropyBounded`: Equation (24), PDF p.9: actual entropy supremum over ALL normalized states on the full multimode Hilbert space, not over diagonal states or finite cutoffs. Both entropy and energy retain infinity. Negative budgets are unused.
--   - `oscillatorEnvelope`: Equation (24), PDF p.9: the literal ratio (E+E0)/(ell E_star), in nats.
-- source:
--   Uniform finite-dimensional approximation of basic capacities of energy-constrained channels, arXiv:1707.05641v2, https://arxiv.org/abs/1707.05641v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

/-!
Statements from Shirokov, arXiv:1707.05641v2, PDF pp.9,16.
The independent-paper override permits imports of these pinned accepted modules.
Trace-class states, full CPTP coefficient maps, nuclear trace norm, spectral
entropy in nats, and complete ordered energy spectra are reused unchanged.
All new definitions belong to this paper. Deferred nodes are listed in HARD.md
and GAPS.json, including the full capacity theorems and extended-QCMI lemmas.
Compilation is explicitly pending the batch handoff.
-/

noncomputable section

open Filter
open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P07

namespace TC

export QAlgorithms.Papers.Independent.Dependency50.P13
  (State stateEntropy spectralEnergy)

end TC

namespace Coeff

export QAlgorithms.Papers.Independent.Dependency50.P33
  (State tensorApply traceSize)

export QAlgorithms.Papers.Independent.Frontier30.P14
  (conjugateKernel partialRight)

end Coeff

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

/-- PDF p.16, Lemma 4: coefficients of an ACTUAL bounded operator on l2(I).
The countable basis labels used below cover every separable system. -/
def boundedCoefficients {I : Type} (K : Hilbert I →L[ℂ] Hilbert I) : Matrix I I ℂ :=
  fun i j => K (lp.single 2 j 1) i

/-- PDF p.16: trace of K X, used for bounded K and trace-class X only.
The inner sum is an l2 pairing and the outer diagonal sum is the trace-class
trace, so neither series uses the default of a divergent real sum. -/
def weightedTrace {I : Type} (K : Hilbert I →L[ℂ] Hilbert I)
    (X : Matrix I I ℂ) : ℂ :=
  ∑' i, ∑' j, boundedCoefficients K i j * X j i

/-- Lemma 4, PDF p.16: Pi(X)=P X P+Tr((1-P)X) tau on the entire trace class.
P is self-adjoint and idempotent in the theorem. No support restriction is
imposed on tau. The action on arrays outside trace class is unused. -/
def projectionReplacement {I : Type} (P : Hilbert I →L[ℂ] Hilbert I)
    (tau : Coeff.State I) (X : Matrix I I ℂ) : Matrix I I ℂ :=
  Coeff.conjugateKernel (boundedCoefficients P) X +
    weightedTrace (1 - P) X • tau.coefficients

example {I : Type} (K : Hilbert I →L[ℂ] Hilbert I) :
    weightedTrace K (0 : Matrix I I ℂ) = 0 := by
  simp [weightedTrace]

example {I : Type} (P : Hilbert I →L[ℂ] Hilbert I) (tau : Coeff.State I) :
    projectionReplacement P tau (0 : Matrix I I ℂ) = 0 := by
  funext i j
  simp [projectionReplacement, Coeff.conjugateKernel, weightedTrace]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 5, PDF p.16: Tr((I-P_m)rho) in the ordered Hamiltonian eigenbasis.
On normalized positive trace-class states the nonnegative diagonal series is
summable with sum one; this real subseries is always finite. Index m is the
FIRST excluded eigenvector, not the last retained eigenvector. -/
def truncationTail (b : HilbertBasis ℕ ℂ H) (rho : TC.State b) (m : ℕ) : ℝ :=
  ∑' k : ℕ, if m ≤ k then (inner ℂ (b k) (rho.val.val (b k))).re else 0

example (b : HilbertBasis ℕ ℂ H) (rho : TC.State b) (m : ℕ)
    (hsupport : ∀ k : ℕ, m ≤ k → (inner ℂ (b k) (rho.val.val (b k))).re = 0) :
    truncationTail b rho m = 0 := by
  unfold truncationTail
  have hzero : ∀ k : ℕ,
      (if m ≤ k then (inner ℂ (b k) (rho.val.val (b k))).re else 0) = 0 := by
    intro k
    split_ifs with hk
    · exact hsupport k hk
    · rfl
  simp only [hzero, tsum_zero]

/-- Equation (24), PDF p.9: oscillator ground energy, including zero-point energy. -/
def oscillatorGround {ell : ℕ} (hbar : ℝ) (omega : Fin ell → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, hbar * omega i

/-- Equation (24), PDF p.9: geometric mean of the positive mode energy scales. -/
def oscillatorGeometricMean {ell : ℕ} (hbar : ℝ) (omega : Fin ell → ℝ) : ℝ :=
  (∏ i, hbar * omega i) ^ (1 / (ell : ℝ))

/-- PDF pp.9,20: full Fock spectrum; source n_i>=1 becomes occupation n_i-1>=0.
Positivity of hbar and omega makes the ofReal conversion exact. -/
def oscillatorLevels {ell : ℕ} (hbar : ℝ) (omega : Fin ell → ℝ)
    (n : Fin ell → ℕ) : ℝ≥0 :=
  Real.toNNReal (∑ i, hbar * omega i * ((n i : ℝ) + 1 / 2))

/-- Equation (24), PDF p.9: actual entropy supremum over ALL normalized states
on the full multimode Hilbert space, not over diagonal states or finite cutoffs.
Both entropy and energy retain infinity. Negative budgets are unused. -/
def oscillatorEntropyBounded {ell : ℕ} (b : HilbertBasis (Fin ell → ℕ) ℂ H)
    (hbar : ℝ) (omega : Fin ell → ℝ) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : TC.State b //
      TC.spectralEnergy b (oscillatorLevels hbar omega) rho ≤ ENNReal.ofReal E},
    TC.stateEntropy b rho.val

/-- Equation (24), PDF p.9: the literal ratio (E+E0)/(ell E_star), in nats. -/
def oscillatorEnvelope {ell : ℕ} (hbar : ℝ) (omega : Fin ell → ℝ) (E : ℝ) : ℝ :=
  (ell : ℝ) * Real.log
    ((E + oscillatorGround hbar omega) / ((ell : ℝ) * oscillatorGeometricMean hbar omega)) +
      (ell : ℝ)

example (hbar : ℝ) (omega : Fin 1 → ℝ) :
    oscillatorGround hbar omega = (1 / 2 : ℝ) * (hbar * omega 0) := by
  simp [oscillatorGround]

example (hbar : ℝ) (omega : Fin 1 → ℝ) :
    oscillatorLevels hbar omega (fun _ => 0) =
      Real.toNNReal (hbar * omega 0 * (1 / 2)) := by
  simp [oscillatorLevels]

end QAlgorithms.Papers.Independent.Claimed50.P07


