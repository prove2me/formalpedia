-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
-- name    : QAlgorithms_Papers_Independent_Frontier30_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:13:01.283302+00:00
-- url     : https://prove2.me/theorems/77187b9a-94a1-4a04-bdcd-eb70f4971d69
-- title:
--   Definitions for Gaussian Quantum Information
-- statement:
--   The objects the formalized statements of *Gaussian Quantum Information* (arXiv:1110.3234) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QuadratureIndex`: PDF p.5, Eq.(5): a mode followed by its q/p coordinate, in that order. The frozen Dependency50.P10.Phase uses grouped Q/P coordinates instead.
--   - `interleavedSymplecticForm`: PDF p.5, Eq.(2): direct sum of [[0,1],[-1,0]] in interleaved order. Frozen declarations named omega describe other objects, not this symplectic form.
--   - `quantumCovariance`: PDF p.6, Eq.(17): the plus-i uncertainty inequality. PosSemidef includes Hermiticity, hence this predicate also imposes real symmetry of V.
--   - `isSymplectic`: PDF p.6, Eq.(24): symplecticity in the source's coordinates.
--   - `williamsonDiagonal`: PDF p.9, Eq.(44): each positive Williamson parameter occurs twice.
--   - `twoModeDelta`: PDF p.10, Eqs.(53)–(54): the determinant invariant of the two-mode blocks.
--   - `twoModeSpectrum`: PDF p.10, Eq.(54): the smaller, then the larger, nonnegative square root. The theorem below supplies all radicand and positivity guards.
--   - `HasCoherentCoefficients`: PDF p.7, Eq.(29): identifies the actual l2 vector, not a formal power series.
--   - `annihilationSequence`: PDF p.5, Eq.(3): annihilation as a sequence. Square-summability of relevant quadrature actions is imposed separately, rather than declaring this unbounded map bounded.
--   - `creationSequence`: PDF p.5, Eq.(4): creation on Fock coordinates, with the vacuum boundary explicit.
--   - `quadratureSequence`: PDF p.5, Eq.(6): actual quadrature actions q=a+a^dagger and p=i(a^dagger-a), with hbar=2, as possibly non-l2 sequences.
--   - `finitePureQuadratures`: PDF pp.5–6, Eqs.(14)–(15): the finite second-moment (quadratic-form) domain for a pure state. This guard prevents use of divergent totalized series.
--   - `pureMean`: PDF p.5, Eq.(14): real first observable moments on the finite form domain.
--   - `pureQuadratureCovariance`: PDF p.6, Eq.(15): the real part of the quadrature form is the symmetrized second moment. Subtraction of the actual means centers it. Used only for norm-one vectors in finitePureQuadratures. This observable covariance is distinct from Dependency50.P10.pureCovariance, a matrix purity predicate.
-- source:
--   Gaussian Quantum Information, arXiv:1110.3234v1, https://arxiv.org/abs/1110.3234v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Statements from Weedbrook et al., arXiv:1110.3234v1.
The phase-space coordinates are interleaved (q1,p1,...,qN,pN), hbar = 2.
The oscillator space is the full countable l2 space. Entropies are in nats.
Only selected complete results are stated; the unit HARD.md and GAPS.json
account for every remaining planned node. No covariance tuple is called a state.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P08

open scoped BigOperators ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

/-- PDF p.5, Eq.(5): a mode followed by its q/p coordinate, in that order.
The frozen Dependency50.P10.Phase uses grouped Q/P coordinates instead. -/
abbrev QuadratureIndex (n : ℕ) := Fin n × Fin 2

/-- PDF p.5, Eq.(2): direct sum of [[0,1],[-1,0]] in interleaved order.
Frozen declarations named omega describe other objects, not this symplectic form. -/
def interleavedSymplecticForm (n : ℕ) : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ :=
  fun i j => if i.1 = j.1 then
    (if i.2 = j.2 then 0 else if i.2 = 0 then 1 else -1) else 0

/-- PDF p.6, Eq.(17): the plus-i uncertainty inequality. PosSemidef includes
Hermiticity, hence this predicate also imposes real symmetry of V. -/
def quantumCovariance {n : ℕ} (V : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) : Prop :=
  (V.map (fun x : ℝ => (x : ℂ)) +
    Complex.I • (interleavedSymplecticForm n).map (fun x : ℝ => (x : ℂ))).PosSemidef

/-- PDF p.6, Eq.(24): symplecticity in the source's coordinates. -/
def isSymplectic {n : ℕ} (S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) : Prop :=
  S * interleavedSymplecticForm n * S.transpose = interleavedSymplecticForm n

/-- PDF p.9, Eq.(44): each positive Williamson parameter occurs twice. -/
def williamsonDiagonal {n : ℕ} (nu : Fin n → ℝ) :
    Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ :=
  Matrix.diagonal (fun i => nu i.1)

/-- PDF p.10, Eqs.(53)–(54): the determinant invariant of the two-mode blocks. -/
def twoModeDelta (V : Matrix (QuadratureIndex 2) (QuadratureIndex 2) ℝ) : ℝ :=
  (V.submatrix (fun i : Fin 2 => ((0 : Fin 2), i))
    (fun j : Fin 2 => ((0 : Fin 2), j))).det +
  (V.submatrix (fun i : Fin 2 => ((1 : Fin 2), i))
    (fun j : Fin 2 => ((1 : Fin 2), j))).det +
  2 * (V.submatrix (fun i : Fin 2 => ((0 : Fin 2), i))
    (fun j : Fin 2 => ((1 : Fin 2), j))).det

/-- PDF p.10, Eq.(54): the smaller, then the larger, nonnegative square root.
The theorem below supplies all radicand and positivity guards. -/
def twoModeSpectrum (V : Matrix (QuadratureIndex 2) (QuadratureIndex 2) ℝ) (k : Fin 2) : ℝ :=
  Real.sqrt ((twoModeDelta V + (if k = 0 then -1 else 1) *
    Real.sqrt ((twoModeDelta V) ^ 2 - 4 * V.det)) / 2)

example : interleavedSymplecticForm 1 ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (1 : Fin 2)) = 1 := by
  norm_num [interleavedSymplecticForm]

example : interleavedSymplecticForm 1 ((0 : Fin 1), (1 : Fin 2)) ((0 : Fin 1), (0 : Fin 2)) = -1 := by
  norm_num [interleavedSymplecticForm]

example (n : ℕ) : williamsonDiagonal (fun _ : Fin n => (1 : ℝ)) = 1 := by
  ext i j
  simp [williamsonDiagonal, Matrix.diagonal, Matrix.one_apply]

/-- PDF p.7, Eq.(29): identifies the actual l2 vector, not a formal power series. -/
def HasCoherentCoefficients (alpha : ℂ) (psi : Fock) : Prop :=
  ∀ n, psi n = coherentCoefficient alpha n

/-- PDF p.5, Eq.(3): annihilation as a sequence. Square-summability of relevant
quadrature actions is imposed separately, rather than declaring this unbounded map bounded. -/
def annihilationSequence (psi : Fock) (n : ℕ) : ℂ :=
  (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * psi (n + 1)

/-- PDF p.5, Eq.(4): creation on Fock coordinates, with the vacuum boundary explicit. -/
def creationSequence (psi : Fock) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (Real.sqrt (n : ℝ) : ℂ) * psi (n - 1)

/-- PDF p.5, Eq.(6): actual quadrature actions q=a+a^dagger and
p=i(a^dagger-a), with hbar=2, as possibly non-l2 sequences. -/
def quadratureSequence (k : Fin 2) (psi : Fock) (n : ℕ) : ℂ :=
  if k = 0 then annihilationSequence psi n + creationSequence psi n
  else Complex.I * (creationSequence psi n - annihilationSequence psi n)

/-- PDF pp.5–6, Eqs.(14)–(15): the finite second-moment (quadratic-form)
domain for a pure state. This guard prevents use of divergent totalized series. -/
def finitePureQuadratures (psi : Fock) : Prop :=
  ∀ k : Fin 2, Summable (fun n : ℕ => ‖quadratureSequence k psi n‖ ^ 2)

/-- PDF p.5, Eq.(14): real first observable moments on the finite form domain. -/
def pureMean (psi : Fock) (k : Fin 2) : ℝ :=
  (∑' n : ℕ, star (psi n) * quadratureSequence k psi n).re

/-- PDF p.6, Eq.(15): the real part of the quadrature form is the
symmetrized second moment. Subtraction of the actual means centers it.
Used only for norm-one vectors in finitePureQuadratures. This observable covariance
is distinct from Dependency50.P10.pureCovariance, a matrix purity predicate. -/
def pureQuadratureCovariance (psi : Fock) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    (∑' n : ℕ, star (quadratureSequence i psi n) * quadratureSequence j psi n).re -
      pureMean psi i * pureMean psi j

example : coherentCoefficient 0 0 = 1 := by
  norm_num [coherentCoefficient]

example (psi : Fock) : creationSequence psi 0 = 0 := by
  simp [creationSequence]

example : quadratureSequence 0 (lp.single 2 0 (1 : ℂ)) 1 = 1 := by
  norm_num [quadratureSequence, annihilationSequence, creationSequence, lp.single_apply]

example : quadratureSequence 1 (lp.single 2 0 (1 : ℂ)) 1 = Complex.I := by
  norm_num [quadratureSequence, annihilationSequence, creationSequence, lp.single_apply]

end QAlgorithms.Papers.Independent.Frontier30.P08


