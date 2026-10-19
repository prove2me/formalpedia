-- Prove2me | Definitions.Def_QAlgorithms_Defs_TwoBasisCertification
-- name    : QAlgorithms_Defs_TwoBasisCertification
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:04.945794+00:00
-- url     : https://prove2.me/theorems/7730050b-46e4-42c6-b13a-c40cab62fac5
-- title:
--   TwoBasisCertification
-- statement:
--   TwoBasisCertification
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TwoBasisCertification.lean

import Definitions.Def_QAlgorithms_Defs_HaarTargetStates
import Definitions.Def_QAlgorithms_Defs_ComplexAmplitudePrograms
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
noncomputable section

open scoped Matrix

namespace QAlgorithms.TwoBasisCertification

variable {n m d k b w M K N c out : ℕ}

/-- Logarithmic fixed suffix schedule with gamma=1, rounding and cap:
2602.11616 pp.3,8–9. n=0 gives an empty prefix and suffix. -/
def suffixSize (n : ℕ) : ℕ :=
  min n ⌈2 * Real.logb 2 (max (2 : ℝ) n)⌉₊

/-- Physical conditional target on the suffix, 2602.11616 pp.8–10.
The full-Hadamard amplitude answer fiber is corrected by H^⊗k.
The vector is subnormalized and a zero fiber stays zero. -/
def conditionalTarget (r k : ℕ) (psi : EuclideanSpace ℂ (Qubits (r+k)))
    (had : Bool) (z : Qubits r) : EuclideanSpace ℂ (Qubits k) :=
  let fiber : EuclideanSpace ℂ (Qubits k) :=
    WithLp.toLp 2 fun w => amplitudeOracle psi had (Fin.append z w)
  if had then act (hadamardN k) fiber else fiber

/-- Conditional accepting projector, 2602.11616 pp.8–10.
Normalized nonzero fibers give rank one; zero fibers give zero acceptance. -/
def conditionalProjector (r k : ℕ) (psi : EuclideanSpace ℂ (Qubits (r+k)))
    (had : Bool) (z : Qubits r) : Matrix (Qubits k) (Qubits k) ℂ :=
  pureDensity (normalizedVec (conditionalTarget r k psi had z))

/-- Exact accepting effect of the fair two-basis prefix/suffix test,
2602.11616 p.9. The suffix measurement is one projector/complement
measurement after the r prefix measurements. -/
def test (r k : ℕ) (psi : EuclideanSpace ℂ (Qubits (r+k))) :
    Matrix (Qubits (r+k)) (Qubits (r+k)) ℂ :=
  (((1/2 : ℂ) • (∑ z : Qubits r,
    Matrix.kronecker (pureDensity (ket z)) (conditionalProjector r k psi false z)) +
    (1/2 : ℂ) • (∑ z : Qubits r,
      Matrix.kronecker (pureDensity (act (hadamardN r) (ket z)))
        (conditionalProjector r k psi true z))).submatrix
      (qubitsAppendEquiv r k) (qubitsAppendEquiv r k))

/-- Actual sequential law, 2602.11616 pp.8–10.
Apply the chosen prefix basis change, retain each subnormalized suffix
block, then measure the conditional projector/complement. No lab branch
normalization or division is performed. -/
def outcomeLaw (r k : ℕ) (psi : EuclideanSpace ℂ (Qubits (r+k)))
    (rho : Matrix (Qubits (r+k)) (Qubits (r+k)) ℂ) (accept : Bool) : ℝ :=
  (1/2 : ℝ) * ∑ had : Bool,
    let X := rho.submatrix (qubitsAppendEquiv r k).symm (qubitsAppendEquiv r k).symm
    let basis := if had then Matrix.kronecker (hadamardN r) (1 : Matrix (Qubits k) (Qubits k) ℂ)
      else 1
    let rotated := conjSuperop basis X
    ∑ z : Qubits r,
      let block := Matrix.of fun w v => rotated (z,w) (z,v)
      let Pi := compiledSuffixEffect r k had z (amplitudeOracle psi)
      effectProb (if accept then Pi else 1-Pi) block

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,5,8,9,10). -/
example : suffixSize 0 = 0 := by simp [suffixSize]

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,5,8,9,10). -/
example (r k : ℕ) (had : Bool) (z : Qubits r) :
    conditionalProjector r k 0 had z = 0 := by
  have h0 : conditionalTarget r k 0 had z = 0 := by
    cases had
    · rfl
    · unfold conditionalTarget amplitudeOracle
      simp only [Bool.false_eq_true, if_false, if_true]
      have hh : act (hadamardN (r+k)) (0 : EuclideanSpace ℂ (Qubits (r+k))) = 0 := by
        simp [act]
      rw [hh]
      change act (hadamardN k) 0 = 0
      simp [act]
  rw [conditionalProjector,h0]
  ext a b
  simp [normalizedVec,pureDensity]

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.3,5,8,9,10). -/
example (r k : ℕ) (psi : EuclideanSpace ℂ (Qubits (r+k))) (accept : Bool) :
    outcomeLaw r k psi 0 accept = 0 := by
  cases accept <;>
    simp [outcomeLaw, conjSuperop, effectProb, Matrix.trace, Matrix.mul_apply]

end QAlgorithms.TwoBasisCertification


