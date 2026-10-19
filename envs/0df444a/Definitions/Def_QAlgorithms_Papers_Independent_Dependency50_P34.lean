-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34
-- name    : QAlgorithms_Papers_Independent_Dependency50_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:21:26.324557+00:00
-- url     : https://prove2.me/theorems/c86ba756-f71d-4b1b-b169-221d7b7cd206
-- title:
--   Definitions for Quantum Interference between a Single-Photon Fock State and a Coherent State
-- statement:
--   The objects the formalized statements of *Quantum Interference between a Single-Photon Fock State and a Coherent State* (arXiv:1009.1844) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `beamMatrix`: PDF p.3, Eq.(1): output order (2,3), input order (0,1). For the second MZI splitter the arguments are (t2,r2Prime,r2,t2Prime), as drawn on PDF p.6, Eq.(21).
--   - `phaseMatrix`: PDF p.6, Eq.(20): the phase is inserted in the second path.
--   - `mziMatrix`: PDF p.6, Eq.(21): the geometrically oriented second splitter acts last.
--   - `balancedSplitter`: PDF p.7, §III/D: both splitters have transmission 1/sqrt(2) and reflection i/sqrt(2). Their geometric orientations agree in this symmetric case.
--   - `TwoModeFock`: PDF pp.3,8: the occupation basis uses first-output occupation followed by second-output occupation. Reuses the accepted general atomic lp space.
--   - `fockKet`: PDF pp.3,8: the normalized two-mode Fock ket |m,n> in l²(N x N).
--   - `fockOutput`: PDF p.3, Eq.(4), and p.8, comparison preceding Eq.(35): finite creation polynomial for the input |m,n>. Expand (B00*aFirst† + B10*aSecond†)^m (B01*aFirst† + B11*aSecond†)^n / sqrt(m! n!). The square-root factorial factor converts monomials to normalized Fock kets. The sums have k<=m and l<=n, so natural subtraction is exact in every term. Every term is an lp.single, hence square summability is carried by the type. This constructs each finite occupation output, without postulating an extension to infinite superpositions or assuming the answer to Eq.(35).
--   - `comparisonOutput`: PDF p.8, Eq.(35): actual balanced-MZI output of |1,1>, constructed from Eq.(21) and the two creation polynomials, before applying any simplification.
--   - `jointWeight`: PDF p.8, paragraph following Eq.(35): joint occupation Born weight. This is a probability when the vector has norm one, as asserted in the results.
--   - `portOccupation`: PDF pp.7–8: port index 0 means output 4 and index 1 means output 5.
--   - `marginalWeight`: PDF p.8: marginal probability for detecting n photons at the chosen port. The summands are nonnegative; the theorems assert normalization and summability on the vectors used, rather than interpreting default nonsummable real sums.
--   - `photonMean`: PDF p.7, Eq.(26), and p.8: occupation-sum photon mean. Summability is part of the statistics theorem's conclusion.
-- source:
--   Quantum Interference between a Single-Photon Fock State and a Coherent State, arXiv:1009.1844v2, https://arxiv.org/abs/1009.1844v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

/-!
# Quantum interference between a single-photon Fock state and a coherent state

arXiv:1009.1844v2. This module states the MZI scattering result and the
finite two-photon comparison. Infinite-dimensional coherent-state, marginal,
and Wigner results are explicitly deferred in the accompanying GAPS.json.
The finite occupation expansion below is not an isometry on arbitrary lp inputs.
-/

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Dependency50.P34

/-- PDF p.3, Eq.(1): output order (2,3), input order (0,1).
For the second MZI splitter the arguments are (t2,r2Prime,r2,t2Prime),
as drawn on PDF p.6, Eq.(21). -/
def beamMatrix (tPrime r rPrime t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![tPrime, r; rPrime, t]

/-- PDF p.6, Eq.(20): the phase is inserted in the second path. -/
def phaseMatrix (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Complex.I * (theta : ℂ))]

/-- PDF p.6, Eq.(21): the geometrically oriented second splitter acts last. -/
def mziMatrix (B1 B2 : Matrix (Fin 2) (Fin 2) ℂ) (theta : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  B2 * phaseMatrix theta * B1

/-- PDF p.7, §III/D: both splitters have transmission 1/sqrt(2)
and reflection i/sqrt(2). Their geometric orientations agree in this symmetric case. -/
def balancedSplitter : Matrix (Fin 2) (Fin 2) ℂ :=
  beamMatrix (1 / (Real.sqrt 2 : ℂ)) (Complex.I / (Real.sqrt 2 : ℂ))
    (Complex.I / (Real.sqrt 2 : ℂ)) (1 / (Real.sqrt 2 : ℂ))

/-- PDF pp.3,8: the occupation basis uses first-output occupation followed by
second-output occupation. Reuses the accepted general atomic lp space. -/
abbrev TwoModeFock := QAlgorithms.RealRegisters.Hilbert (ℕ × ℕ)

/-- PDF pp.3,8: the normalized two-mode Fock ket |m,n> in l²(N x N). -/
def fockKet (m n : ℕ) : TwoModeFock :=
  lp.single 2 (m, n) (1 : ℂ)

/-- PDF p.3, Eq.(4), and p.8, comparison preceding Eq.(35): finite creation
polynomial for the input |m,n>. Expand
(B00*aFirst† + B10*aSecond†)^m (B01*aFirst† + B11*aSecond†)^n / sqrt(m! n!).
The square-root factorial factor converts monomials to normalized Fock kets.
The sums have k<=m and l<=n, so natural subtraction is exact in every term.
Every term is an lp.single, hence square summability is carried by the type.
This constructs each finite occupation output, without postulating an extension
to infinite superpositions or assuming the answer to Eq.(35). -/
def fockOutput (B : Matrix (Fin 2) (Fin 2) ℂ) (m n : ℕ) : TwoModeFock :=
  ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (n + 1),
    ((m.choose k : ℂ) * (n.choose l : ℂ) *
      (Real.sqrt (((Nat.factorial (k + l) : ℝ) *
        (Nat.factorial (m - k + (n - l)) : ℝ)) /
        ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
      B 0 0 ^ k * B 1 0 ^ (m - k) * B 0 1 ^ l * B 1 1 ^ (n - l)) •
        fockKet (k + l) (m - k + (n - l))

/-- PDF p.8, Eq.(35): actual balanced-MZI output of |1,1>, constructed from
Eq.(21) and the two creation polynomials, before applying any simplification. -/
def comparisonOutput (theta : ℝ) : TwoModeFock :=
  fockOutput (mziMatrix balancedSplitter balancedSplitter theta) 1 1

/-- PDF p.8, paragraph following Eq.(35): joint occupation Born weight.
This is a probability when the vector has norm one, as asserted in the results. -/
def jointWeight (psi : TwoModeFock) (nm : ℕ × ℕ) : ℝ :=
  Complex.normSq (psi nm)

/-- PDF pp.7–8: port index 0 means output 4 and index 1 means output 5. -/
def portOccupation (j : Fin 2) (nm : ℕ × ℕ) : ℕ :=
  if j = 0 then nm.1 else nm.2

/-- PDF p.8: marginal probability for detecting n photons at the chosen port.
The summands are nonnegative; the theorems assert normalization and summability
on the vectors used, rather than interpreting default nonsummable real sums. -/
def marginalWeight (psi : TwoModeFock) (j : Fin 2) (n : ℕ) : ℝ :=
  ∑' nm : ℕ × ℕ, if portOccupation j nm = n then jointWeight psi nm else 0

/-- PDF p.7, Eq.(26), and p.8: occupation-sum photon mean.
Summability is part of the statistics theorem's conclusion. -/
def photonMean (psi : TwoModeFock) (j : Fin 2) : ℝ :=
  ∑' nm : ℕ × ℕ, (portOccupation j nm : ℝ) * jointWeight psi nm

example (tPrime r rPrime t : ℂ) : beamMatrix tPrime r rPrime t 0 1 = r := by
  rfl

example : phaseMatrix 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseMatrix]

example : balancedSplitter 0 0 = 1 / (Real.sqrt 2 : ℂ) := by
  rfl

example (m n : ℕ) : ‖fockKet m n‖ = 1 := by
  change ‖lp.single (E := fun _ : ℕ × ℕ => ℂ) 2 (m, n) (1 : ℂ)‖ = 1
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact norm_one

example (m n : ℕ) : fockKet m n (m, n) = 1 := by
  simp [fockKet]

example : fockKet 1 0 (0, 1) = 0 := by
  simp [fockKet]

example (B : Matrix (Fin 2) (Fin 2) ℂ) : fockOutput B 0 0 = fockKet 0 0 := by
  simp [fockOutput]

example : jointWeight (fockKet 1 0) (1, 0) = 1 := by
  simp [jointWeight, fockKet]

example (nm : ℕ × ℕ) : portOccupation 0 nm = nm.1 := by
  simp [portOccupation]

example (nm : ℕ × ℕ) : portOccupation 1 nm = nm.2 := by
  simp [portOccupation]

example (j : Fin 2) (n : ℕ) : marginalWeight 0 j n = 0 := by
  simp [marginalWeight, jointWeight]

example (j : Fin 2) : photonMean 0 j = 0 := by
  simp [photonMean, jointWeight]

end QAlgorithms.Papers.Independent.Dependency50.P34


