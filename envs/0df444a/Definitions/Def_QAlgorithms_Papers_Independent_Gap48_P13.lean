-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13
-- name    : QAlgorithms_Papers_Independent_Gap48_P13
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:35:54.797289+00:00
-- url     : https://prove2.me/theorems/6dd7255f-0444-4dc2-a2f5-c1a9c6082d0c
-- title:
--   Definitions for Markov triplets on CCR-algebras
-- statement:
--   The objects the formalized statements of *Markov triplets on CCR-algebras* (arXiv:0812.3724) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `hermiteValue`: PDF pp.3–4, (1),(5): the accepted physicists' Hermite function in one real coordinate.
--   - `exponentialVector`: PDF p.4, Lemma 1.1: an exponential vector in the complete number-space model. Summability is a conclusion below, so no nonsummable-tsum default is assumed.
--   - `creationPowerVacuum`: PDF pp.3–4, (7): the actual vector (a+)^n phi_0, not a bounded creation operator.
--   - `creationExponentialVacuum`: PDF p.4: exp(z a+) phi_0 means this convergent vector series. No operator-norm exponential of an unbounded operator is taken.
--   - `associatedLaguerre`: PDF p.5, (14): associated Laguerre polynomial for the nonnegative integer parameter.
--   - `in1`: PDF p.13: first time block injection.
--   - `in2`: PDF p.13: middle time block injection.
--   - `in3`: PDF p.13: third time block injection.
--   - `a22`: PDF p.13, (38): diagonal middle covariance block.
--   - `a12`: PDF p.13, (38): first-to-middle covariance block H2 -> H1.
--   - `a23`: PDF p.13, (38): middle-to-third covariance block H3 -> H2.
--   - `a13`: PDF p.13, (38): outer covariance block H3 -> H1.
--   - `marginal12`: PDF p.13: actual covariance of the 12 marginal, by Example 1.1.
--   - `marginal23`: PDF p.13: actual covariance of the 23 marginal, by Example 1.1.
--   - `entropyMode`: PDF p.11, eta(x)-eta(x+1): natural logarithms, including 0 log 0 = 0.
--   - `covarianceEntropy`: PDF pp.11–12, Theorem 1.3: explicit quasifree entropy Tr g(A). This is the finite one-particle trace of a spectral function, NOT the entropy of A viewed as a density. The bosonic Fock density has no particle cutoff. Only positive-semidefinite covariances are used in theorems.
--   - `IsMarkov`: PDF p.13, (36), with each quasifree marginal entropy evaluated by Theorem 1.3. All four terms are finite in finite modes, including vacuum and empty summands. This definition is independent of the projection/block-diagonal characterization.
--   - `diagonal3`: PDF p.14: block diagonal one-particle operators, in the three time factors.
--   - `assemble3`: PDF p.13: construct all nine blocks with the source's row/column directions.
--   - `bMatrix`: PDF p.13: B=diag(A restricted to H1+H2,I3); not a free matrix.
--   - `cMatrix`: PDF p.13: C=diag(I1,A22,I3); not a free matrix.
--   - `dMatrix`: PDF p.13: D=diag(I1,A restricted to H2+H3); not a free matrix.
--   - `PowerCondition`: PDF p.14, (40): exact order of all eight one-particle factors. Its theorem uses below are restricted to invertible covariances.
--   - `SeparatingProjection`: PDF p.17, Theorem 2.3: an orthogonal projection that separates H1 and H3. The column equations give its complete restrictions, not only compressed blocks.
--   - `realSpectrumFunction`: PDF p.21: complex-valued continuous functions on the real spectrum. Complex functional calculus is applied to z |-> f(Re z); for Hermitian A this is exactly f(A), and permits every continuous function of the finite real spectrum.
--   - `refinedIndex`: PDF p.14, (41): reindex the split middle space to the two independent pieces.
--   - `splitCovariance`: PDF p.14, (41): the constructed positive family, not a product assumption.
--   - `correlatedPair`: PDF pp.14–15: a concrete member of (41) with positive eigenvalues 3/2 and 5/2.
--   - `diagonalPair`: PDF p.17, Example 2.2: diagonal two-by-two blocks.
--   - `exampleCoupling`: PDF p.17, Example 2.2: the two neighbouring rational blocks.
--   - `exampleOuter`: PDF p.17, Example 2.2: the outer rational block, with identical columns.
--   - `counterexampleCovariance`: PDF p.17, Example 2.2: the explicit six-by-six covariance, with adjoint lower blocks.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, https://arxiv.org/abs/0812.3724v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

/-!
arXiv:0812.3724v2, Markov triplets on CCR-algebras.
The oscillator is the complete number-space representation of the Hermite basis.
Finite-mode Markovness is written using the explicit entropy formula of Theorem 1.3,
not using a projection criterion as its definition. Missing full Fock/CCR interfaces
and source defects are recorded in the unit's HARD.md and GAPS.json.
Compilation and independent moderation are pending the separate handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

namespace Osc
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad displacement displacementMatrix HasFockMatrix
   DisplacementRealized IsTraceClass IsDensity TraceHasSum fockTrace thermalDensity
   ThermalRealized photonMean photonProbability)
end Osc

/-- PDF pp.3–4, (1),(5): the accepted physicists' Hermite function in one real coordinate. -/
abbrev hermiteValue (n : ℕ) (x : ℝ) : ℂ :=
  QAlgorithms.Papers.Independent.Renew46.P19.hermiteFunction n (fun _ => x)

/-- PDF p.4, Lemma 1.1: an exponential vector in the complete number-space model.
Summability is a conclusion below, so no nonsummable-tsum default is assumed. -/
def exponentialVector (z : ℂ) : Osc.Fock :=
  ∑' n : ℕ, (z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) • Osc.fockKet n

/-- PDF pp.3–4, (7): the actual vector (a+)^n phi_0, not a bounded creation operator. -/
def creationPowerVacuum (n : ℕ) : Osc.Fock :=
  (Real.sqrt (Nat.factorial n : ℝ) : ℂ) • Osc.fockKet n

/-- PDF p.4: exp(z a+) phi_0 means this convergent vector series.
No operator-norm exponential of an unbounded operator is taken. -/
def creationExponentialVacuum (z : ℂ) : Osc.Fock :=
  ∑' n : ℕ, (z ^ n / (Nat.factorial n : ℂ)) • creationPowerVacuum n

/-- PDF p.5, (14): associated Laguerre polynomial for the nonnegative integer parameter. -/
def associatedLaguerre (m alpha : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * (Nat.factorial (m + alpha) : ℝ) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (m - k) : ℝ) *
        (Nat.factorial (alpha + k) : ℝ)) * x ^ k

example : creationPowerVacuum 0 = Osc.fockKet 0 := by
  simp [creationPowerVacuum]

example : Osc.displacement (-star (0 : ℂ)) = Osc.displacement 0 := by
  simp

example (x : ℝ) : associatedLaguerre 0 0 x = 1 := by
  simp [associatedLaguerre]

/-- PDF p.13: first time block injection. -/
def in1 {I J K : Type*} (i : I) : (I ⊕ (J ⊕ K)) := Sum.inl i

/-- PDF p.13: middle time block injection. -/
def in2 {I J K : Type*} (j : J) : (I ⊕ (J ⊕ K)) := Sum.inr (Sum.inl j)

/-- PDF p.13: third time block injection. -/
def in3 {I J K : Type*} (k : K) : (I ⊕ (J ⊕ K)) := Sum.inr (Sum.inr k)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- PDF p.13, (38): diagonal middle covariance block. -/
def a22 (A : Mat (I ⊕ (J ⊕ K))) : Mat J := A.submatrix in2 in2

/-- PDF p.13, (38): first-to-middle covariance block H2 -> H1. -/
def a12 (A : Mat (I ⊕ (J ⊕ K))) : Matrix I J ℂ := A.submatrix in1 in2

/-- PDF p.13, (38): middle-to-third covariance block H3 -> H2. -/
def a23 (A : Mat (I ⊕ (J ⊕ K))) : Matrix J K ℂ := A.submatrix in2 in3

/-- PDF p.13, (38): outer covariance block H3 -> H1. -/
def a13 (A : Mat (I ⊕ (J ⊕ K))) : Matrix I K ℂ := A.submatrix in1 in3

/-- PDF p.13: actual covariance of the 12 marginal, by Example 1.1. -/
def marginal12 (A : Mat (I ⊕ (J ⊕ K))) : Mat (I ⊕ J) :=
  A.submatrix (Sum.elim in1 in2) (Sum.elim in1 in2)

/-- PDF p.13: actual covariance of the 23 marginal, by Example 1.1. -/
def marginal23 (A : Mat (I ⊕ (J ⊕ K))) : Mat (J ⊕ K) :=
  A.submatrix Sum.inr Sum.inr

/-- PDF p.11, eta(x)-eta(x+1): natural logarithms, including 0 log 0 = 0. -/
def entropyMode (x : ℝ) : ℝ :=
  (x + 1) * Real.log (x + 1) - x * Real.log x

/-- PDF pp.11–12, Theorem 1.3: explicit quasifree entropy Tr g(A).
This is the finite one-particle trace of a spectral function, NOT the entropy
of A viewed as a density. The bosonic Fock density has no particle cutoff.
Only positive-semidefinite covariances are used in theorems. -/
def covarianceEntropy {L : Type*} [Fintype L] [DecidableEq L] (A : Mat L) : ℝ :=
  (cfc entropyMode A).trace.re

/-- PDF p.13, (36), with each quasifree marginal entropy evaluated by Theorem 1.3.
All four terms are finite in finite modes, including vacuum and empty summands.
This definition is independent of the projection/block-diagonal characterization. -/
def IsMarkov (A : Mat (I ⊕ (J ⊕ K))) : Prop :=
  covarianceEntropy A - covarianceEntropy (marginal23 A) =
    covarianceEntropy (marginal12 A) - covarianceEntropy (a22 A)

/-- PDF p.14: block diagonal one-particle operators, in the three time factors. -/
def diagonal3 (U1 : Mat I) (U2 : Mat J) (U3 : Mat K) : Mat (I ⊕ (J ⊕ K)) :=
  Matrix.fromBlocks U1 0 0 (Matrix.fromBlocks U2 0 0 U3)

/-- PDF p.13: construct all nine blocks with the source's row/column directions. -/
def assemble3 (A11 : Mat I) (A12 : Matrix I J ℂ) (A13 : Matrix I K ℂ)
    (A21 : Matrix J I ℂ) (A22 : Mat J) (A23 : Matrix J K ℂ)
    (A31 : Matrix K I ℂ) (A32 : Matrix K J ℂ) (A33 : Mat K) : Mat (I ⊕ (J ⊕ K)) :=
  fun i j => match i, j with
    | .inl r, .inl s => A11 r s
    | .inl r, .inr (.inl s) => A12 r s
    | .inl r, .inr (.inr s) => A13 r s
    | .inr (.inl r), .inl s => A21 r s
    | .inr (.inl r), .inr (.inl s) => A22 r s
    | .inr (.inl r), .inr (.inr s) => A23 r s
    | .inr (.inr r), .inl s => A31 r s
    | .inr (.inr r), .inr (.inl s) => A32 r s
    | .inr (.inr r), .inr (.inr s) => A33 r s

/-- PDF p.13: B=diag(A restricted to H1+H2,I3); not a free matrix. -/
def bMatrix (A : Mat (I ⊕ (J ⊕ K))) : Mat (I ⊕ (J ⊕ K)) :=
  assemble3 (A.submatrix in1 in1) (a12 A) 0
    (A.submatrix in2 in1) (a22 A) 0 0 0 1

/-- PDF p.13: C=diag(I1,A22,I3); not a free matrix. -/
def cMatrix (A : Mat (I ⊕ (J ⊕ K))) : Mat (I ⊕ (J ⊕ K)) := diagonal3 1 (a22 A) 1

/-- PDF p.13: D=diag(I1,A restricted to H2+H3); not a free matrix. -/
def dMatrix (A : Mat (I ⊕ (J ⊕ K))) : Mat (I ⊕ (J ⊕ K)) :=
  Matrix.fromBlocks 1 0 0 (marginal23 A)

/-- PDF p.14, (40): exact order of all eight one-particle factors.
Its theorem uses below are restricted to invertible covariances. -/
def PowerCondition (A : Mat (I ⊕ (J ⊕ K))) : Prop :=
  ∀ t : ℝ,
    imaginaryPower A t * imaginaryPower (1 + A) (-t) *
      imaginaryPower (dMatrix A) (-t) * imaginaryPower (1 + dMatrix A) t =
    imaginaryPower (bMatrix A) t * imaginaryPower (1 + bMatrix A) (-t) *
      imaginaryPower (cMatrix A) (-t) * imaginaryPower (1 + cMatrix A) t

/-- PDF p.17, Theorem 2.3: an orthogonal projection that separates H1 and H3.
The column equations give its complete restrictions, not only compressed blocks. -/
def SeparatingProjection (A P : Mat (I ⊕ (J ⊕ K))) : Prop :=
  P.IsHermitian ∧ P * P = P ∧
  (∀ (i : (I ⊕ (J ⊕ K))) (j : I), P i (in1 j) = (1 : Mat (I ⊕ (J ⊕ K))) i (in1 j)) ∧
  (∀ (i : (I ⊕ (J ⊕ K))) (k : K), P i (in3 k) = 0) ∧ P * A = A * P

/-- PDF p.21: complex-valued continuous functions on the real spectrum.
Complex functional calculus is applied to z |-> f(Re z); for Hermitian A this
is exactly f(A), and permits every continuous function of the finite real spectrum. -/
def realSpectrumFunction {L : Type*} [Fintype L] [DecidableEq L]
    (f : ℝ → ℂ) (A : Mat L) : Mat L := cfc (fun z : ℂ => f z.re) A

example : entropyMode 0 = 0 := by
  simp [entropyMode]

example : covarianceEntropy (0 : Mat (Fin 0)) = 0 := by
  simp [covarianceEntropy, Matrix.trace]

example (A : Mat (I ⊕ (J ⊕ K))) (i : I) (k : K) : a13 A i k = A (in1 i) (in3 k) := rfl

example (U1 : Mat I) (U2 : Mat J) (U3 : Mat K) (i : I) (k : K) :
    diagonal3 U1 U2 U3 (in1 i) (in3 k) = 0 := rfl

example (A : Mat (I ⊕ (J ⊕ K))) (i : K) (j : K) :
    bMatrix A (in3 i) (in3 j) = (1 : Mat K) i j := rfl

/-- PDF p.14, (41): reindex the split middle space to the two independent pieces. -/
def refinedIndex {I Ja Jb K : Type*} : (I ⊕ ((Ja ⊕ Jb) ⊕ K)) → (I ⊕ Ja) ⊕ (Jb ⊕ K)
  | .inl i => .inl (.inl i)
  | .inr (.inl (.inl j)) => .inl (.inr j)
  | .inr (.inl (.inr j)) => .inr (.inl j)
  | .inr (.inr k) => .inr (.inr k)

/-- PDF p.14, (41): the constructed positive family, not a product assumption. -/
def splitCovariance {I Ja Jb K : Type*} [Fintype I] [Fintype Ja] [Fintype Jb]
    [Fintype K] [DecidableEq I] [DecidableEq Ja] [DecidableEq Jb] [DecidableEq K]
    (L : Mat (I ⊕ Ja)) (R : Mat (Jb ⊕ K)) : Mat (I ⊕ ((Ja ⊕ Jb) ⊕ K)) :=
  (Matrix.fromBlocks L 0 0 R).submatrix refinedIndex refinedIndex

/-- PDF pp.14–15: a concrete member of (41) with positive eigenvalues 3/2 and 5/2. -/
def correlatedPair : Mat (Fin 1 ⊕ Fin 1) :=
  fun i j => if i = j then 2 else 1 / 2

example {Ja Jb : Type*} [Fintype Ja] [Fintype Jb] [DecidableEq Ja] [DecidableEq Jb]
    (L : Mat (I ⊕ Ja)) (R : Mat (Jb ⊕ K)) :
    a13 (splitCovariance L R) = 0 := by
  ext i k
  rfl

example : correlatedPair (Sum.inl 0) (Sum.inr 0) = 1 / 2 := rfl

/-- PDF p.17, Example 2.2: diagonal two-by-two blocks. -/
def diagonalPair (x y : ℂ) : Mat (Fin 2) := !![x, 0; 0, y]

/-- PDF p.17, Example 2.2: the two neighbouring rational blocks. -/
def exampleCoupling : Mat (Fin 2) := !![(1 : ℂ), 1; -(2 : ℂ) / 7, -(2 : ℂ) / 7]

/-- PDF p.17, Example 2.2: the outer rational block, with identical columns. -/
def exampleOuter : Mat (Fin 2) := !![(1 : ℂ) / 14, (1 : ℂ) / 14;
  -(1 : ℂ) / 49, -(1 : ℂ) / 49]

/-- PDF p.17, Example 2.2: the explicit six-by-six covariance, with adjoint lower blocks. -/
def counterexampleCovariance : Mat (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) :=
  assemble3 (diagonalPair 4 5) exampleCoupling exampleOuter
    exampleCoupling.conjTranspose (diagonalPair 6 3) exampleCoupling
    exampleOuter.conjTranspose exampleCoupling.conjTranspose (diagonalPair 3 1)

example : counterexampleCovariance (in1 0) (in3 0) = (1 : ℂ) / 14 := rfl

example : counterexampleCovariance (in3 0) (in1 1) = -(1 : ℂ) / 49 := by
  norm_num [counterexampleCovariance, assemble3, exampleOuter, in1, in3,
    Matrix.conjTranspose_apply]

end QAlgorithms.Papers.Independent.Gap48.P13


