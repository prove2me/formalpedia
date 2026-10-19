-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
-- name    : QAlgorithms_Papers_Independent_Information100_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:25:42.933+00:00
-- url     : https://prove2.me/theorems/e4e5eefd-0031-4861-8046-b0fd0b21c97b
-- title:
--   Definitions for Separability criteria and lower bounds of entanglement via realignment
-- statement:
--   The objects the formalized statements of *Separability criteria and lower bounds of entanglement via realignment* (arXiv:2610.15664) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `columnVec`: PDF p.2: column vectorization. The pair is (column, row), so lexicographic ordering stacks columns.
--   - `realignment`: PDF p.2: realignment, with ordinary transpose on the second vectorized factor.
--   - `nuclearNorm`: PDF p.2: rectangular nuclear norm, the trace of the positive square root of A-adjoint times A. The square matrix version is the frozen trace norm.
--   - `Parameters`: PDF p.3, Eq.(5): auxiliary matrices are real; all four dimensions are independent. The inner-product condition excludes r=0 without a redundant positivity assumption.
--   - `enhanced`: PDF p.3, Eq.(5): the affine enhanced realignment matrix. Neither marginal vector is conjugated. Empty auxiliary row sets are allowed.
--   - `augmentedGram`: PDF p.3, Eq.(6): real Gram matrix plus a real rank-one term, viewed over C.
--   - `separableBound`: PDF p.3, Eq.(6): the two PSD square roots multiply in the displayed order.
--   - `rankOneBlock`: PDF pp.2--3, Eqs.(2)--(4): common rank-one border formula. Constant vectors of length 1 give (2), constant vectors of length l give (3), arbitrary a,b give (4).
--   - `rankOneParameters`: PDF p.3: r=1, mu=nu=1, with arbitrary real border vectors.
--   - `PureEnsemble`: PDF pp.5,10: a finite normalized pure-state ensemble with its density. Zero weights are allowed, and the number of members is not fixed in advance.
--   - `convexRoof`: PDF pp.5,10, Eqs.(9),(11),(19): convex roof over every finite normalized pure-state decomposition. For the continuous pure costs used below and density matrices in positive finite dimension, the set is nonempty, bounded below and its infimum is attained, so this is the printed minimum. On an empty feasible set the total real sInf has value 0; no theorem below uses that case.
--   - `pureConcurrence`: PDF p.5, Eq.(8): pure concurrence, including the factor 2 under the radical.
--   - `concurrence`: PDF p.5, Eq.(9): mixed concurrence is a convex roof.
--   - `partialTransposeB`: PDF p.5, Eq.(10): partial transpose on B. This is the frozen partialTransposeFirst applied after exchanging the two subsystem factors.
--   - `pureNormalizedNegativity`: PDF p.5, Eq.(10): normalized pure negativity. Theorems using it require min(dA,dB)>=2; its value on a maximally entangled d-state is 1.
--   - `cren`: PDF p.5, Eq.(11): normalized CREN; distinct from mixed-state negativity.
--   - `SchmidtData`: PDF p.6, Lemma 2: Schmidt probabilities may vanish and the local dimensions may differ. Both families contain exactly min(dA,dB) orthonormal vectors.
--   - `schmidtVector`: PDF p.6: sqrt(lambda), rather than lambda, is the Schmidt amplitude.
--   - `Tripartite`: PDF pp.7--11: the tripartite basis is A x (B x C).
--   - `cutIndex`: PDF p.9: convert a cut basis (single party, other two parties in original order) to the A x (B x C) basis. 0=A|BC, 1=B|AC, 2=C|AB.
--   - `cutDensity`: PDF p.9, Eq.(15): density reindexed for the selected single-party cut.
--   - `IsBiseparableVector`: PDF p.9, Eq.(14): a normalized pure vector factors over at least one cut.
--   - `IsBiseparable`: PDF pp.7,9, Eq.(14): ensemble members may use DIFFERENT bipartitions.
--   - `tripartiteScore`: PDF p.9, Eq.(15): average of three trace norms using the SAME auxiliary tuple.
--   - `pureGME`: PDF p.10, Eq.(18): pure GME concurrence is a MINIMUM, with no factor sqrt(2).
--   - `gmeConcurrence`: PDF p.10, Eq.(19): mixed GME concurrence is its convex roof.
--   - `singletonEnsemble`: Sanity: a singleton pure ensemble is normalized and represents that state.
--   - `horodecki24`: PDF p.4, Example 1: Horodecki 2-by-4 density in lexicographic product basis. The formula is used only at a=0.9.
--   - `bell24`: PDF p.4, Example 1: the Bell vector uses |00> and |11> in C2 tensor C4.
--   - `exampleOneState`: PDF p.4, Example 1: x is the Bell signal fraction.
--   - `horodecki33`: PDF pp.4--5, Example 2: the Horodecki 3-by-3 state. Its selected t values are all strictly between 0 and 1, so its denominator is positive.
--   - `exampleTwoState`: PDF p.5, Example 2: p is the signal fraction, with white noise (1-p) I9/9.
--   - `qutritW`: PDF p.9, Example 4: the six QUTRIT basis words, not the qubit W state.
--   - `exampleFourState`: PDF p.9, Example 4: q is the signal fraction, with white noise (1-q) I27/27.
--   - `parametersTwo`: PDF pp.4,5,9: the common rank-two tuple has mu=nu=(1/sqrt(2),1/sqrt(2)).
--   - `BorderChoice`: PDF pp.4--5,9: package variable auxiliary row counts for finite tables.
--   - `rankOneChoice`: PDF pp.2--3: rank-one choices include zero-length borders for realignment.
--   - `bipartiteViolation`: PDF pp.4--5: witness violation is a STRICT trace-norm excess.
--   - `tripartiteViolation`: PDF p.9: a strict excess above the biseparable bound.
--   - `exampleOneChoice`: PDF p.4, Table I: order is our theorem, [31], [30], [29], [18].
--   - `exampleOneCutoff`: PDF p.4, Table I: exact terminating decimal sufficient cutoffs.
--   - `exampleTwoParameter`: PDF p.5, Table II: t rows, in printed order.
--   - `exampleTwoCutoff`: PDF p.5, Table II: columns [18], [29], [30], [31], our theorem. Every decimal digit of the printed bounds is retained.
--   - `exampleTwoChoice`: PDF p.5, Example 2: choices associated to all five comparison columns.
--   - `exampleFourChoice`: PDF pp.9--10, Table III: choices our theorem, [31], [30], [22].
--   - `exampleFourCutoff`: PDF pp.9--10, Table III: sufficient signal cutoffs.
-- source:
--   Separability criteria and lower bounds of entanglement via realignment, arXiv:2610.15664v1, https://arxiv.org/abs/2610.15664v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
# Separability criteria and lower bounds of entanglement via realignment

Source: arXiv:2610.15664v1. All page numbers below are PDF pages.
Paper-local definitions implement Eqs. (2)--(15), (18)--(19).
Theorem 5 and Examples 3 and 5 are deferred with source-interface reports.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

/-- PDF p.2: column vectorization. The pair is (column, row), so lexicographic
ordering stacks columns. -/
def columnVec {I J : Type*} (A : Matrix I J ℂ) : J × I → ℂ :=
  fun p => A p.2 p.1

/-- PDF p.2: realignment, with ordinary transpose on the second vectorized factor. -/
def realignment {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × I) (J × J) ℂ :=
  fun a b => rho (a.2, b.2) (a.1, b.1)

/-- PDF p.2: rectangular nuclear norm, the trace of the positive square root
of A-adjoint times A. The square matrix version is the frozen trace norm. -/
def nuclearNorm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℂ) : ℝ :=
  (cfc Real.sqrt (Aᴴ * A)).trace.re

/-- PDF p.3, Eq.(5): auxiliary matrices are real; all four dimensions are independent.
The inner-product condition excludes r=0 without a redundant positivity assumption. -/
structure Parameters (m n r : ℕ) where
  P : Matrix (Fin m) (Fin r) ℝ
  Q : Matrix (Fin n) (Fin r) ℝ
  mu : Fin r → ℝ
  nu : Fin r → ℝ
  pairing : ∑ k, nu k * mu k = 1

/-- PDF p.3, Eq.(5): the affine enhanced realignment matrix. Neither marginal
vector is conjugated. Empty auxiliary row sets are allowed. -/
def enhanced {I J : Type*} [Fintype I] [Fintype J] {m n r : ℕ}
    (z : Parameters m n r) (rho : Matrix (I × J) (I × J) ℂ) :
    Matrix (Fin m ⊕ (I × I)) (Fin n ⊕ (J × J)) ℂ :=
  Matrix.fromBlocks
    (fun i j => ((∑ k, z.P i k * z.Q j k : ℝ) : ℂ))
    (fun i b => ((∑ k, z.P i k * z.mu k : ℝ) : ℂ) * columnVec (traceLeft rho) b)
    (fun a j => columnVec (traceRight rho) a * ((∑ k, z.Q j k * z.nu k : ℝ) : ℂ))
    (realignment rho)

/-- PDF p.3, Eq.(6): real Gram matrix plus a real rank-one term, viewed over C. -/
def augmentedGram {s r : ℕ} (P : Matrix (Fin s) (Fin r) ℝ) (v : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ((∑ k, P k i * P k j) + v i * v j : ℝ)

/-- PDF p.3, Eq.(6): the two PSD square roots multiply in the displayed order. -/
def separableBound {m n r : ℕ} (z : Parameters m n r) : ℝ :=
  nuclearNorm (cfc Real.sqrt (augmentedGram z.P z.nu) *
    cfc Real.sqrt (augmentedGram z.Q z.mu))

/-- PDF pp.2--3, Eqs.(2)--(4): common rank-one border formula. Constant vectors
of length 1 give (2), constant vectors of length l give (3), arbitrary a,b give (4). -/
def rankOneBlock {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (rho : Matrix (I × J) (I × J) ℂ) :
    Matrix (Fin m ⊕ (I × I)) (Fin n ⊕ (J × J)) ℂ :=
  Matrix.fromBlocks (fun i j => ((a i * b j : ℝ) : ℂ))
    (fun i j => (a i : ℂ) * columnVec (traceLeft rho) j)
    (fun i j => columnVec (traceRight rho) i * (b j : ℂ)) (realignment rho)

/-- PDF p.3: r=1, mu=nu=1, with arbitrary real border vectors. -/
def rankOneParameters {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) : Parameters m n 1 where
  P := fun i _ => a i
  Q := fun i _ => b i
  mu := fun _ => 1
  nu := fun _ => 1
  pairing := by simp

/-- PDF pp.5,10: a finite normalized pure-state ensemble with its density.
Zero weights are allowed, and the number of members is not fixed in advance. -/
structure PureEnsemble (I : Type*) [Fintype I] where
  count : ℕ
  weight : Fin count → ℝ
  vector : Fin count → EuclideanSpace ℂ I
  nonnegative : ∀ k, 0 ≤ weight k
  total : ∑ k, weight k = 1
  normalized : ∀ k, IsState (vector k)

/-- PDF pp.5,10, Eqs.(9),(11),(19): convex roof over every finite normalized
pure-state decomposition. For the continuous pure costs used below and density
matrices in positive finite dimension, the set is nonempty, bounded below and
its infimum is attained, so this is the printed minimum. On an empty feasible
set the total real sInf has value 0; no theorem below uses that case. -/
def convexRoof {I : Type*} [Fintype I] (cost : EuclideanSpace ℂ I → ℝ)
    (rho : Matrix I I ℂ) : ℝ :=
  sInf {a : ℝ | ∃ e : PureEnsemble I,
    QAlgorithms.ensembleDensity e.weight e.vector = rho ∧ a = ∑ k, e.weight k * cost (e.vector k)}

/-- PDF p.5, Eq.(8): pure concurrence, including the factor 2 under the radical. -/
def pureConcurrence {I J : Type*} [Fintype I] [Fintype J]
    (phi : EuclideanSpace ℂ (I × J)) : ℝ :=
  let A := traceRight (pureDensity phi)
  Real.sqrt (2 * (1 - (A * A).trace.re))

/-- PDF p.5, Eq.(9): mixed concurrence is a convex roof. -/
def concurrence {I J : Type*} [Fintype I] [Fintype J]
    (rho : Matrix (I × J) (I × J) ℂ) : ℝ :=
  convexRoof pureConcurrence rho

/-- PDF p.5, Eq.(10): partial transpose on B. This is the frozen
partialTransposeFirst applied after exchanging the two subsystem factors. -/
def partialTransposeB {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun a b => Entanglement.partialTransposeFirst
    (fun x y : J × I => rho (x.2, x.1) (y.2, y.1)) (a.2, a.1) (b.2, b.1)

/-- PDF p.5, Eq.(10): normalized pure negativity. Theorems using it require
min(dA,dB)>=2; its value on a maximally entangled d-state is 1. -/
def pureNormalizedNegativity {dA dB : ℕ}
    (phi : EuclideanSpace ℂ (Fin dA × Fin dB)) : ℝ :=
  (nuclearNorm (partialTransposeB (pureDensity phi)) - 1) /
    ((min dA dB : ℝ) - 1)

/-- PDF p.5, Eq.(11): normalized CREN; distinct from mixed-state negativity. -/
def cren {dA dB : ℕ} (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : ℝ :=
  convexRoof pureNormalizedNegativity rho

/-- PDF p.6, Lemma 2: Schmidt probabilities may vanish and the local dimensions
may differ. Both families contain exactly min(dA,dB) orthonormal vectors. -/
structure SchmidtData (dA dB : ℕ) where
  probability : Fin (min dA dB) → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  total : ∑ i, probability i = 1
  left : Fin (min dA dB) → EuclideanSpace ℂ (Fin dA)
  right : Fin (min dA dB) → EuclideanSpace ℂ (Fin dB)
  leftOrthonormal : Orthonormal ℂ left
  rightOrthonormal : Orthonormal ℂ right

/-- PDF p.6: sqrt(lambda), rather than lambda, is the Schmidt amplitude. -/
def schmidtVector {dA dB : ℕ} (s : SchmidtData dA dB) :
    EuclideanSpace ℂ (Fin dA × Fin dB) :=
  ∑ k, (Real.sqrt (s.probability k) : ℂ) • tensorVec (s.left k) (s.right k)

/-- PDF pp.7--11: the tripartite basis is A x (B x C). -/
abbrev Tripartite (d : ℕ) := Fin d × (Fin d × Fin d)

/-- PDF p.9: convert a cut basis (single party, other two parties in original
order) to the A x (B x C) basis. 0=A|BC, 1=B|AC, 2=C|AB. -/
def cutIndex {d : ℕ} (k : Fin 3) (a : Tripartite d) : Tripartite d :=
  if k = 0 then a else if k = 1 then (a.2.1, (a.1, a.2.2))
  else (a.2.1, (a.2.2, a.1))

/-- PDF p.9, Eq.(15): density reindexed for the selected single-party cut. -/
def cutDensity {d : ℕ} (rho : Matrix (Tripartite d) (Tripartite d) ℂ) (k : Fin 3) :
    Matrix (Tripartite d) (Tripartite d) ℂ :=
  fun a b => rho (cutIndex k a) (cutIndex k b)

/-- PDF p.9, Eq.(14): a normalized pure vector factors over at least one cut. -/
def IsBiseparableVector {d : ℕ} (phi : EuclideanSpace ℂ (Tripartite d)) : Prop :=
  ∃ k : Fin 3, ∃ a : EuclideanSpace ℂ (Fin d),
    ∃ b : EuclideanSpace ℂ (Fin d × Fin d), IsState a ∧ IsState b ∧
      ∀ i, phi (cutIndex k i) = a i.1 * b i.2

/-- PDF pp.7,9, Eq.(14): ensemble members may use DIFFERENT bipartitions. -/
def IsBiseparable {d : ℕ} (rho : Matrix (Tripartite d) (Tripartite d) ℂ) : Prop :=
  ∃ e : PureEnsemble (Tripartite d), QAlgorithms.ensembleDensity e.weight e.vector = rho ∧
    ∀ k, IsBiseparableVector (e.vector k)

/-- PDF p.9, Eq.(15): average of three trace norms using the SAME auxiliary tuple. -/
def tripartiteScore {d m n r : ℕ} (z : Parameters m n r)
    (rho : Matrix (Tripartite d) (Tripartite d) ℂ) : ℝ :=
  (∑ k : Fin 3, nuclearNorm (enhanced z (cutDensity rho k))) / 3

/-- PDF p.10, Eq.(18): pure GME concurrence is a MINIMUM, with no factor sqrt(2). -/
def pureGME {d : ℕ} (phi : EuclideanSpace ℂ (Tripartite d)) : ℝ :=
  let f := fun k : Fin 3 =>
    let A := traceRight (cutDensity (pureDensity phi) k)
    Real.sqrt (1 - (A * A).trace.re)
  min (f 0) (min (f 1) (f 2))

/-- PDF p.10, Eq.(19): mixed GME concurrence is its convex roof. -/
def gmeConcurrence {d : ℕ} (rho : Matrix (Tripartite d) (Tripartite d) ℂ) : ℝ :=
  convexRoof pureGME rho

/-- Sanity: the first two entries of vec([[1,2],[3,4]]) are 1,3. -/
example : columnVec (!![(1 : ℂ), 2; 3, 4]) (0, 1) = 3 := by rfl

/-- Sanity: realignment on a product uses a transpose, with no conjugation. -/
example {I J : Type*} (A : Matrix I I ℂ) (B : Matrix J J ℂ) (a : I × I) (b : J × J) :
    realignment (Matrix.kronecker A B) a b = columnVec A a * columnVec B b := by rfl

/-- Sanity: the upper-left block is nonzero even at the zero operator. -/
example : enhanced (rankOneParameters (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 3))
    (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (Sum.inl 0) (Sum.inl 0) = 6 := by
  norm_num [enhanced, rankOneParameters, Matrix.fromBlocks]

/-- Sanity: the rectangular zero matrix has nuclear norm zero. -/
example : nuclearNorm (0 : Matrix (Fin 2) (Fin 3) ℂ) = 0 := by
  simp [nuclearNorm, cfc_zero]

/-- Sanity: real Gram augmentation is symmetric. -/
example {s r : ℕ} (P : Matrix (Fin s) (Fin r) ℝ) (v : Fin r → ℝ) :
    (augmentedGram P v).transpose = augmentedGram P v := by
  ext i j
  simp [augmentedGram, mul_comm]

/-- Sanity: the one-vector border recovers every block of Eq.(4). -/
example {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (rho : Matrix (I × J) (I × J) ℂ) :
    enhanced (rankOneParameters a b) rho = rankOneBlock a b rho := by
  simp [enhanced, rankOneParameters, rankOneBlock]

/-- Sanity: a singleton pure ensemble is normalized and represents that state. -/
def singletonEnsemble {I : Type*} [Fintype I] (phi : EuclideanSpace ℂ I)
    (hphi : IsState phi) : PureEnsemble I where
  count := 1
  weight := fun _ => 1
  vector := fun _ => phi
  nonnegative := by intro k; norm_num
  total := by simp
  normalized := fun _ => hphi

example {I : Type*} [Fintype I] (phi : EuclideanSpace ℂ I) (hphi : IsState phi) :
    QAlgorithms.ensembleDensity (singletonEnsemble phi hphi).weight
      (singletonEnsemble phi hphi).vector = pureDensity phi := by
  change (∑ _ : Fin 1, (1 : ℂ) • pureDensity phi) = pureDensity phi
  simp

/-- Sanity: partial transpose on B is involutive. -/
example {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ) :
    partialTransposeB (partialTransposeB rho) = rho := by rfl

/-- Sanity: a normalized singleton bipartite vector has zero pure concurrence. -/
example : pureConcurrence (ket (ι := Fin 1 × Fin 1) (0, 0)) = 0 := by
  simp [pureConcurrence, traceRight, pureDensity, ket, Matrix.mul_apply, Matrix.trace]

/-- Sanity: the three cut maps have the intended coordinate order. -/
example : cutIndex (d := 3) 1 (0, (1, 2)) = (1, (0, 2)) := by decide

example : cutIndex (d := 3) 2 (0, (1, 2)) = (1, (2, 0)) := by decide

/-- PDF p.4, Example 1: Horodecki 2-by-4 density in lexicographic product basis.
The formula is used only at a=0.9. -/
def horodecki24 (a : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  fun u v =>
    let i := u.1.val * 4 + u.2.val
    let j := v.1.val * 4 + v.2.val
    (((if i = j then (if i = 4 ∨ i = 7 then (1 + a) / 2 else a)
      else if (i, j) ∈ ([(0, 5), (5, 0), (1, 6), (6, 1), (2, 7), (7, 2)] : List (ℕ × ℕ))
        then a
      else if (i = 4 ∧ j = 7) ∨ (i = 7 ∧ j = 4) then Real.sqrt (1 - a ^ 2) / 2
      else 0) / (1 + 7 * a) : ℝ) : ℂ)

/-- PDF p.4, Example 1: the Bell vector uses |00> and |11> in C2 tensor C4. -/
def bell24 : EuclideanSpace ℂ (Fin 2 × Fin 4) :=
  (1 / Real.sqrt 2 : ℂ) • (ket (0, 0) + ket (1, 1))

/-- PDF p.4, Example 1: x is the Bell signal fraction. -/
def exampleOneState (x : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  ((1 - x : ℝ) : ℂ) • horodecki24 0.9 + (x : ℂ) • pureDensity bell24

/-- PDF pp.4--5, Example 2: the Horodecki 3-by-3 state. Its selected t values
are all strictly between 0 and 1, so its denominator is positive. -/
def horodecki33 (t : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun u v =>
    let i := u.1.val * 3 + u.2.val
    let j := v.1.val * 3 + v.2.val
    (((if i = j then (if i = 6 ∨ i = 8 then (1 + t) / 2 else t)
      else if (i, j) ∈ ([(0, 4), (4, 0), (0, 8), (8, 0), (4, 8), (8, 4)] : List (ℕ × ℕ))
        then t
      else if (i = 6 ∧ j = 8) ∨ (i = 8 ∧ j = 6) then Real.sqrt (1 - t ^ 2) / 2
      else 0) / (1 + 8 * t) : ℝ) : ℂ)

/-- PDF p.5, Example 2: p is the signal fraction, with white noise (1-p) I9/9. -/
def exampleTwoState (t p : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (((1 - p) / 9 : ℝ) : ℂ) • 1 + (p : ℂ) • horodecki33 t

/-- PDF p.9, Example 4: the six QUTRIT basis words, not the qubit W state. -/
def qutritW : EuclideanSpace ℂ (Tripartite 3) :=
  (1 / Real.sqrt 6 : ℂ) •
    (ket (0, (0, 1)) + ket (0, (1, 0)) + ket (1, (0, 0)) +
      ket (1, (1, 2)) + ket (1, (2, 1)) + ket (2, (1, 1)))

/-- PDF p.9, Example 4: q is the signal fraction, with white noise (1-q) I27/27. -/
def exampleFourState (q : ℝ) : Matrix (Tripartite 3) (Tripartite 3) ℂ :=
  (((1 - q) / 27 : ℝ) : ℂ) • 1 + (q : ℂ) • pureDensity qutritW

/-- PDF pp.4,5,9: the common rank-two tuple has mu=nu=(1/sqrt(2),1/sqrt(2)). -/
def parametersTwo {m n : ℕ} (P : Matrix (Fin m) (Fin 2) ℝ)
    (Q : Matrix (Fin n) (Fin 2) ℝ) : Parameters m n 2 where
  P := P
  Q := Q
  mu := fun _ => (Real.sqrt 2)⁻¹
  nu := fun _ => (Real.sqrt 2)⁻¹
  pairing := by
    simp only [Fin.sum_univ_two]
    rw [← two_mul, ← pow_two, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

/-- PDF pp.4--5,9: package variable auxiliary row counts for finite tables. -/
structure BorderChoice where
  rowsLeft : ℕ
  rowsRight : ℕ
  rank : ℕ
  parameters : Parameters rowsLeft rowsRight rank

/-- PDF pp.2--3: rank-one choices include zero-length borders for realignment. -/
def rankOneChoice {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) : BorderChoice :=
  ⟨m, n, 1, rankOneParameters a b⟩

/-- PDF pp.4--5: witness violation is a STRICT trace-norm excess. -/
def bipartiteViolation {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (c : BorderChoice) (rho : Matrix (I × J) (I × J) ℂ) : ℝ :=
  nuclearNorm (enhanced c.parameters rho) - separableBound c.parameters

/-- PDF p.9: a strict excess above the biseparable bound. -/
def tripartiteViolation {d : ℕ} (c : BorderChoice)
    (rho : Matrix (Tripartite d) (Tripartite d) ℂ) : ℝ :=
  tripartiteScore c.parameters rho - separableBound c.parameters - 2 * ((d : ℝ) - 1) / 3

/-- PDF p.4, Table I: order is our theorem, [31], [30], [29], [18]. -/
def exampleOneChoice (i : Fin 5) : BorderChoice :=
  if i = 0 then ⟨2, 2, 2, parametersTwo
    (!![9.28, 10.51; 10.44, 10.65]) (!![10.01, 12.75; 13.03, 13.54])⟩
  else if i = 1 then rankOneChoice
    ![11.9967, 12.9195, 11.6808, 12.1705, 11.4476]
    ![12.5025, 11.5102, 12.0119, 12.3982, 12.7818]
  else if i = 2 then rankOneChoice (fun _ : Fin 5 => 10) (fun _ : Fin 5 => 12)
  else if i = 3 then rankOneChoice (fun _ : Fin 1 => 10) (fun _ : Fin 1 => 12)
  else rankOneChoice (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)

/-- PDF p.4, Table I: exact terminating decimal sufficient cutoffs. -/
def exampleOneCutoff : Fin 5 → ℝ :=
  ![0.223231, 0.232959, 0.223267, 0.223276, 0.252746]

/-- PDF p.5, Table II: t rows, in printed order. -/
def exampleTwoParameter : Fin 5 → ℝ := ![0.2, 0.4, 0.6, 0.8, 0.9]

/-- PDF p.5, Table II: columns [18], [29], [30], [31], our theorem.
Every decimal digit of the printed bounds is retained. -/
def exampleTwoCutoff : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0.9955, 0.9943, 0.99408, 0.99406, 0.994043;
     0.9960, 0.9948, 0.99463, 0.99462, 0.994607;
     0.9972, 0.9964, 0.99627, 0.99626, 0.996251;
     0.9986, 0.9982, 0.998127, 0.998125, 0.9981233;
     0.9993, 0.9991, 0.99906893, 0.99906843, 0.999067726]

/-- PDF p.5, Example 2: choices associated to all five comparison columns. -/
def exampleTwoChoice (i : Fin 5) : BorderChoice :=
  if i = 0 then rankOneChoice (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
  else if i = 1 then rankOneChoice (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 2)
  else if i = 2 then rankOneChoice (fun _ : Fin 10 => 2) (fun _ : Fin 10 => 2)
  else if i = 3 then rankOneChoice
    (fun j : Fin 10 => if j = 0 then 17 / 8 else 2)
    (fun j : Fin 10 => if j = 0 then 21 / 10 else 2)
  else ⟨6, 6, 2, parametersTwo
    (!![3.511157, 1.621537; 0.8302, 2.934043; 1.626937, 2.083113;
        2.058475, 2.54207; 2.053231, 1.890969; 2.197353, 3.218868])
    (!![3.317891, 1.579999; 1.533877, 1.714491; 2.860596, 3.503382;
        2.042115, 3.078828; 0.519943, 3.29257; 1.828804, 0.217855])⟩

/-- PDF pp.9--10, Table III: choices our theorem, [31], [30], [22]. -/
def exampleFourChoice (i : Fin 4) : BorderChoice :=
  if i = 0 then ⟨3, 3, 2, parametersTwo
    (!![10.65, 11.57; 11.88, 11.94; 12.42, 11.69])
    (!![12.45, 12.81; 13.05, 12.1; 11.62, 12.45])⟩
  else if i = 1 then rankOneChoice ![1, 2] ![2, 1]
  else if i = 2 then rankOneChoice ![1, 1] ![1, 1]
  else rankOneChoice ![1] ![1]

/-- PDF pp.9--10, Table III: sufficient signal cutoffs. -/
def exampleFourCutoff : Fin 4 → ℝ := ![0.804647, 0.805132, 0.805211, 0.805318]

/-- Sanity: the 2-by-4 matrix retains its distinct bottom-block coupling. -/
example (a : ℝ) : horodecki24 a (1, 0) (1, 3) =
    ((Real.sqrt (1 - a ^ 2) / 2 / (1 + 7 * a) : ℝ) : ℂ) := by
  simp [horodecki24]

/-- Sanity: the 3-by-3 matrix has the printed 00--22 coherence. -/
example (t : ℝ) : horodecki33 t (0, 0) (2, 2) = ((t / (1 + 8 * t) : ℝ) : ℂ) := by
  simp [horodecki33]

/-- Sanity: the literal cutoff with nine fractional digits is retained. -/
example : exampleTwoCutoff 4 4 = (999067726 : ℝ) / 1000000000 := by
  change (0.999067726 : ℝ) = (999067726 : ℝ) / 1000000000
  norm_num

/-- Sanity: the white-noise endpoint is exactly the maximally mixed state. -/
example : exampleTwoState 0.9 0 = (1 / 9 : ℂ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) := by
  norm_num [exampleTwoState]

example : exampleFourState 0 = (1 / 27 : ℂ) • (1 : Matrix (Tripartite 3) (Tripartite 3) ℂ) := by
  norm_num [exampleFourState]

/-- Sanity: |112> is one of the six qutrit W words, with amplitude 1/sqrt(6). -/
example : qutritW (1, (1, 2)) = (1 / Real.sqrt 6 : ℂ) := by
  simp [qutritW, ket]

end QAlgorithms.Papers.Independent.Information100.P03


