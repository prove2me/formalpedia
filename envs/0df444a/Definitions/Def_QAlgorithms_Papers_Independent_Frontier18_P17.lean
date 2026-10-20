-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17
-- name    : QAlgorithms_Papers_Independent_Frontier18_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T18:25:32.027305+00:00
-- url     : https://prove2.me/theorems/b83597d0-7273-478c-980f-e57abfd86452
-- title:
--   Definitions for Singular value decomposition and matrix reorderings in quantum information theory
-- statement:
--   The objects the formalized statements of *Singular value decomposition and matrix reorderings in quantum information theory* (arXiv:1011.1585) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `res`: PDF p.2, Eq. (5): row stacking, row index first.
--   - `vec`: PDF p.2, Eq. (6): column stacking, column index first.
--   - `unres`: PDF pp.2,7: inverse row reshaping, including rectangular matrices.
--   - `reshuffle`: PDF p.3, Definition 2: primary reshuffling in matrix-unit coordinates.
--   - `alternateReshuffle`: PDF p.3, Definition 3: reversed subsystem order and transposed matrix-unit bases.
--   - `hs`: PDF pp.1,5, Eq. (1): Hilbert–Schmidt product, conjugate-linear in the first slot.
--   - `ThinSVD`: PDF p.2, Eqs. (2)–(4): thin SVD with precisely the positive terms. The full matrix identity and orthonormal families specify all nonzero singular data.
--   - `operatorCoefficients`: PDF p.5, Eq. (31): printed array (rho, E_i tensor E_j), conjugate to the usual expansion array. This is not asserted to be Eq. (29)'s coefficient array.
--   - `superMatrix`: PDF p.6, Eq. (35): row-vectorized matrix of a linear map, output index first.
--   - `dynamical`: PDF p.6, Eqs. (37),(39): unnormalized dynamical matrix, output factor first.
--   - `jamiolkowski`: PDF p.6, Eq. (43): normalize by the input dimension, positive in the theorem.
--   - `CPTP`: PDF pp.5–6, Definition 7: CP and TP on the full complex matrix algebra. CP uses the accepted predicate; it does not silently impose TP in Choi's criterion.
--   - `reshuffleMatrix`: PDF pp.3,8: permutation from row coordinates to reshuffled row coordinates.
--   - `unreshuffleMatrix`: PDF p.8, Eq. (63): explicit inverse permutation, with its own index types.
--   - `depolarizingKraus`: PDF p.7, Eq. (57): valid Pauli Kraus family in Eq. (50)'s parameter convention.
--   - `shift`: PDF p.8, Eq. (60): X_d sends j to j-1 modulo d.
--   - `clock`: PDF p.8, Eq. (61): positive clock phase exp(2 pi i j/d).
--   - `pauliChannel`: PDF p.8, Eq. (62): generalized Pauli map with an arbitrary probability array. Transport the frozen positive shift from cyclic residues to Fin d and negate its shift exponent, giving the source's X^i Z^j with X|j> = |j-1>.
--   - `partialTranspose`: PDF p.8, Example 6: transpose only the first factor of every input operator.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, https://arxiv.org/abs/1011.1585v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

/-!
Miszczak, arXiv:1011.1585v2 (2011). Statements only; PDF page numbers.
Product indices use the canonical row-major order. The inverse reshuffling is
explicitly typed. Frozen tensor, transpose, depolarizing and Weyl interfaces
are imported; the remaining new definitions are local to this paper.
Contradictory Eqs. (54)–(56) and Definition 9 are recorded in HARD.md.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)
open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.2, Eq. (5): row stacking, row index first. -/
def res {I J : Type*} (A : Matrix I J ℂ) : EuclideanSpace ℂ (I × J) :=
  WithLp.toLp 2 fun p => A p.1 p.2

/-- PDF p.2, Eq. (6): column stacking, column index first. -/
def vec {I J : Type*} (A : Matrix I J ℂ) : EuclideanSpace ℂ (J × I) :=
  WithLp.toLp 2 fun p => A p.2 p.1

/-- PDF pp.2,7: inverse row reshaping, including rectangular matrices. -/
def unres {I J : Type*} (v : EuclideanSpace ℂ (I × J)) : Matrix I J ℂ :=
  fun i j => v (i,j)

/-- PDF p.3, Definition 2: primary reshuffling in matrix-unit coordinates. -/
def reshuffle {I J : Type*} (A : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × I) (J × J) ℂ :=
  fun p q => A (p.1,q.1) (p.2,q.2)

/-- PDF p.3, Definition 3: reversed subsystem order and transposed matrix-unit bases. -/
def alternateReshuffle {I J : Type*} (A : Matrix (I × J) (I × J) ℂ) :
    Matrix (J × J) (I × I) ℂ :=
  fun p q => A (q.2,p.2) (q.1,p.1)

/-- PDF pp.1,5, Eq. (1): Hilbert–Schmidt product, conjugate-linear in the first slot. -/
def hs {I J : Type*} [Fintype I] [Fintype J] (A B : Matrix I J ℂ) : ℂ :=
  inner ℂ (res A) (res B)

/-- PDF p.2, Eqs. (2)–(4): thin SVD with precisely the positive terms.
The full matrix identity and orthonormal families specify all nonzero singular data. -/
def ThinSVD {I J : Type*} [Fintype I] [Fintype J] {k : ℕ}
    (A : Matrix I J ℂ) (s : Fin k → ℝ)
    (u : Fin k → EuclideanSpace ℂ I) (v : Fin k → EuclideanSpace ℂ J) : Prop :=
  Orthonormal ℂ u ∧ Orthonormal ℂ v ∧ (∀ i, 0 < s i) ∧
    A = ∑ i, (s i : ℂ) • (fun a b => u i a * conj (v i b))

/-- PDF p.5, Eq. (31): printed array (rho, E_i tensor E_j), conjugate to the
usual expansion array. This is not asserted to be Eq. (29)'s coefficient array. -/
def operatorCoefficients {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (rho : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × I) (J × J) ℂ :=
  fun a b => hs rho (Matrix.kronecker (Matrix.single a.1 a.2 1) (Matrix.single b.1 b.2 1))

/-- PDF p.6, Eq. (35): row-vectorized matrix of a linear map, output index first. -/
def superMatrix {I J : Type*} [DecidableEq I]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : Matrix (J × J) (I × I) ℂ :=
  fun a b => Phi (Matrix.single b.1 b.2 1) a.1 a.2

/-- PDF p.6, Eqs. (37),(39): unnormalized dynamical matrix, output factor first. -/
def dynamical {I J : Type*} [DecidableEq I]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : Matrix (J × I) (J × I) ℂ :=
  fun p q => Phi (Matrix.single p.2 q.2 1) p.1 q.1

/-- PDF p.6, Eq. (43): normalize by the input dimension, positive in the theorem. -/
def jamiolkowski {I J : Type*} [Fintype I] [DecidableEq I]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : Matrix (J × I) (J × I) ℂ :=
  ((Fintype.card I : ℂ)⁻¹) • dynamical Phi

/-- PDF pp.5–6, Definition 7: CP and TP on the full complex matrix algebra.
CP uses the accepted predicate; it does not silently impose TP in Choi's criterion. -/
def CPTP {I J : Type*} [Fintype I] [Fintype J]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive Phi ∧ ∀ X, (Phi X).trace = X.trace

/-- PDF pp.3,8: permutation from row coordinates to reshuffled row coordinates. -/
def reshuffleMatrix (I J : Type*) [DecidableEq I] [DecidableEq J] :
    Matrix ((I × I) × (J × J)) ((I × J) × (I × J)) ℂ :=
  fun p q => if p = ((q.1.1,q.2.1),(q.1.2,q.2.2)) then 1 else 0

/-- PDF p.8, Eq. (63): explicit inverse permutation, with its own index types. -/
def unreshuffleMatrix (I J : Type*) [DecidableEq I] [DecidableEq J] :
    Matrix ((I × J) × (I × J)) ((I × I) × (J × J)) ℂ :=
  fun p q => if p = ((q.1.1,q.2.1),(q.1.2,q.2.2)) then 1 else 0

/-- PDF p.7, Eq. (57): valid Pauli Kraus family in Eq. (50)'s parameter convention. -/
def depolarizingKraus (p : ℝ) : Fin 4 → Matrix Bool Bool ℂ :=
  ![((Real.sqrt (1+3*p) / 2 : ℝ) : ℂ) • 1,
    ((Real.sqrt (1-p) / 2 : ℝ) : ℂ) • QAlgorithms.pauliX,
    ((Real.sqrt (1-p) / 2 : ℝ) : ℂ) • QAlgorithms.pauliY,
    ((Real.sqrt (1-p) / 2 : ℝ) : ℂ) • QAlgorithms.pauliZ]

/-- PDF p.8, Eq. (60): X_d sends j to j-1 modulo d. -/
def shift (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val = (j.val + d - 1) % d then 1 else 0

/-- PDF p.8, Eq. (61): positive clock phase exp(2 pi i j/d). -/
def clock (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (d : ℂ))

/-- PDF p.8, Eq. (62): generalized Pauli map with an arbitrary probability array.
Transport the frozen positive shift from cyclic residues to Fin d and negate its
shift exponent, giving the source's X^i Z^j with X|j> = |j-1>. -/
def pauliChannel (d : ℕ) [NeZero d] (p : (Fin d × Fin d) → ℝ)
    (rho : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ a : Fin d × Fin d, let W := ((QAlgorithms.Papers.Independent.Information100.P34.weyl
      (d := d) (-(a.1.val : ZMod d)) (a.2.val : ZMod d)).submatrix
        (fun i : Fin d => (i.val : ZMod d)) (fun i : Fin d => (i.val : ZMod d)))
    (p a : ℂ) • (W * rho * Wᴴ)

/-- PDF p.8, Example 6: transpose only the first factor of every input operator. -/
def partialTranspose {I J : Type*} (X : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun p q => X (q.1,p.2) (p.1,q.2)

/-! Sanity examples for the coordinate and boundary conventions. -/

example {I J : Type*} (A : Matrix I J ℂ) (i : I) (j : J) : res A (i,j) = A i j := rfl

example {I J : Type*} (A : Matrix I J ℂ) (i : I) (j : J) : vec A (j,i) = A i j := rfl

example {I J : Type*} (A : Matrix I J ℂ) : unres (res A) = A := rfl

example {I J : Type*} (A : Matrix (I × J) (I × J) ℂ) (i k : I) (j l : J) :
    reshuffle A (i,k) (j,l) = A (i,j) (k,l) := rfl

example {I J : Type*} (A : Matrix (I × J) (I × J) ℂ) (i k : I) (j l : J) :
    alternateReshuffle A (j,l) (i,k) = A (k,l) (i,j) := rfl

example {I J : Type*} [Fintype I] [Fintype J] (A B : Matrix I J ℂ) :
    hs A B = inner ℂ (res A) (res B) := rfl

example {I J : Type*} [Fintype I] [Fintype J] :
    ThinSVD (0 : Matrix I J ℂ) (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) := by
  simp [ThinSVD, Orthonormal] <;> rfl

example {I J : Type*} [DecidableEq I] (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (i j : I) (a b : J) : dynamical Phi (a,i) (b,j) = Phi (Matrix.single i j 1) a b := rfl

example {I J : Type*} [DecidableEq I] (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (i j : I) (a b : J) : superMatrix Phi (a,b) (i,j) = Phi (Matrix.single i j 1) a b := rfl

example {I J : Type*} [Fintype I] [DecidableEq I]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) :
    jamiolkowski Phi = ((Fintype.card I : ℂ)⁻¹) • dynamical Phi := rfl

example (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    transposeMap N X = X.transpose := rfl

example (p : ℝ) : depolarizingKraus p 0 =
    ((Real.sqrt (1+3*p) / 2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := rfl

example (X : Matrix Bool Bool ℂ) : depolarizing 1 X = X := by simp [QAlgorithms.Papers.Independent.Information100.P30.depolarizing]

example : shift 3 (0 : Fin 3) (1 : Fin 3) = 1 := by norm_num [shift]

example : clock 1 (0 : Fin 1) (0 : Fin 1) = 1 := by simp [clock]

example {I J : Type*} (X : Matrix (I × J) (I × J) ℂ) (i k : I) (j l : J) :
    partialTranspose X (i,j) (k,l) = X (k,j) (i,l) := rfl

example {I J : Type*} [DecidableEq I] [DecidableEq J] (i k : I) (j l : J) :
    reshuffleMatrix I J ((i,k),(j,l)) ((i,j),(k,l)) = 1 := by
  simp [reshuffleMatrix]

example {I J : Type*} [DecidableEq I] [DecidableEq J] (i k : I) (j l : J) :
    unreshuffleMatrix I J ((i,j),(k,l)) ((i,k),(j,l)) = 1 := by
  simp [unreshuffleMatrix]

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (Psi : Matrix J J ℂ →ₗ[ℂ] Matrix J J ℂ) :
    tensorMap Phi Psi 0 = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P30.tensorMap]

example {I : Type*} [Fintype I] :
    CPTP (LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) := by
  constructor
  · intro r X hX
    have hid : QAlgorithms.idTensorSuperop
        (LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) X = X := by
      ext p q
      rfl
    rw [hid]
    exact hX
  · intro X
    rfl

example {d : ℕ} [NeZero d] :
    QAlgorithms.Papers.Independent.Information100.P34.weyl (d := d) 0 0 = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P34.weyl]

end QAlgorithms.Papers.Independent.Frontier18.P17


