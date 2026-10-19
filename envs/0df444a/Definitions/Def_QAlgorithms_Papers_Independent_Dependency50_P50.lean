-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
-- name    : QAlgorithms_Papers_Independent_Dependency50_P50
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:24:11.229837+00:00
-- url     : https://prove2.me/theorems/c9d22d1d-7247-457d-8b63-c4f5d6510b90
-- title:
--   Definitions for The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps
-- statement:
--   The objects the formalized statements of *The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps* (arXiv:quant-ph/0702255) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Bipartite`: PDF pp.3–4: C^n tensor C^m in the ordered product coordinate basis.
--   - `BipartiteMat`: PDF p.5, §IV: operators on the ordered input-reference/output tensor product.
--   - `schmidtNumber`: PDF p.4 after Theorem 1: coefficient-matrix rank, the Schmidt number. This agrees with either reduced rank and extends the definition to zero by rank zero; there is no unit-norm restriction.
--   - `PreservesHermiticity`: PDF p.3, §II: preservation of all Hermitian operators.
--   - `Positive`: PDF p.3, §II: positive means positive semidefinite, with no normalization.
--   - `j2`: PDF p.5, equation (4): the complex-linear, unnormalized J2 map. The entry formula is the matrix-unit sum Σ_ij E_ij tensor T(E_ij).
--   - `j1`: PDF p.4, Lemma 2: J1 in the canonical matrix-unit basis, with E_ij* in its first factor; hence the two reference indices are reversed.
--   - `hsPair`: PDF pp.3,5: Hilbert–Schmidt pairing, linear in its left argument, explicitly Σ_ij conjugate(B_ij) A_ij = Tr(B* A).
--   - `mapPair`: PDF p.5, equations (5)–(7): the Hilbert–Schmidt pairing on map space, computed by summing the output pairings over the canonical input matrix units.
--   - `j2Family`: PDF p.6, basis-dependence paragraph: the J2 sum with a supplied family F. Statements using an arbitrary basis carry a genuine complex basis parameter.
--   - `phaseBasis`: PDF p.6: an explicit changed basis witnessing basis dependence at n=m=2. Multiplying every canonical matrix unit by i gives another orthonormal basis; the J2 sum is multiplied by i squared, hence changes sign.
--   - `antisymmetricVector`: PDF p.8: the antisymmetric vector e1 tensor e2 - e2 tensor e1. Source indices 1,2 are Lean indices 0,1; this vector has norm sqrt(2).
-- source:
--   The Jamiołkowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, https://arxiv.org/abs/quant-ph/0702255v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

/-!
arXiv:quant-ph/0702255v1, Ranade and Ali (2007), PDF pp.3–8.
Concrete finite-dimensional coordinates: reference/input first, output second.
The source inner product is linear in its first argument, so its quadratic form
⟨Cv,v⟩ is `inner ℂ v (QAlgorithms.act C v)` in Mathlib.
The Choi matrices below are unnormalized. No trace-preservation is assumed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF pp.3–4: C^n tensor C^m in the ordered product coordinate basis. -/
abbrev Bipartite (n m : ℕ) := EuclideanSpace ℂ (Fin n × Fin m)

/-- PDF p.5, §IV: operators on the ordered input-reference/output tensor product. -/
abbrev BipartiteMat (n m : ℕ) := Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ

/-- PDF p.4 after Theorem 1: coefficient-matrix rank, the Schmidt number.
This agrees with either reduced rank and extends the definition to zero by rank zero;
there is no unit-norm restriction. -/
def schmidtNumber {n m : ℕ} (v : Bipartite n m) : ℕ :=
  Matrix.rank (Matrix.of (fun (i : Fin n) (j : Fin m) => v (i, j)))

/-- PDF p.3, §II: preservation of all Hermitian operators. -/
def PreservesHermiticity {n m : ℕ} (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∀ A : (Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → (T A).IsHermitian

/-- PDF p.3, §II: positive means positive semidefinite, with no normalization. -/
def Positive {n m : ℕ} (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∀ A : (Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → (T A).PosSemidef

/-- PDF p.5, equation (4): the complex-linear, unnormalized J2 map.
The entry formula is the matrix-unit sum Σ_ij E_ij tensor T(E_ij). -/
def j2 {n m : ℕ} : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) →ₗ[ℂ] BipartiteMat n m where
  toFun T := fun p q => T (Matrix.single p.1 q.1 1) p.2 q.2
  map_add' T S := by ext p q; rfl
  map_smul' c T := by ext p q; rfl

/-- PDF p.4, Lemma 2: J1 in the canonical matrix-unit basis, with E_ij*
in its first factor; hence the two reference indices are reversed. -/
def j1 {n m : ℕ} (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : BipartiteMat n m :=
  fun p q => T (Matrix.single q.1 p.1 1) p.2 q.2

/-- PDF pp.3,5: Hilbert–Schmidt pairing, linear in its left argument,
explicitly Σ_ij conjugate(B_ij) A_ij = Tr(B* A). -/
def hsPair {I : Type*} [Fintype I] (A B : Matrix I I ℂ) : ℂ :=
  ∑ i, ∑ j, conj (B i j) * A i j

/-- PDF p.5, equations (5)–(7): the Hilbert–Schmidt pairing on map space,
computed by summing the output pairings over the canonical input matrix units. -/
def mapPair {n m : ℕ} (T S : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : ℂ :=
  ∑ a : Fin n × Fin n, hsPair (T (Matrix.single a.1 a.2 1)) (S (Matrix.single a.1 a.2 1))

/-- PDF p.6, basis-dependence paragraph: the J2 sum with a supplied family F.
Statements using an arbitrary basis carry a genuine complex basis parameter. -/
def j2Family {n m : ℕ} (F : (Fin n × Fin n) → (Matrix (Fin n) (Fin n) ℂ)) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    BipartiteMat n m :=
  ∑ a : Fin n × Fin n, Matrix.kronecker (F a) (T (F a))

/-- PDF p.6: an explicit changed basis witnessing basis dependence at n=m=2.
Multiplying every canonical matrix unit by i gives another orthonormal basis;
the J2 sum is multiplied by i squared, hence changes sign. -/
def phaseBasis : (Fin 2 × Fin 2) → (Matrix (Fin 2) (Fin 2) ℂ) :=
  fun a => Complex.I • Matrix.single a.1 a.2 1

/-- PDF p.8: the antisymmetric vector e1 tensor e2 - e2 tensor e1.
Source indices 1,2 are Lean indices 0,1; this vector has norm sqrt(2). -/
def antisymmetricVector : Bipartite 2 2 :=
  QAlgorithms.tensorVec (QAlgorithms.ket (0 : Fin 2)) (QAlgorithms.ket (1 : Fin 2)) -
    QAlgorithms.tensorVec (QAlgorithms.ket (1 : Fin 2)) (QAlgorithms.ket (0 : Fin 2))

/-- Sanity check: the Weyl matrix unit has entry one at its specified row/column. -/
example {n : ℕ} (i j : Fin n) : Matrix.single i j (1 : ℂ) i j = 1 := by
  simp

/-- Sanity check: zero has Schmidt number zero, including cancellation/empty sums. -/
example {n m : ℕ} : schmidtNumber (0 : Bipartite n m) = 0 := by
  change Matrix.rank (0 : Matrix (Fin n) (Fin m) ℂ) = 0
  exact Matrix.rank_zero

/-- Sanity check: J2 has no transpose in the reference factor and no factor 1/n. -/
example {n m : ℕ} (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) (i j : Fin n) (a b : Fin m) :
    j2 T (i, a) (j, b) = T (Matrix.single i j 1) a b := rfl

/-- Sanity check: the frozen amplification applies T to each entire matrix block. -/
example {n m k : ℕ} (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ))
    (A : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ)
    (a b : Fin k) (i j : Fin m) :
    QAlgorithms.idTensorSuperop (R := Fin k) T A (a, i) (b, j) =
      T (fun x y => A (a, x) (b, y)) i j := rfl

end QAlgorithms.Papers.Independent.Dependency50.P50


