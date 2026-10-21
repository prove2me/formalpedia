-- Prove2me | Definitions.Def_ShapleySnowSG_Kernel_KroneckerMEP
-- name    : ShapleySnowSG_Kernel_KroneckerMEP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:36.342041+00:00
-- url     : https://prove2.me/theorems/71cb3432-a3b8-4741-b7f2-b50354329690
-- title:
--   §2.2, §2.4, §3.1, Appendix A — Kronecker determinant (K5), auxiliary matrices Δ^ℓ, the solution sets S^M, T^M, S^Δ, S^R, reduced arrays and the family E
-- statement:
--   This file fixes the multiparameter-eigenvalue layer for an arbitrary $n\times(n+1)$ array of real matrices
--   $$D=\begin{pmatrix}M^1_0&M^1_1&\cdots&M^1_n\\ \vdots&&&\vdots\\ M^n_0&M^n_1&\cdots&M^n_n\end{pmatrix},$$
--   where the matrices of row $k$ all have the same size $p_k\times q_k$.
--
--   1. **Kronecker determinant.** For an $n\times n$ array $(A_{k\ell})$ with row $k$ made of $p_k\times q_k$ matrices, $\det_\otimes(A)$ is the $\prod_k p_k\times\prod_k q_k$ matrix whose entry at row $(i_1,\dots,i_n)$ and column $(j_1,\dots,j_n)$ is
--   $$\det\big(A_{k\ell}^{\,i_kj_k}\big)_{1\le k,\ell\le n}\qquad\text{(property (K5))}.$$
--   2. **Auxiliary matrices** (Definition 2.2.2). For $0\le\ell\le n$, $D^{(\ell)}$ is $D$ with its $(\ell+1)$-th column deleted and $\Delta^\ell:=(-1)^\ell\det_\otimes D^{(\ell)}$.
--   3. **Solution sets** (square arrays). $S^M$ and $S^\Delta$ accept complex solution vectors as in §2.4; the game-specific $T^M$ and $S^R$ use real solution vectors. $S^M$: $\det(M^k_0+z^1M^k_1+\dots+z^nM^k_n)=0$ for all $k$ (2.7); $T^M$: $\mathrm{val}(M^k_0+z^1M^k_1+\dots+z^nM^k_n)=0$ for all $k$ (§3.1); $S^\Delta$: $\det(\Delta^k-z^k\Delta^0)=0$ for all $k$ (2.8); $S^R$: $\mathrm{rank}(\Delta^k-z^k\Delta^0)<\max_{w\in\mathbb R}\mathrm{rank}(\Delta^k-w\Delta^0)$ for all $k$ (2.9).
--   4. **Reduced array** (3.2). Given, for each row $k$, row indices $\dot I_k$ and column indices $\dot J_k$ of equal size, $\dot M^k_\ell$ is the $\dot I_k\times\dot J_k$ sub-matrix of $M^k_\ell$.
--   5. **The family $E$** (p. 17). For matrices $A,B$ of equal size and $d\in\mathbb N$, $E$ is the set of polynomials $w\mapsto\det$ of a square sub-matrix of $A-wB$ that are nonzero and of degree at most $d$.
--
--   These are the objects in which the paper's characterisation of the discounted values is phrased.
--
--   **Formalization Note** Rows and columns of $\Delta^\ell$ are indexed by tuples $(i_1,\dots,i_n)$ rather than their lexicographic enumeration (Appendix A's canonical bijection); this only relabels rows and columns. Column $0$ of the array is the paper's column $\ell=0$; the paper's row $k\in\{1,\dots,n\}$ is `k : Fin n`, so $\Delta^k$ is `aux M k.succ`. $D^{(\ell)}$ keeps the remaining columns in order (`Fin.succAbove`). $S^M$ and $S^\Delta$ are polymorphic over real or complex arrays; `complexArray` maps a real array to complex entries for §2.4. $T^M$ and $S^R$ are real-valued for §3. "$\max_w\mathrm{rank}$" is encoded as "some real $w$ gives a strictly larger rank". $E$ uses square sub-matrices given by embeddings `Fin m ↪ R`, `Fin m ↪ C`, with the polynomial matrix $A-XB$.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 8, Definition 2.2.2; pp. 11–13, (2.7)–(2.9); p. 14, (3.2) and the four systems; p. 17, the family E^k; pp. 27–28, Definition A2 and (K5)

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix Polynomial

/-- Kronecker determinant of an `n × n` array of matrices whose `k`-th row consists of
`p k × q k` matrices, through its entry formula (K5), p. 28:
`det⊗(A)_{(i_1…i_n),(j_1…j_n)} = det [A_{kℓ}^{i_k j_k}]_{k,ℓ}`
(rows of the scalar determinant are the rows `k` of the array, columns are its columns `ℓ`).
Rows and columns are indexed by tuples instead of their lexicographic enumeration. -/
noncomputable def kronDet {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} {p q : Fin n → Type*}
    (A : ∀ k : Fin n, Fin n → Matrix (p k) (q k) 𝕜) : Matrix (∀ k, p k) (∀ k, q k) 𝕜 :=
  fun i j => Matrix.det (Matrix.of fun (k m : Fin n) => A k m (i k) (j k))

/-- Definition 2.2.2 (p. 8): the auxiliary matrices of an `n × (n+1)` array `M`
(`M k ℓ` is `M^{k+1}_ℓ`, column `0` first): `Δ^ℓ = (-1)^ℓ det⊗ D^{(ℓ)}`, where `D^{(ℓ)}`
deletes the column of index `ℓ` and keeps the others in order. -/
noncomputable def aux {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) 𝕜) (ℓ : Fin (n + 1)) :
    Matrix (∀ k, p k) (∀ k, q k) 𝕜 :=
  ((-1 : 𝕜) ^ (ℓ : ℕ)) • kronDet fun k m => M k (ℓ.succAbove m)

/-- Row `k` of the multiparameter pencil: `M^k_0 + z^1 M^k_1 + ⋯ + z^n M^k_n`. -/
def pencil {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) 𝕜) (z : Fin n → 𝕜) (k : Fin n) :
    Matrix (p k) (q k) 𝕜 :=
  M k 0 + ∑ l : Fin n, z l • M k l.succ

/-- `y^1 ⊗ ⋯ ⊗ y^n`, as a vector indexed by tuples. -/
def tensorVec {𝕜 : Type*} [CommMonoid 𝕜] {n : ℕ} {p : Fin n → Type*} (y : ∀ k, p k → 𝕜) :
    (∀ k, p k) → 𝕜 :=
  fun i => ∏ k, y k (i k)

/-- `S^M` (2.7), real solutions: `det(M^k_0 + z^1 M^k_1 + ⋯ + z^n M^k_n) = 0` for all `k`. -/
def SM {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} {p : Fin n → Type*}
    [∀ k, Fintype (p k)] [∀ k, DecidableEq (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) 𝕜) : Set (Fin n → 𝕜) :=
  {z | ∀ k, (pencil M z k).det = 0}

/-- `T^M` (§3.1, p. 14), real solutions: `val(M^k_0 + z^1 M^k_1 + ⋯ + z^n M^k_n) = 0` for all `k`. -/
def TM {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) ℝ) : Set (Fin n → ℝ) :=
  {z | ∀ k, IsMatVal (pencil M z k) 0}

/-- `S^Δ` (2.8), real solutions: `det(Δ^k − z^k Δ^0) = 0` for all `k`. -/
def SDelta {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} {p : Fin n → Type*}
    [∀ k, Fintype (p k)] [∀ k, DecidableEq (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) 𝕜) : Set (Fin n → 𝕜) :=
  {z | ∀ k, (aux M k.succ - z k • aux M 0).det = 0}

/-- The real array of §2.4 regarded over `ℂ`, where the multiparameter eigenvalue
problems (2.7)–(2.8) take their solutions. -/
noncomputable def complexArray {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) ℝ) :
    ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) ℂ :=
  fun k l => (M k l).map (algebraMap ℝ ℂ)

/-- Rank drop at `z`: `rank(A − zB) < max_{w ∈ ℝ} rank(A − wB)`, i.e. some real `w` gives a
strictly larger rank. -/
def RankDrop {m m' : Type*} [Fintype m'] (A B : Matrix m m' ℝ) (z : ℝ) : Prop :=
  ∃ w : ℝ, (A - z • B).rank < (A - w • B).rank

/-- `S^R` (2.9), real solutions: `rank(Δ^k − z^k Δ^0) < max_w rank(Δ^k − w Δ^0)` for all `k`. -/
def SR {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) ℝ) : Set (Fin n → ℝ) :=
  {z | ∀ k, RankDrop (aux M k.succ) (aux M 0) (z k)}

/-- The reduced array `Ḋ` (3.2): `Ṁ^k_ℓ` is the square sub-matrix of `M^k_ℓ` with rows
`r k 0, …` and columns `c k 0, …` (the kernel of state `k`). -/
def redArray {n : ℕ} {I J : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (I k) (J k) ℝ) (s : Fin n → ℕ)
    (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k) :
    ∀ k : Fin n, Fin (n + 1) → Matrix (Fin (s k)) (Fin (s k)) ℝ :=
  fun k l => (M k l).submatrix (r k) (c k)

/-- The family `E` of p. 17 for the pencil `A − wB`: the determinants of square sub-matrices of
`A − wB`, as polynomials in `w`, that are nonzero and of degree at most `d`. -/
noncomputable def Efam {R C : Type*} (A B : Matrix R C ℝ) (d : ℕ) : Set ℝ[X] :=
  {P | ∃ (m : ℕ) (f : Fin m ↪ R) (h : Fin m ↪ C),
      P = ((A.map Polynomial.C - (Polynomial.X : ℝ[X]) • B.map Polynomial.C).submatrix f h).det ∧
      P ≠ 0 ∧ P.natDegree ≤ d}

end ShapleySnowSG.Kernel


