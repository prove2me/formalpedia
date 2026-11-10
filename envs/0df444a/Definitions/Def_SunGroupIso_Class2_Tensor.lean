-- Prove2me | Definitions.Def_SunGroupIso_Class2_Tensor
-- name    : SunGroupIso_Class2_Tensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:12.587741+00:00
-- url     : https://prove2.me/theorems/9016aa53-aa53-4686-94a5-9b9e3bfd108b
-- title:
--   Alternating tensors, the complex parameter, restricted tensor isomorphism and matrix-tuple congruence over $\mathbb Z/p^\tau$
-- statement:
--   Over $R=\mathbb Z/p^\tau\mathbb Z$: an $n\times n\times m$ tensor $T=(t_{i,j,k})$ is **alternating** if $t_{i,j,k}=-t_{j,i,k}$ and $t_{i,i,k}=0$. $(X,Y,Z)\circ T$ has entries $\sum X_{i,i'}Y_{j,j'}Z_{k,k'}t_{i',j',k'}$. $N_{T,\vec x}=\sum_i x_iN_{T,i}$ with $N_{T,i}[j,k]=t_{i,j,k}$, and $M_{T,\vec y}=\sum_k y_kM_{T,k}$ with $M_{T,k}[i,j]=t_{i,j,k}$. The **complex parameter** is $c_T=c_{T,0}+c_{T,1}$ where $p^{c_{T,0}}$ and $p^{c_{T,1}}$ are the numbers of distinct $N_{T,\vec x}$ and $M_{T,\vec y}$.
--
--   An **instance of the restricted alternating tensor isomorphism problem** with parameter $w$ is $(T,T',P,P')$, $P,P'\in M(d\times n,R)$, $T,T'$ alternating, such that (1) $P\vec x=0$ implies $N_{T,\vec x}[j,k]=0$ for all $j,k>w$, and (2) $N_{T,\vec x}=0$ implies $P\vec x=0$. A **solution** is $X\in GL(n,R)$, $Y\in GL(m,R)$ with $(X,X,Y)\circ T=T'$ and $PX^{T}=P'$.
--
--   A square matrix is **alternating** if $A^T=-A$ with zero diagonal. Tuples $A,B\in M(n,R)^m$ are **congruent** if $P^TA_iP=B_i$ for all $i$ and some $P\in GL(n,R)$; the **automorphism group** is $\{P\in GL(n,R):P^TA_iP=A_i\ \forall i\}$.
--
--   **Codes.** Matrices row-major, tensors in $(i,j,k)$ order, entries as representatives in $[0,p^\tau)$, preceded by the header $p,\tau,n,m$.
--
--   **Formalization Note** Indices are zero-based: the page's "$j,k>w$" is `w ≤ j.val`. $c_T$ uses `Nat.log p` of the two image sizes, which are powers of $p$.
--
--   `NondegenerateTuple` is the §2.1 convention: every row and column of every invertibly transformed tuple has a nonzero entry in some matrix. `NondegenerateTensor` applies it to the slice tuple (N_{T,i})_i.
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), §2.1 pp. 8–9 (PDF 10–11); §2.3 p. 10 (PDF 12)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)

variable {R : Type*} [CommRing R]

/-- **Alternating tensor** (§2.3, p. 10, PDF p. 12): an `n × n × m` tensor `T = (t_{i,j,k})` with
`t_{i,j,k} = −t_{j,i,k}` and `t_{i,i,k} = 0`. -/
def IsAltTensor {n m : ℕ} (T : Fin n → Fin n → Fin m → R) : Prop :=
  (∀ i j k, T i j k = -T j i k) ∧ ∀ i k, T i i k = 0

/-- **`(X, Y, Z) ∘ T`** (§2.3, p. 10): `t'_{i,j,k} = Σ_{i',j',k'} X_{i,i'} Y_{j,j'} Z_{k,k'} t_{i',j',k'}`. -/
def actT {n m : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin m) (Fin m) R)
    (T : Fin n → Fin n → Fin m → R) : Fin n → Fin n → Fin m → R :=
  fun i j k => ∑ i', ∑ j', ∑ k', X i i' * Y j j' * Z k k' * T i' j' k'

/-- `N_{T,x⃗} = Σ_i x_i N_{T,i}`, the `n × m` matrix with `N_{T,i}[j,k] = t_{i,j,k}` (§2.3, p. 10). -/
def NT {n m : ℕ} (T : Fin n → Fin n → Fin m → R) (x : Fin n → R) : Matrix (Fin n) (Fin m) R :=
  fun j k => ∑ i, x i * T i j k

/-- `M_{T,y⃗} = Σ_k y_k M_{T,k}`, the `n × n` matrix with `M_{T,k}[i,j] = t_{i,j,k}` (§2.3, p. 10). -/
def MT {n m : ℕ} (T : Fin n → Fin n → Fin m → R) (y : Fin m → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ∑ k, y k * T i j k

/-- **The complex parameter** `c_T = c_{T,0} + c_{T,1}` (§2.3, p. 10): `p^{c_{T,0}}` is the number of
distinct matrices `N_{T,x⃗}` and `p^{c_{T,1}}` the number of distinct `M_{T,y⃗}` (both numbers are powers
of `p` over `R = Z/p^τZ`, so the base-`p` logarithm is exact). -/
def cT (p : ℕ) {n m : ℕ} (T : Fin n → Fin n → Fin m → R) : ℕ :=
  Nat.log p (Set.range (NT T)).ncard + Nat.log p (Set.range (MT T)).ncard

/-- **Input instance of the restricted alternating tensor isomorphism problem** with parameter `w`
(§2.3, p. 10): `T, T'` alternating, and `P ∈ M(d × n, R)` such that (1) `P x⃗ = 0` implies that the
`(j,k)`-entry of `N_{T,x⃗}` is zero for all `j, k > w`; (2) `N_{T,x⃗} = 0` implies `P x⃗ = 0`.
(Indices are zero-based here: one-based `j > w` is zero-based `j ≥ w`.) -/
def IsRestrictedInstance {n m d : ℕ} (w : ℕ) (T T' : Fin n → Fin n → Fin m → R)
    (P : Matrix (Fin d) (Fin n) R) : Prop :=
  IsAltTensor T ∧ IsAltTensor T' ∧
  (∀ x : Fin n → R, P.mulVec x = 0 → ∀ j : Fin n, ∀ k : Fin m, w ≤ j.val → w ≤ k.val →
    NT T x j k = 0) ∧
  (∀ x : Fin n → R, NT T x = 0 → P.mulVec x = 0)

/-- **A solution of the restricted alternating tensor isomorphism problem** (§2.3, p. 10): invertible
`X, Y` with `(X, X, Y) ∘ T = T'` and `P · Xᵀ = P'`. -/
def IsRestrictedSolution {n m d : ℕ} (T T' : Fin n → Fin n → Fin m → R)
    (P P' : Matrix (Fin d) (Fin n) R) (X : GL (Fin n) R) (Y : GL (Fin m) R) : Prop :=
  actT (X : Matrix (Fin n) (Fin n) R) X Y T = T' ∧ P * (X : Matrix (Fin n) (Fin n) R).transpose = P'

/-- **Alternating matrix** (§2.1, p. 8): zero diagonal and `Aᵀ = −A`. -/
def IsAltMat {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop := A.transpose = -A ∧ ∀ i, A i i = 0

/-- Non-degeneracy of a rectangular matrix tuple (§2.1, PDF p. 10): no invertible
left and right transformations produce a common zero row or a common zero column. -/
def NondegenerateTuple {a b k : ℕ} (A : Fin k → Matrix (Fin a) (Fin b) R) : Prop :=
  (∀ (X : GL (Fin a) R) (Y : GL (Fin b) R) (i : Fin a),
    ∃ t j, ((X : Matrix (Fin a) (Fin a) R) * A t * (Y : Matrix (Fin b) (Fin b) R)) i j ≠ 0) ∧
  (∀ (X : GL (Fin a) R) (Y : GL (Fin b) R) (j : Fin b),
    ∃ t i, ((X : Matrix (Fin a) (Fin a) R) * A t * (Y : Matrix (Fin b) (Fin b) R)) i j ≠ 0)

/-- The standing non-degeneracy convention applied to the slice tuple `(N_{T,i})_i`. -/
def NondegenerateTensor {n m : ℕ} (T : Fin n → Fin n → Fin m → R) : Prop :=
  NondegenerateTuple (fun i => fun j k => T i j k)

/-- **Congruence of matrix tuples** (§2.1, p. 9): some `P ∈ GL(n, R)` has `Pᵀ A_i P = B_i` for every `i`. -/
def Congruent {n m : ℕ} (A B : Fin m → Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ P : GL (Fin n) R, ∀ i, (P : Matrix (Fin n) (Fin n) R).transpose * A i * P = B i

/-- **The (invertible) automorphism group** of a matrix tuple, as a set: `{P ∈ GL(n,R) : Pᵀ A P = A}`. -/
def autSet {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) R) : Set (GL (Fin n) R) :=
  {P | ∀ i, (P : Matrix (Fin n) (Fin n) R).transpose * A i * P = A i}

/-! ### Codes over `R = Z/p^τZ` -/

/-- A matrix over `Z/qZ`: its entries in row-major order, each in `[0, q)`. -/
def encMat {q a b : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod q)) : List Bool :=
  (List.ofFn fun i => (List.ofFn fun j => encZMod (A i j)).flatten).flatten

/-- A tuple of `m` square matrices. -/
def encTuple {q n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) (ZMod q)) : List Bool :=
  (List.ofFn fun i => encMat (A i)).flatten

/-- An `n × n × m` tensor over `Z/qZ`, entries in the order `(i, j, k)`. -/
def encTensor {q n m : ℕ} (T : Fin n → Fin n → Fin m → ZMod q) : List Bool :=
  (List.ofFn fun i => (List.ofFn fun j => (List.ofFn fun k => encZMod (T i j k)).flatten).flatten).flatten

/-- The header `p, τ, n, m` of an input over `Z/p^τZ`. -/
def encHeader (p τ n m : ℕ) : List Bool := encodeNat p ++ encodeNat τ ++ encodeNat n ++ encodeNat m

end SunGroupIso.Class2


