-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_Schur
-- name    : CommutativeRankNC_Approximation_Schur
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:29.709801+00:00
-- url     : https://prove2.me/theorems/d46e8172-6fa1-4cd7-bdf4-7549fbc9173f
-- title:
--   Normalized Schur coefficients, truncation and polarization
-- statement:
--   Normalize a rational matrix $A$ of rank $r$ by shared invertible row and column maps to $\operatorname{diag}(I_r,0)$. Write a transformed direction in blocks $\left[\begin{smallmatrix}X&Q\\P&Z\end{smallmatrix}\right]$. The coefficient matrices are
--
--   $$h_0=Z,\qquad h_j=(-1)^jPX^{j-1}Q\quad(j\ge1).$$
--
--   The lower block Toeplitz matrix $J_k$ has block $h_{u-v}$ for $v\le u<k$ and zero otherwise. Both scalar and polynomial directions use this same normalization. The actual series $H=\sum_jt^jh_j$ lies in $\mathbb Q(x)[[t]]$; Smith data are units $U,V$ and ordered exponents satisfying $UHV=\operatorname{diag}(t^{\nu_i},0)$ in that ring. Homogenization replaces $h_j$ by $z^{k-j-1}h_j$; complete polarization uses the alternating subset sum without dividing by $k!$. Bucket degree is defined by monomial support, including zero entries. These are analysis objects, not computational advice.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), §§2.1, 4, 5.2, pp.7–9, 15–20, 24–27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_MatrixSpace

noncomputable section

namespace CommutativeRankNC.Approximation

/-- Rank normalization by the same invertible rational row/column maps for A
and every direction. Existence is part of the theorem layer, not an input to
the headline algorithm. -/
structure Normalization {n : ℕ} (A : QMatrix n) where
  r : ℕ
  le : r ≤ n
  rank_eq : A.rank = r
  left : (QMatrix n)ˣ
  right : (QMatrix n)ˣ
  normal : (left : QMatrix n) * A * (right : QMatrix n) =
    fun i j => if i = j ∧ i.val < r then 1 else 0

def topIndex {n r : ℕ} (hr : r ≤ n) (i : Fin r) : Fin n := i.castLE hr
def bottomIndex {n r : ℕ} (hr : r ≤ n) (i : Fin (n - r)) : Fin n :=
  ⟨r + i.val, by omega⟩

/-- Coefficient h_j in Z-tP(I+tX)⁻¹Q, with the displayed sign and index. -/
def schurCoefficient {R : Type*} [CommRing R] {n r : ℕ} (hr : r ≤ n)
    (C : Matrix (Fin n) (Fin n) R) (j : ℕ) : Matrix (Fin (n-r)) (Fin (n-r)) R :=
  let X := C.submatrix (topIndex hr) (topIndex hr)
  let Q := C.submatrix (topIndex hr) (bottomIndex hr)
  let P := C.submatrix (bottomIndex hr) (topIndex hr)
  let Z := C.submatrix (bottomIndex hr) (bottomIndex hr)
  if j = 0 then Z else (-1 : R) ^ j • (P * X ^ (j-1) * Q)

def truncatedSchur {R : Type*} [CommRing R] {n r : ℕ} (hr : r ≤ n)
    (C : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Matrix (Fin k × Fin (n-r)) (Fin k × Fin (n-r)) R :=
  fun u v => if v.1 ≤ u.1 then schurCoefficient hr C (u.1.val-v.1.val) u.2 v.2 else 0

def polynomialPencil {n m : ℕ} (B : Fin m → QMatrix n) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℚ) :=
  fun u v => ∑ i, MvPolynomial.X i * MvPolynomial.C (B i u v)

def normalizedTuple {n m : ℕ} {A : QMatrix n} (S : Normalization A)
    (B : Fin m → QMatrix n) : Fin m → QMatrix n :=
  fun i => (S.left : QMatrix n) * B i * (S.right : QMatrix n)

def scalarJ {n : ℕ} {A : QMatrix n} (S : Normalization A) (C : QMatrix n) (k : ℕ) :=
  truncatedSchur S.le ((S.left : QMatrix n) * C * (S.right : QMatrix n)) k

def polynomialJ {n m : ℕ} {A : QMatrix n} (S : Normalization A)
    (B : Fin m → QMatrix n) (k : ℕ) :=
  truncatedSchur S.le (polynomialPencil (normalizedTuple S B)) k

noncomputable def genericJ {n m : ℕ} {A : QMatrix n} (S : Normalization A)
    (B : Fin m → QMatrix n) (k : ℕ) :=
  (polynomialJ S B k).map (algebraMap _ (RationalFunctions m))

/-- The actual power-series matrix; no independent free list of Smith exponents. -/
noncomputable def schurSeries {n m : ℕ} {A : QMatrix n} (S : Normalization A)
    (B : Fin m → QMatrix n) :
    Matrix (Fin (n-S.r)) (Fin (n-S.r)) (PowerSeries (RationalFunctions m)) :=
  fun i j => PowerSeries.mk fun d => algebraMap _ _
    (schurCoefficient S.le (polynomialPencil (normalizedTuple S B)) d i j)

/-- Genuine Smith decomposition over K[[t]], with nonzero invariant factors
exactly t^ν and every remaining diagonal entry zero. -/
def IsSmithDecomposition {K : Type*} [Field K] {s d : ℕ}
    (H : Matrix (Fin s) (Fin s) (PowerSeries K)) (ν : Fin d → ℕ)
    (U V : (Matrix (Fin s) (Fin s) (PowerSeries K))ˣ) : Prop :=
  d ≤ s ∧ Monotone ν ∧ (U : Matrix _ _ _) * H * (V : Matrix _ _ _) =
    fun i j => if h : i = j ∧ i.val < d then PowerSeries.X ^ (ν ⟨i.val, h.2⟩) else 0

/-- Generic rank of the actual affine pencil over K(t). -/
noncomputable def affinePencil {K : Type*} [Field K] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (FractionRing (Polynomial K)) :=
  fun i j => algebraMap _ _ (Polynomial.C (A i j) + Polynomial.X * Polynomial.C (C i j))

def homogenizedJ {n m : ℕ} {A : QMatrix n} (S : Normalization A)
    (B : Fin m → QMatrix n) (k : ℕ) :
    Matrix (Fin k × Fin (n-S.r)) (Fin k × Fin (n-S.r)) (MvPolynomial (Fin (m+1)) ℚ) :=
  fun u v => if v.1 ≤ u.1 then
    MvPolynomial.X 0 ^ (k - (u.1.val-v.1.val) - 1) *
      MvPolynomial.rename Fin.succ
        (schurCoefficient S.le (polynomialPencil (normalizedTuple S B))
          (u.1.val-v.1.val) u.2 v.2)
    else 0

/-- Unnormalized complete polarization, with diagonal value k! times the
original homogeneous polynomial. -/
def polarize {s : ℕ} (k : ℕ) (p : MvPolynomial (Fin s) ℚ) :
    MvPolynomial (Fin k × Fin s) ℚ :=
  ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
    (-1 : MvPolynomial (Fin k × Fin s) ℚ) ^ (k-S.card) *
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i => ∑ j ∈ S, MvPolynomial.X (j,i)) p

def polarizedJ {n m : ℕ} {A : QMatrix n} (S : Normalization A)
    (B : Fin m → QMatrix n) (k : ℕ) := (homogenizedJ S B k).map (polarize k)

noncomputable def polynomialMatrixRank {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Type*} (M : Matrix ι ι (MvPolynomial σ ℚ)) : ℕ :=
  (M.map (algebraMap _ (FractionRing (MvPolynomial σ ℚ)))).rank

/-- Homogeneous degree one in one whole bucket: every supported monomial has
bucket degree one. Zero polynomials satisfy the same convention. -/
def BucketLinear {k s : ℕ} (p : MvPolynomial (Fin k × Fin s) ℚ) (bucket : Fin k) : Prop :=
  ∀ a ∈ p.support, ∑ i : Fin s, a (bucket,i) = 1

end CommutativeRankNC.Approximation


