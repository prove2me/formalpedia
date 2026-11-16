-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_PolynomialMatrices
-- name    : DetSupportRank_DeterminantSupport_Supplement_PolynomialMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:34.23109+00:00
-- url     : https://prove2.me/theorems/78b69da1-4c19-48a4-81fc-2d05ea589064
-- title:
--   Formal variable matrices, ordered minors and scalar congruence
-- statement:
--   The rectangular variable matrix has entries $X_{ij}=x_{i,j}$ in the formal polynomial ring $F[x_{i,j}]$. Define its square determinant, its ordered square minors, and the independent column-minor sums
--   $$\det_n(X)=\det(X),\qquad M_{I,k}(X)=\sum_{|J|=k}\det(X_{I,J}).$$
--   The source uses $|I|=k$; unequal-size minors have the previously documented zero extension. Also define $S_r=\{0,r\}$ and the actual polynomial matrix $XKX^{\mathsf T}$ by mapping scalar entries of $K$ into constant polynomials and multiplying matrices. When $n=0$, the total definition of $S_r$ has no possible input $r$. These constructors make no determinant, partition-rank, or multilinearity assertion.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §2 and §4.2, matrix notation and Observation 4.7, p. 5, 10–11 (PDF p. 5, 10–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_OrderedSubmatrices

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- The rectangular matrix of actual formal variables; §2, p.5. -/
def variableMatrix (F : Type*) [CommRing F] (d n : ℕ) :
    Matrix (Fin d) (Fin n) (MvPolynomial (Fin d × Fin n) F) :=
  fun i j => MvPolynomial.X (i, j)

/-- The actual formal determinant, never a function on finite-field inputs. -/
def determinantPolynomial (F : Type*) [CommRing F] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) F := Matrix.det (variableMatrix F n n)

/-- The ordered minor of the variable matrix. -/
def variableMinor {F : Type*} [CommRing F] {n : ℕ}
    (I J : Finset (Fin n)) : MvPolynomial (Fin n × Fin n) F :=
  determinantMinor (variableMatrix F n n) I J

/-- The paper's {1,i}, in zero-based indices. -/
def firstRowPair {n : ℕ} (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val = 0 ∨ j = r)

/-- All column minors of size k, summed independently of any other sum. -/
def sumColumnMinors {F : Type*} [CommRing F] {n : ℕ}
    (I : Finset (Fin n)) (k : ℕ) : MvPolynomial (Fin n × Fin n) F :=
  ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard k, variableMinor I J

/-- Actual scalar extension and matrix multiplication X K Xᵀ, pp.10-11. -/
def conjugatedMatrix {F : Type*} [CommRing F] {n : ℕ}
    (K : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) F) :=
  variableMatrix F n n * K.map MvPolynomial.C * (variableMatrix F n n).transpose
end DetSupportRank.DeterminantSupport.Supplement


