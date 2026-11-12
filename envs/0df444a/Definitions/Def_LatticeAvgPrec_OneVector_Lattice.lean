-- Prove2me | Definitions.Def_LatticeAvgPrec_OneVector_Lattice
-- name    : LatticeAvgPrec_OneVector_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:27.590121+00:00
-- url     : https://prove2.me/theorems/5fa9d0e0-6178-4091-8afb-4f96ff00d719
-- title:
--   Bitlength, total row bitlength $L$, column lattice $\Lambda(B)$ and successive minima $\lambda_i$
-- statement:
--   For an integer $z$, $\operatorname{bits}(z)=1+\lceil\log_2(1+|z|)\rceil$ (§2, p.8). The bitlength of row $i$ of $B\in\mathbb Z^{n\times m}$ is $h_i=\max_j\operatorname{bits}(B_{ij})$, and the total row bitlength is
--   $$L=\sum_i h_i$$
--   (p.3). Since $\operatorname{bits}\ge1$, $L\ge n$ whenever $m\ge1$.
--
--   The column lattice is $\Lambda(B)=B\mathbb Z^m$, here a set of integer vectors; vectors carry the Euclidean norm $\|v\|_2=(\sum_i v_i^2)^{1/2}$, and $\|Y_j\|_2$ denotes the norm of column $j$. The $i$-th successive minimum $\lambda_i(\Lambda)$ is "the least radius containing $i$ independent lattice vectors" (p.4): the infimum of the radii $r\ge0$ for which $\Lambda$ contains $i$ vectors, linearly independent over $\mathbb R$, of norm at most $r$.
--
--   These are the size and quality measures in every statement of the mission.
--
--   **Formalization Note** $\lceil\log_2 m\rceil$ is `Nat.clog 2 m`. $\lambda_i$ is an `sInf` over a set of radii that is nonempty and bounded below for a full-rank lattice and $1\le i\le n$; for $i$ larger than the rank the set is empty and the value is $0$, a case no statement uses.
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), §1 p.3 (h_i, L); §1.1.1 p.4 (Λ(B), λ_i); §2 p.8 (bits, column lattices, Euclidean norm)

import Definitions.Def_LatticeAvgPrec_OneVector_Encoding
open Matrix

namespace LatticeAvgPrec.OneVector

/-- Signed bitlength (§2, p.8): `bits(z) = 1 + ⌈log₂(1 + |z|)⌉`. `Nat.clog 2 m` is `⌈log₂ m⌉` for
`m ≥ 1`. -/
def bits (z : ℤ) : ℕ := 1 + Nat.clog 2 (1 + z.natAbs)

/-- The bitlength of row `i` of `B`: the largest signed entry bitlength in that row. -/
def rowBits {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℤ) (i : Fin n) : ℕ :=
  Finset.univ.sup (fun j => bits (B i j))

/-- Total row bitlength `L = Σ_i h_i` (p.3). -/
def totalRowBits {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℤ) : ℕ :=
  ∑ i, rowBits B i

/-- The column lattice `Λ(B) = B ℤ^m`, as a set of integer vectors. -/
def lat {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℤ) : Set (Fin n → ℤ) :=
  Set.range (fun x : Fin m → ℤ => B *ᵥ x)

/-- Euclidean norm of a real vector. -/
noncomputable def l2 {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Euclidean norm of an integer vector. -/
noncomputable def ivNorm {n : ℕ} (v : Fin n → ℤ) : ℝ := Real.sqrt (∑ i, ((v i : ℝ)) ^ 2)

/-- Euclidean norm of column `j` of an integer matrix. -/
noncomputable def colNorm {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℤ) (j : Fin m) : ℝ :=
  ivNorm (fun t => Y t j)

/-- The `i`-th successive minimum `λ_i(Λ)` (p.4): the least radius `r ≥ 0` such that `Λ` contains
`i` linearly independent vectors of Euclidean length at most `r`. For a full-rank lattice in `ℤ^n`
and `1 ≤ i ≤ n` the set is nonempty and bounded below, and the infimum is attained. -/
noncomputable def lam {n : ℕ} (Λ : Set (Fin n → ℤ)) (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ vs : Fin i → Fin n → ℤ, (∀ j, vs j ∈ Λ) ∧
    LinearIndependent ℝ (fun j => fun t => ((vs j t : ℤ) : ℝ)) ∧ ∀ j, ivNorm (vs j) ≤ r}

end LatticeAvgPrec.OneVector


