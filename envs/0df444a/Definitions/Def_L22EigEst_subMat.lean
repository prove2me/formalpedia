-- Prove2me | Definitions.Def_L22EigEst_subMat
-- name    : L22EigEst_subMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:16:13.985192+00:00
-- url     : https://prove2.me/theorems/10dffd7c-b063-4047-8d74-ee5c0d4aa27c
-- title:
--   The sub-sampled matrix $M$ of equation (3) and its query count
-- statement:
--   Let $B$ be a real $n\times n$ matrix (in Algorithm 1, $B=SA'S^\top$), $q\in(0,1)$, and let $\xi_{ij}\in\{0,1\}$ be coins indexed by the pairs $i<j$. The matrix $M$ of equation (3) is symmetric with
--
--   $$M_{ij}=\begin{cases}B_{ii}& i=j,\\ B_{ij}/q & i\ne j\text{ and }\xi_{ij}=1,\\ 0&\text{otherwise,}\end{cases}$$
--
--   where for $i>j$ the coin and entry of the pair $(j,i)$ are used. The **number of queried entries** for a sampling pattern $\delta$ and coins $\xi$ is the number of sampled rows plus the number of sampled pairs $i<j$ with $\xi_{ij}=1$: Algorithm 1 "need only query the entries of $SA'S^\top$ along the diagonal or where $\xi_{ij}=1$".
--
--   **Formalization Note** In the $n\times n$ view the rows and columns of $M$ off the sample are zero, so the $n$ eigenvalues of $M$ are its $|S|$ eigenvalues on the sample and $n-|S|$ zeros, which is the output of Algorithm 1. The module proves that $M$ is symmetric.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Algorithm 1 (Figure 1), p.11, eq. (3); proof of Lemma 4.7, p.24

import Definitions.Def_L22EigEst_sampMat

namespace L22EigEst

/-- The index set `{(i, j) : i < j}` of the coin flips `ξ_ij` of Algorithm 1 (Figure 1, p.11:
"sampling ξ_ij ∼ Ber(q) for each i < j"). -/
abbrev Pair (n : ℕ) : Type :=
  {x : Fin n × Fin n // x.1 < x.2}

/-- **The sub-sampled matrix `M` of equation (3)** (Algorithm 1, Figure 1, p.11), Menand,
Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), applied to `B = SA′S⊺`:
`M_ii = B_ii`; `M_ij = B_ij/q` if `i ≠ j` and `ξ_ij = 1`; `0` otherwise, with `M_ij = M_ji`.

**Formalization Note.** `n × n` view (p.9): rows and columns off the sample are zero because those
of `B` are. One coin `ξ` per pair `i < j`; the entry at `(i, j)` and at `(j, i)` both use the coin
of the ordered pair `(min, max)` and the entry `B_{min,max}`, so `M` is symmetric by construction. -/
noncomputable def subMat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) (ξ : Pair n → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then B i i
    else if h : i < j then (if ξ ⟨(i, j), h⟩ then B i j / q else 0)
    else if h' : j < i then (if ξ ⟨(j, i), h'⟩ then B j i / q else 0)
    else 0

/-- **The number of entries queried to form `M`** (Algorithm 1, p.11: "the algorithm need only
query the entries of SA′S⊺ along the diagonal or where ξ_ij = 1"; proof of Lemma 4.7, p.24): the
sampled diagonal positions plus the sampled pairs `i < j` with `ξ_ij = 1`. -/
def queries {n : ℕ} (δ : Fin n → Bool) (ξ : Pair n → Bool) : ℕ :=
  sampCount δ +
    (Finset.univ.filter (fun x : Pair n => δ x.1.1 = true ∧ δ x.1.2 = true ∧ ξ x = true)).card

theorem subMat_isHermitian {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) (ξ : Pair n → Bool) :
    (subMat B q ξ).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, subMat]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : ¬ j = i := fun e => hij e.symm
    rcases lt_or_gt_of_ne hij with h | h
    · have hn : ¬ j < i := not_lt.mpr h.le
      simp [hij, hji, h, hn]
    · have hn : ¬ i < j := not_lt.mpr h.le
      simp [hij, hji, h, hn]

end L22EigEst


