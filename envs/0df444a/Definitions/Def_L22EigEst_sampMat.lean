-- Prove2me | Definitions.Def_L22EigEst_sampMat
-- name    : L22EigEst_sampMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:12:24.57026+00:00
-- url     : https://prove2.me/theorems/a4e57182-6835-4acc-8359-fee1e8da14be
-- title:
--   Row-sampling matrix $S$, $S_{ii}=\delta_i/\sqrt{p_i}$, in the $n\times n$ view
-- statement:
--   Given probabilities $p_1,\dots,p_n$ and a sampling pattern $\delta\in\{0,1\}^n$, the **row-sampling matrix** is the $n\times n$ diagonal matrix
--
--   $$S=\mathrm{diag}\Big(\frac{\delta_1}{\sqrt{p_1}},\dots,\frac{\delta_n}{\sqrt{p_n}}\Big),$$
--
--   and $|S|=\#\{i:\delta_i=1\}$ is the number of sampled rows. The paper equally views $S$ as the $|S|\times n$ matrix of its non-zero rows; products such as $SAS^\top$ then change only by zero rows and columns, which affects neither their non-zero eigenvalues nor their column norms.
--
--   **Formalization Note** The $n\times n$ view is used throughout, so $SAS^\top=SAS$ is $n\times n$, with zero rows and columns off the sample. If $p_i=0$, Lean's $1/\sqrt0=0$ gives $S_{ii}=0$. The module also proves that $\mathrm{diag}(d)\,B\,\mathrm{diag}(d)$ is symmetric for symmetric $B$.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), §2, p.9

import Mathlib

namespace L22EigEst

/-- **The row-sampling matrix, `n × n` view**: the diagonal matrix with `S_ii = δ_i/√p_i`.
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), §2, p.9: "Equivalently, S
can be viewed as the n × n diagonal matrix with S_ii = δ_i/√p_i, whose non-zero rows are exactly the
rows above. … We use the two views interchangeably".

**Formalization Note.** `δ : Fin n → Bool` is the sampling pattern. The `n × n` view is used
throughout: `SAS⊺ = S * A * S` is `n × n`, with zero rows and columns off the sample. If `p_i = 0`
then Lean's `1/√0 = 0` makes `S_ii = 0`. -/
noncomputable def sampMat {n : ℕ} (p : Fin n → ℝ) (δ : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if δ i then 1 / Real.sqrt (p i) else 0)

/-- **The number of sampled rows** `|S| = #{i : δ_i = 1}` (bold **s** on p.11; §2, p.9:
"also write S for the set of sampled indices {i : δ_i = 1}, so that |S| = s"). -/
def sampCount {n : ℕ} (δ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => δ i = true)).card

/-- Conjugating a symmetric matrix by a real diagonal matrix gives a symmetric matrix. -/
theorem isHermitian_diag_conj {n : ℕ} (d : Fin n → ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) :
    (Matrix.diagonal d * B * Matrix.diagonal d).IsHermitian := by
  ext i j
  have h := congrFun (congrFun hB i) j
  rw [Matrix.conjTranspose_apply] at h
  simp only [star_trivial] at h
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [h]; ring

end L22EigEst


