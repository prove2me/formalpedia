-- Prove2me | Definitions.Def_TinyCoreset_Affine_Setting
-- name    : TinyCoreset_Affine_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:44:32.249032+00:00
-- url     : https://prove2.me/theorems/1e268d9e-6b16-4fa5-a3cc-469a986c0464
-- title:
--   §2, §3 and §4, pp. 603–616 — squared distances, mean row, Σ^(m), and the outputs of Algorithms 1 and 2
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ be a data matrix whose rows $A_{1*},\ldots,A_{n*}$ are points of $\mathbb R^d$. This file fixes the objects of the affine $j$-subspace coreset construction.
--
--   1. **Distances.** For a set $C\subseteq\mathbb R^d$ and a point $p$, $\operatorname{dist}(p,C)=\inf_{c\in C}\|p-c\|_2$. The cost of $C$ is the sum of squared row distances, and for nonnegative weights $w_1,\ldots,w_r$ on the rows of a matrix $S\in\mathbb R^{r\times d}$ its weighted form is
--   $$\operatorname{dist}^2(A,C)=\sum_{i=1}^n\operatorname{dist}^2(A_{i*},C),\qquad \operatorname{dist}^2_w(S,C)=\sum_{i=1}^r w_i\operatorname{dist}^2(S_{i*},C).$$
--   2. **Frobenius norm and singular values.** $\|M\|_F^2=\sum_{i,k}M_{ik}^2$. For the rectangular diagonal factor $\Sigma$ of a singular value decomposition $A=U\Sigma V^T$, $\sigma_i=\Sigma_{i,i}$ for $1\le i\le\min\{n,d\}$, and $\sigma_i=0$ otherwise.
--   3. **Mean and centring.** The mean row is $\mu(A)=\frac1n\sum_{i=1}^n A_{i*}$, and the centred matrix is $A'=A-\mathbb 1\cdot\mu(A)$, with rows $A_{i*}-\mu(A)$.
--   4. **Truncation.** $\Sigma^{(m)}$ is the $n\times d$ matrix that keeps the first $m$ diagonal entries of $\Sigma$ and is zero elsewhere, so the $m$-rank approximation is $A^{(m)}=U\Sigma^{(m)}V^T$.
--   5. **Algorithm 1 (subspace-Coreset$(A,j,\varepsilon)$).** It sets
--   $$m=\min\{n,\ d,\ j+\lceil j/\varepsilon\rceil-1\},$$
--   takes as coreset $S'$ the matrix of the first $m$ rows of $\Sigma^{(m)}V^T$ (all further rows are zero), each with weight $1$, and $\Delta=\|A-A^{(m)}\|_F^2$.
--   6. **Algorithm 2 (affine-$j$-subspace-Coreset$(A,j,\varepsilon)$).** It runs Algorithm 1 on $A'$ and outputs the $2m$ points
--   $$S=\mathbb 1\cdot\mu(A)+\sqrt{\frac mn}\cdot\begin{bmatrix}S'\\-S'\end{bmatrix},$$
--   each with weight $n/(2m)$. With $\mu(A)$ replaced by $0$ this is the matrix $S''=\sqrt{m/n}\,[S';-S']$ of the proof of Theorem 19.
--
--   These are the objects about which Theorems 17 and 19 make their coreset guarantees.
--
--   **Formalization Note** The SVD and $A^{(m)}$ are the published `ProjLikeRetr.FixedRank.IsSVD` and `truncSVD`; `truncSigma` is the middle factor of `truncSVD` (equal by definition). Diagonal positions of $\Sigma$ are 0-based in Lean (`truncSigma m` keeps positions $<m$), while `sigma` is 1-based as on p. 603. Mathlib's distance to the empty set is $0$ (the paper has $\infty$), so statements only use nonempty sets. The natural-number subtraction in $j+\lceil j/\varepsilon\rceil-1$ is exact because $j\ge1$ in every use. For $n=0$, Lean's $1/0=0$ makes $\mu(A)=0$; Algorithm 2 is only used with $n\ge1$. The rows of the $2m$-point output are ordered $\mu+\sqrt{m/n}\,S'_{i*}$ ($i=1,\ldots,m$) and then $\mu-\sqrt{m/n}\,S'_{i*}$. The helpers `row`, `distSq`, `wDistSq`, `frobSq`, `sigma` (items 1 and 2) are not redefined here: they are imported from the shared module `TinyCoreset.DimRed.Setting`.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), pp. 603–605 (§2, Definition 1), p. 615 (text before Theorem 17, Algorithm 1), p. 616 (§4, Algorithm 2)

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.Affine

open scoped Matrix

/-- Algorithm 2, line 1, p. 616: the mean row `µ(A) = (1/n) Σ_{i=1}^n A_{i*}`. (For `n = 0` Lean's
`1 / 0 = 0` makes it `0`; Algorithm 2 is only run with `n ≥ 1`.) -/
noncomputable def mean {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : Fin d → ℝ :=
  fun k => (1 / (n : ℝ)) * ∑ i, A i k

/-- §4, p. 616 and Algorithm 2, line 2: the centred matrix `A′ = A − 𝟙 · µ(A)`, whose rows are
`A_{i*} − µ(A)`. -/
noncomputable def center {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun i k => A i k - mean A k

/-- Algorithm 1, line 1, p. 615: the coreset size `m = min{n, d, j + ⌈j/ε⌉ − 1}`. The natural-number
subtraction is exact in every use, since there `j ≥ 1`. -/
noncomputable def coresetSize (n d j : ℕ) (ε : ℝ) : ℕ :=
  min n (min d (j + ⌈(j : ℝ) / ε⌉₊ - 1))

/-- The coreset size never exceeds the number of input points (structural). -/
theorem coresetSize_le (n d j : ℕ) (ε : ℝ) : coresetSize n d j ε ≤ n :=
  min_le_left _ _

/-- Definition 1, p. 604: `Σ^(m)`, the `n × d` matrix that keeps the first `m` diagonal entries of `S`
(0-based diagonal positions `< m`) and is `0` elsewhere. It is the middle factor of the published
`truncSVD`, so `truncSVD m U S V = U * truncSigma m S * Vᵀ`. -/
def truncSigma {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun a b => if a.val = b.val ∧ a.val < m then S a b else 0

/-- Algorithm 1, line 3, with the text before Theorem 17 (p. 615): the coreset `S` of
`subspace-Coreset`, the matrix consisting of the first `m` rows of `Σ^(m) Vᵀ` (the remaining rows of
`Σ^(m) Vᵀ` are zero). -/
def subspaceCoresetRows {n d : ℕ} (m : ℕ) (hm : m ≤ n) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  fun i => (truncSigma m S * Vᵀ) (Fin.castLE hm i)

/-- Algorithm 2, line 3, p. 616: `S = 𝟙 · µ + √(m/n) · [S′; −S′]`, the `2m` points `µ + √(m/n) S′_{i*}`
(rows `0, …, m−1`) followed by `µ − √(m/n) S′_{i*}` (rows `m, …, 2m−1`). With `mu = 0` it is the
matrix `S″ = √(m/n) · [S′; −S′]` of the proof of Theorem 19 (p. 618). -/
noncomputable def affineCoresetRows {m d : ℕ} (n : ℕ) (mu : Fin d → ℝ)
    (S' : Matrix (Fin m) (Fin d) ℝ) : Matrix (Fin (m + m)) (Fin d) ℝ :=
  Fin.append (fun i k => mu k + Real.sqrt ((m : ℝ) / (n : ℝ)) * S' i k)
    (fun i k => mu k - Real.sqrt ((m : ℝ) / (n : ℝ)) * S' i k)

/-- Algorithm 2, line 4, p. 616: the common weight `n/(2m)` of the `2m` coreset points. -/
noncomputable def affineWeight (n m : ℕ) : ℝ :=
  (n : ℝ) / (2 * (m : ℝ))

end TinyCoreset.Affine


