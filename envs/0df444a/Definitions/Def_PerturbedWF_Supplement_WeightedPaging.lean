-- Prove2me | Definitions.Def_PerturbedWF_Supplement_WeightedPaging
-- name    : PerturbedWF_Supplement_WeightedPaging
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:06:25.867745+00:00
-- url     : https://prove2.me/theorems/ab4536d1-7df1-44bc-b8c0-101bfaf46e8e
-- title:
--   Weighted paging: the distance $d(i,j)=w_i+w_j$, the matrix $A=\mathrm{diag}(w)$ and $\kappa=(k+1)\ln(k+1)$
-- statement:
--   In **weighted paging** there are $n$ pages with weights $w_i\ge0$ and a cache of size $k$; a configuration $x\in\{x\in\mathbb Z^n_{\ge0}:\sum_ix_i=k\}$ is the cache content (multisets are admitted). The distance between pages $i\ne j$ is
--   $$d(i,j)=w_i+w_j,\qquad d(i,i)=0,$$
--   so that $\|x-y\|=\sum_i w_i|x_i-y_i|$ on configurations. The algorithm of §8.2.1 uses $A=\mathrm{diag}(w)$ (so $v_i=w_iq_i$) and draws each $q_i$ independently with the density (8.2) for
--   $$\kappa=(k+1)\ln(k+1).$$
--
--   **Formalization Note** Weights may be $0$; then $d$ is not positive off the diagonal, which the transportation norm does not need.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §8.2 'Weighted paging', p.21 (PDF p.22); §8.2.1 'Algorithm', p.22 (PDF p.23)

import Mathlib
import Definitions.Def_PerturbedWF_Supplement_KServer

namespace PerturbedWF.Supplement

/-!
# Weighted paging: the weighted-star distance, `A = diag(w)` and `κ` (§8.2, §8.2.1)

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §8.2 "Weighted paging", p.21 (PDF p.22) and §8.2.1
"Algorithm", p.22 (PDF p.23).

There are `n` pages with weights `w_i ≥ 0` and a cache of size `k` (a configuration in
`kConfig ι k`; multisets are allowed, footnote 2). The distance between pages `i ≠ j` is
`d(i, j) = w_i + w_j`, so that `‖x − y‖ = ∑_i w_i |x_i − y_i|` on configurations. The algorithm of
§8.2.1 samples `q_i` i.i.d. with the density (8.2) for `κ = (k + 1) ln(k + 1)` and sets
`v = Aq` with `A = diag(w)`.

**Formalization Note.** Weights may be `0` (the reduction of Theorem 8.4 uses a page of weight
`0`), so `wpDist w` need not be positive off the diagonal; it is used directly in `transNorm`.
-/

/-- The weighted-paging distance `d(i, j) = w_i + w_j` for `i ≠ j`, `d(i, i) = 0`. -/
def wpDist {ι : Type} [DecidableEq ι] (w : ι → ℝ) (i j : ι) : ℝ :=
  if i = j then 0 else w i + w j

/-- The matrix `A = diag(w)`, indexed by pages on both sides. -/
def wpMatrix {ι : Type} [DecidableEq ι] (w : ι → ℝ) (i e : ι) : ℝ :=
  if i = e then w i else 0

/-- The parameter `κ = (k + 1) ln(k + 1)` of §8.2.1. -/
noncomputable def wpKappa (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)

end PerturbedWF.Supplement


