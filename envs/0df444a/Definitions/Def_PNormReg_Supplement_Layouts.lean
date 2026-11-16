-- Prove2me | Definitions.Def_PNormReg_Supplement_Layouts
-- name    : PNormReg_Supplement_Layouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:51:03.86621+00:00
-- url     : https://prove2.me/theorems/88c32b1c-9bf9-49b1-9b5b-86821ce5a773
-- title:
--   Sparse and dense input layouts, $\mathrm{nnz}(A)$, and $\|\cdot\|_p$ for $p\in[1,\infty]$
-- statement:
--   For a matrix $A\in\mathbb R^{n\times d}$, $\mathrm{sparsity}(A)$ is the number of entries with $A_{ij}\ne0$ and
--
--   $$\mathrm{nnz}(A)=\mathrm{sparsity}(A)+n+d .$$
--
--   Two input layouts on the base mission's randomized real RAM are defined. In the **sparse layout**, integer memory holds $n$, $d$, the number $s$ of nonzero entries and then, for each nonzero entry in row-major order, its row and column index; real memory holds a header of scalar parameters, then the $s$ nonzero values in the same order, then one dense vector (such as $b$). In the **dense layout**, integer memory holds $n,d$ and real memory a header, then $A$ row by row, then one dense vector. The sparse layout is needed for running times of order $\mathrm{nnz}(A)$, which is less than the cost of reading a dense matrix.
--
--   For $p\in[1,\infty]$, passed as $p^{-1}\in[0,1]$ with $p^{-1}=0$ meaning $p=\infty$, $\|v\|_p$ is the sup norm at $p=\infty$ and the usual $\ell_p$ norm otherwise; $\|M\|_{p,2}$ is the $\ell_p$ norm of the vector of Euclidean row norms of $M$ (so $\|M\|_{\infty,2}=\max_i\|M_{i:}\|_2$), and $f_p(x)=\|Ax-b\|_p$ is the objective of problem (1). An output pair $(x,y)\in\mathbb R^d\times\mathbb R^n$ is read from real cells $-1-j$ and $-1-d-i$.
--
--   These are the input conventions of the supplement's running-time statements (Theorems 1, 3, 4, 6, 7, 8, 10).
--
--   **Formalization Note** The paper names no input format; the layouts are a reading, like the base mission's `goalInput`.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), nnz and ∥M∥_{p,s}, p.7; problem (1), p.1; 1/∞ = 0, pp.11, 15

import Mathlib
import Definitions.Def_PNormReg_InputLayout
import Definitions.Def_PNormReg_SMD

open Matrix

namespace PNormReg

namespace Supplement

/-!
# Sparse and dense input layouts, `nnz`, and norms indexed by `1/p`

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…): problem (1), p.1; `nnz(A)`, `∥M∥_{p,s}` and
`1/∞ = 0`, pp.7, 11 and 15.

**Formalization Note.**
* The paper names no input format; these layouts are a reading, like the base mission's
  `PNormReg.goalInput`. A bound in `nnz(A)` is below the cost of reading a dense matrix, so the
  theorems whose time is `nnz`-bounded (Theorems 3, 4, 10) read the matrix in the sparse layout.
* Sparse layout: integer memory holds `n, d, s` (the number of nonzero entries) and then, for each
  nonzero entry in row-major order, its row and its column index. Real memory holds a header of
  scalar parameters, then the `s` nonzero values in the same order, then one dense vector.
* Dense layout: integer memory `n, d`; real memory a header, `A` row-major, then one dense vector.
* `pInv` stands for `1/p ∈ [0, 1]`, with `pInv = 0` meaning `p = ∞` (p.15, "with 1/p = 0").
  `pNorm pInv` is `∥·∥_∞` at `pInv = 0` and `∥·∥_{1/pInv}` otherwise.
* `outputPair` reads a pair `(x, y) ∈ ℝ^d × ℝ^n` from real cells `−1 − j` (`x_j`) and
  `−1 − d − i` (`y_i`).
-/

/-- The nonzero entries of `A`, as positions in row-major order. -/
noncomputable def sparseEntries {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : List (Fin n × Fin d) :=
  open Classical in
  (List.finRange (n * d)).filterMap fun k =>
    if A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 ≠ 0 then
      some (finProdFinEquiv.symm k) else none

/-- `sparsity(A)`, the number of nonzero entries of `A` (p.7). -/
noncomputable def sparsity {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : ℕ :=
  open Classical in
  (Finset.univ.filter fun ij : Fin n × Fin d => A ij.1 ij.2 ≠ 0).card

/-- `nnz(A) := sparsity(A) + n + d` (p.7). -/
noncomputable def nnz {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : ℕ := sparsity A + n + d

/-- The sparse layout: integer memory `n, d, s, i₁, j₁, …, i_s, j_s`; real memory `header`, then the
values `A_{i₁j₁}, …, A_{i_sj_s}`, then `v`. -/
noncomputable def sparseInput {n d : ℕ} (header : List ℝ) (A : Matrix (Fin n) (Fin d) ℝ)
    (v : Fin n → ℝ) : State :=
  initState
    ([(n : ℤ), (d : ℤ), ((sparseEntries A).length : ℤ)] ++
      (sparseEntries A).flatMap fun ij => [((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)])
    (header ++ (sparseEntries A).map (fun ij => A ij.1 ij.2) ++ List.ofFn v)

/-- The dense layout: integer memory `n, d`; real memory `header`, then `A` row-major, then `v`. -/
noncomputable def denseInput {n d : ℕ} (header : List ℝ) (A : Matrix (Fin n) (Fin d) ℝ)
    (v : Fin n → ℝ) : State :=
  initState [(n : ℤ), (d : ℤ)] (header ++ rowMajor A ++ List.ofFn v)

/-- `∥v∥_p` for `p ∈ [1, ∞]` given by `pInv = 1/p`: the sup norm at `pInv = 0`, else `∥v∥_{1/pInv}`. -/
noncomputable def pNorm {n : ℕ} (pInv : ℝ) (v : Fin n → ℝ) : ℝ :=
  if pInv = 0 then linfNorm v else lpNorm (1 / pInv) v

/-- `∥M∥_{p,2}`, the `ℓ_p` norm of the row `ℓ₂` norms, for `p ∈ [1, ∞]` given by `pInv = 1/p`
(p.7: `∥M∥_{∞,2} = max_i ∥M_{i:}∥₂`). -/
noncomputable def rowNorm {n r : ℕ} (pInv : ℝ) (M : Matrix (Fin n) (Fin r) ℝ) : ℝ :=
  pNorm pInv (fun i => l2Norm (M i))

/-- The objective `f_p(x) = ∥Ax − b∥_p` of (1), `p = 1/pInv`. -/
noncomputable def fP {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (pInv : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  pNorm pInv (A *ᵥ x - b)

/-- The output pair: `x_j = mem(−1 − j)` for `j < d`, `y_i = mem(−1 − d − i)` for `i < n`. -/
noncomputable def outputPair (d n : ℕ) (s : State) : Pair d n :=
  (outputVec d s, fun i => s.core.mem (-1 - (d : ℤ) - (i : ℤ)))

end Supplement

end PNormReg


