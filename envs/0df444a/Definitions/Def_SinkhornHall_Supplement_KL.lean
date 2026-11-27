-- Prove2me | Definitions.Def_SinkhornHall_Supplement_KL
-- name    : SinkhornHall_Supplement_KL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:03:48.236607+00:00
-- url     : https://prove2.me/theorems/b8230453-bfad-53a2-b41a-c0f889b16607
-- title:
--   Matrix normalizations $R(A)$, $C(A)$, the Sinkhorn sequence $(M_k,N_k)$, the spaces $\mathcal M,\mathcal R,\mathcal C$ and problem (2.7)
-- statement:
--   Let $A$ be a real matrix with rows indexed by a finite set $I$ and columns by a finite set $J$, and let $r$, $c$ be vectors on $I$ and $J$. This bundle defines the matrix side of §2.2.
--
--   1. **Matrix normalizations.** $R(A)_{ij}=\dfrac{r_i}{(A\mathbf 1)_i}A_{ij}$ and $C(A)_{ij}=\dfrac{c_j}{(A^\top\mathbf 1)_j}A_{ij}$.
--   2. **Matrix KL divergence.** $D(N\|M)=\sum_{i,j}N_{ij}\log\dfrac{N_{ij}}{M_{ij}}$ with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$ (the vector divergence of the base mission applied to the matrices as vectors indexed by $I\times J$).
--   3. **Sinkhorn sequence (2.6).** $N_0=C(A)$, $M_k=R(N_k)$, $N_{k+1}=C(M_k)$.
--   4. **Spaces.** $\mathcal M=\{M: M_{ij}=0 \text{ where } A_{ij}=0,\ M_{ij}\ge0 \text{ where } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$, $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--   5. **Minimizer of (2.7)**: a pair $(M,N)\in\mathcal R\times\mathcal C$ with $D(N\|M)\le D(N'\|M')$ for all $(M',N')\in\mathcal R\times\mathcal C$.
--   6. **The polytope (2.9)** $\mathcal P=\{N\mathbf 1: N\in\mathcal C\}\subseteq\mathbb R^I$.
--   7. **$(r,c)$-scaling**: a matrix $B_{ij}=A_{ij}x_iy_j$ with positive $x$, $y$, $B\mathbf 1=r$ and $B^\top\mathbf 1=c$; $A$ is **$(r,c)$-scalable** if one exists.
--
--   These are the objects of the KL-minimization view of the Sinkhorn algorithm, shared by Proposition 2.8, Lemmas 2.9, 2.12, 2.13, Theorems 2.10, 3.4 and 3.6 and the §4.2 results.
--
--   **Formalization Note** Divisions use Lean's convention $x/0=0$: the paper leaves $R(A)$ undefined on a zero row (and $C(A)$ on a zero column), where the Lean versions put a zero row (column). On the Sinkhorn sequence of a nonnegative matrix without zero rows or columns and with positive marginals every denominator is positive. The divergence takes values in `EReal`.
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, §1 Notation p.4 (KL divergence, ⊕), §2 p.4 (scalings), p.6 (R(A), C(A)), §2.2 p.8 ((2.6), M, R, C, (2.7)), p.9 ((2.9))

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall.Supplement

/-!
Matrix side of §2.2 of Hayashi–Hirai–Sakabe, *Finding Hall blockers by matrix scaling*,
arXiv:2204.07425v2 (pp.4–9): the matrix normalizations `R(A)`, `C(A)` (p.6), the KL divergence of
two matrices (p.4, p.8), the Sinkhorn matrix sequence (2.6) (p.8), the spaces `M`, `R`, `C` and
the minimizers of (2.7) (p.8), the polytope `P` of (2.9) (p.9), and exact `(r, c)`-scalings (p.4).
-/

section General

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Row normalization of a matrix, `R(A)`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.6: "The row-normalization R(A) of A is a scaling
of A defined by R(A)_ij := (r_i/p_i)A_ij for p_i := (A1)_i."

**Formalization Note.** The paper leaves `R(A)` undefined when `A` has a zero row; Lean's
`x / 0 = 0` makes that row of `rowNormMat r A` zero. On the Sinkhorn sequence (2.6) of a
nonnegative matrix without zero rows or columns every row sum is positive and this value is never
reached. -/
noncomputable def rowNormMat (r : ι → ℝ) (A : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  fun i j => r i / (∑ j', A i j') * A i j

/-- **Column normalization of a matrix, `C(A)`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.6: "the column-normalization C(A) of A is a
scaling of A defined by C(A)_ij := (c_j/q_j)A_ij for q_j := (A⊤1)_j."

**Formalization Note.** As for `rowNormMat`: a zero column becomes a zero column. -/
noncomputable def colNormMat (c : κ → ℝ) (A : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  fun i j => c j / (∑ i', A i' j) * A i j

/-- **KL divergence of two matrices, `D(N‖M) = Σ_{i,j} N_ij log N_ij/M_ij`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (2.7), p.8, with the conventions of §1 Notation, p.4
(`0 log 0/x := 0`, `x log x/0 := ∞` for `x > 0`, sums may differ).

`matKL N M` is the base `klDiv` of the two matrices read as vectors indexed by `ι × κ`; it is `⊤`
exactly when some `M_ij = 0 < N_ij`. -/
noncomputable def matKL (N M : Matrix ι κ ℝ) : EReal :=
  SinkhornHall.klDiv (fun p : ι × κ => N p.1 p.2) (fun p : ι × κ => M p.1 p.2)

/-- **The Sinkhorn matrix sequence `N_k` of (2.6).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (2.6), p.8: "N_0 := C(A), M_k := R(N_k),
N_{k+1} := C(M_k)."

`sinkhornN A r c k` is `N_k`: `N_0 = C(A)` and `N_{k+1} = C(R(N_k))`.

**Formalization Note.** The marginals `r`, `c` are arbitrary (the statements assume them positive);
`R = C` is not assumed (§2.2, p.8: "In this section, we do not assume R = C"). -/
noncomputable def sinkhornN (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) : ℕ → Matrix ι κ ℝ
  | 0 => colNormMat c A
  | k + 1 => colNormMat c (rowNormMat r (sinkhornN A r c k))

/-- **The Sinkhorn matrix sequence `M_k := R(N_k)` of (2.6).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (2.6), p.8. -/
noncomputable def sinkhornM (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (k : ℕ) : Matrix ι κ ℝ :=
  rowNormMat r (sinkhornN A r c k)

/-- **The space `M`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2.2, p.8:
"M := {M ∈ ℝ^{n×m} | M_ij = 0 (i, j : A_ij = 0), M_ij ≥ 0 (i, j : A_ij > 0)}".

**Formalization Note.** The statements assume `A` nonnegative, so "`A_ij = 0`" and "`A_ij > 0`"
cover every entry; the definition is written with `A_ij = 0` and `0 < A_ij` as in the paper. -/
def supportSpace (A : Matrix ι κ ℝ) : Set (Matrix ι κ ℝ) :=
  {M | (∀ i j, A i j = 0 → M i j = 0) ∧ (∀ i j, 0 < A i j → 0 ≤ M i j)}

/-- **The space `R := {M ∈ M | M1 = r}`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2.2, p.8. -/
def rowSpace (A : Matrix ι κ ℝ) (r : ι → ℝ) : Set (Matrix ι κ ℝ) :=
  {M | M ∈ supportSpace A ∧ ∀ i, ∑ j, M i j = r i}

/-- **The space `C := {M ∈ M | M⊤1 = c}`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2.2, p.8. -/
def colSpace (A : Matrix ι κ ℝ) (c : κ → ℝ) : Set (Matrix ι κ ℝ) :=
  {M | M ∈ supportSpace A ∧ ∀ j, ∑ i, M i j = c j}

/-- **Minimizer of problem (2.7).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (2.7), p.8: "inf. D(N‖M) = Σ_{i,j} N_ij log N_ij/M_ij
s.t. M ∈ R, N ∈ C."

`IsMinimizer27 A r c M N` says `M ∈ R`, `N ∈ C` and `D(N‖M) ≤ D(N'‖M')` for all `M' ∈ R`,
`N' ∈ C` (the divergence valued in `EReal`). -/
def IsMinimizer27 (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (M N : Matrix ι κ ℝ) : Prop :=
  M ∈ rowSpace A r ∧ N ∈ colSpace A c ∧
    ∀ M' ∈ rowSpace A r, ∀ N' ∈ colSpace A c, matKL N M ≤ matKL N' M'

/-- **The polytope `P := {p ∈ ℝⁿ | p = N1, N ∈ C}` of (2.9).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (2.9), p.9. -/
def marginalPolytope (A : Matrix ι κ ℝ) (c : κ → ℝ) : Set (ι → ℝ) :=
  {p | ∃ N ∈ colSpace A c, ∀ i, p i = ∑ j, N i j}

/-- **`(r, c)`-scaling of a matrix.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.4: "A scaling of A is a matrix Ã = (Ã_ij)
written as Ã_ij = A_ij x_i y_j for some positive vectors (scaling vectors) x ∈ ℝⁿ, y ∈ ℝᵐ. …
An (r, c)-scaling of A is a scaling Ã of A such that Ã1 = r and Ã⊤1 = c."

`IsScaling A r c B` says `B_ij = A_ij x_i y_j` for some positive `x`, `y`, with row sums `r` and
column sums `c`. -/
def IsScaling (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (B : Matrix ι κ ℝ) : Prop :=
  ∃ (x : ι → ℝ) (y : κ → ℝ), (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
    (∀ i j, B i j = A i j * x i * y j) ∧ (∀ i, ∑ j, B i j = r i) ∧ (∀ j, ∑ i, B i j = c j)

/-- **`(r, c)`-scalability.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.4: "If an (r, c)-scaling of A exists, then A is
said to be (r, c)-scalable." -/
def Scalable (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) : Prop :=
  ∃ B, IsScaling A r c B

end General

end SinkhornHall.Supplement


