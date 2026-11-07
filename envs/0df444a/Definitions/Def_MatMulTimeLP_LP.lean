-- Prove2me | Definitions.Def_MatMulTimeLP_LP
-- name    : MatMulTimeLP_LP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:57.903952+00:00
-- url     : https://prove2.me/theorems/5cb42be7-2118-4ccb-a418-73422f872f83
-- title:
--   The LP width, orthogonal projections, input layouts and the auxiliary LP
-- statement:
--   For the standard-form linear program $\min c^\top x$ subject to $Ax=b$, $x\ge 0$, with $A\in\mathbb R^{d\times n}$, this module defines:
--
--   1. the $\ell_1$ and $\ell_2$ norms, and the width $W=\max\{\max_{i,j}|A_{ij}|,\max_i|b_i|,\max_j|c_j|\}$ of Theorem 1.1;
--   2. the predicate "$P$ is the orthogonal projection onto the image of $B$": $P$ is symmetric and idempotent with the same range as $B$;
--   3. the machine input layouts: $A$ row by row, then $b,c,R,\varepsilon$; $A$ row by row, then $x$; $H$ row by row, then $h$;
--   4. the auxiliary LP of Lemma B.1:
--
--   $$\tilde A=\begin{pmatrix}A&0&b/R-A\mathbf 1\\ \mathbf 1^\top&1&0\end{pmatrix},\quad \tilde b=\begin{pmatrix}b/R\\ n+1\end{pmatrix},\quad \tilde c=\begin{pmatrix}\delta c/C\\0\\1\end{pmatrix},$$
--
--   with the initial dual $\tilde y^{(0)}=(0,-1)$ and slack $\tilde s^{(0)}=(\mathbf 1+\delta c/C,1,1)$.
--
--   These are the data of the reduction from the LP with no known starting point to an LP with an explicit nearly central point.
--
--   **Formalization Note** Feasibility and strict feasibility are the published `WrightPDIPM.CentralPath.PrimalFeasible`, `F`, `Fo`, which have no rank assumption. The sup norm of a vector over an empty index set is $0$, so $W$ is defined at $d=0$. The blocks of $\tilde A$ are written with `Fin.snoc`, with coordinates $0,\dots,n-1$ of `Fin (n + 2)` the original variables. The dimensions are not part of the input, because the program is chosen per size.
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), LP (1) p.3; W, Theorem 1.1 p.3; proof of Lemma 4.2 p.17; Lemma B.1 p.48

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_WrightPDIPM_CentralPath_LP

namespace MatMulTimeLP

open Matrix WrightPDIPM.CentralPath

/-!
# The linear program, its auxiliary LP and its input layouts

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc): the LP (1) p.3, Theorem 1.1 p.3 (the width `W`), the
projections of the proof of Lemma 4.2 p.17, and the auxiliary LP of Lemma B.1 p.48.

**Formalization Note** The feasibility predicates and the strictly feasible set are the published
`WrightPDIPM.CentralPath.PrimalFeasible`, `F` and `Fo`, which carry no rank assumption. `‖v‖` is the
sup norm of `Fin m → ℝ`, with value `0` at `m = 0`. The blocks of `Ã` are written with `Fin.snoc`:
coordinates `0, …, n-1` of `Fin (n + 2)` are the original variables, `n` and `n + 1` the two new ones.
The dimensions `d, n` are not in the machine inputs, because the program is chosen per size.
-/

/-- The `ℓ₁` norm. -/
def l1Norm {m : ℕ} (v : Fin m → ℝ) : ℝ := ∑ i, |v i|

/-- The `ℓ₂` norm. -/
noncomputable def l2Norm {m : ℕ} (v : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The width `W = max{max_{i,j} |A_ij|, max_i |b_i|, max_j |c_j|}` of Theorem 1.1, p.3 (`0` for an
empty family). -/
noncomputable def lpWidth {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ) :
    ℝ :=
  max ‖fun p : Fin d × Fin n => A p.1 p.2‖ (max ‖b‖ ‖c‖)

/-- `P` is the orthogonal projection onto the image of `B`: symmetric, idempotent, with the same
range as `B` (p.17: "the orthogonal projection onto im(XAᵀ)"). -/
def IsOrthoProjOnto {n d : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin d) ℝ) :
    Prop :=
  Pᵀ = P ∧ P * P = P ∧ LinearMap.range P.mulVecLin = LinearMap.range B.mulVecLin

/-- The machine input of Theorem 1.1: `A` row by row, then `b`, `c`, `R`, `ε`. -/
def lpInput {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ) (R ε : ℝ) :
    List ℝ :=
  matToList A ++ vecToList b ++ vecToList c ++ [R, ε]

/-- The machine input of the projection step of Lemma 4.2: `A` row by row, then `x`. -/
def projInput {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) : List ℝ :=
  matToList A ++ vecToList x

/-- The machine input of Theorem 2.2: `H` row by row, then `h`. -/
def fixInput {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : List ℝ :=
  matToList H ++ vecToList h

/-- The vector `(u, p, q) ∈ ℝ^{n+2}`. -/
def col3 {n : ℕ} (u : Fin n → ℝ) (p q : ℝ) : Fin (n + 2) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (Fin.snoc (α := fun _ => ℝ) u p) q

/-- The vector `(u, p) ∈ ℝ^{d+1}`. -/
def row2 {d : ℕ} (u : Fin d → ℝ) (p : ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) u p

/-- The first `n` coordinates of a vector of `ℝ^{n+2}`. -/
def firstCoords {n : ℕ} (v : Fin (n + 2) → ℝ) : Fin n → ℝ :=
  fun j => v j.castSucc.castSucc

/-- The auxiliary constraint matrix of Lemma B.1, p.48: the rows `(A_i, 0, b_i/R - (A1)_i)`, then the
last row `(1ᵀ, 1, 0)`. -/
noncomputable def auxA {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (R : ℝ) :
    Matrix (Fin (d + 1)) (Fin (n + 2)) ℝ :=
  Matrix.of (Fin.snoc (α := fun _ => Fin (n + 2) → ℝ)
    (fun i => col3 (A i) 0 (b i / R - (A *ᵥ fun _ => 1) i)) (col3 (fun _ => 1) 1 0))

/-- The auxiliary right-hand side of Lemma B.1, p.48: `(b/R, n + 1)`. -/
noncomputable def auxB {d : ℕ} (n : ℕ) (b : Fin d → ℝ) (R : ℝ) : Fin (d + 1) → ℝ :=
  row2 (fun i => b i / R) ((n : ℝ) + 1)

/-- The auxiliary cost of Lemma B.1, p.48: `(δc/C, 0, 1)`. -/
noncomputable def auxC {n : ℕ} (c : Fin n → ℝ) (C δ : ℝ) : Fin (n + 2) → ℝ :=
  col3 (fun j => δ * c j / C) 0 1

/-- The initial dual `ỹ⁽⁰⁾ = (0, -1)` of Lemma B.1, p.48. -/
def auxY0 (d : ℕ) : Fin (d + 1) → ℝ :=
  row2 (fun _ => 0) (-1)

/-- The initial slack `s̃⁽⁰⁾ = (1 + δc/C, 1, 1)` of Lemma B.1, p.48. -/
noncomputable def auxS0 {n : ℕ} (c : Fin n → ℝ) (C δ : ℝ) : Fin (n + 2) → ℝ :=
  col3 (fun j => 1 + δ * c j / C) 1 1

end MatMulTimeLP


