-- Prove2me | Definitions.Def_ShapleySnowSG_Kernel_MatrixGame
-- name    : ShapleySnowSG_Kernel_MatrixGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:57:59.836455+00:00
-- url     : https://prove2.me/theorems/c49c0be4-8571-48ac-85a2-af3511dc5941
-- title:
--   §2.3 and p. 5 — matrix-game value, optimal strategy sets X*, Y*, cofactor matrix co(M), entry sum S(M), and Shapley–Snow kernels (Definition 2.3.3)
-- statement:
--   This file fixes the matrix-game layer of the paper.
--
--   1. **Value.** A real matrix $A$ with rows indexed by a finite set $I$ and columns by a finite set $J$ is a zero-sum game in which the row player chooses a mixed strategy $x\in\Delta(I)$, the column player a mixed strategy $y\in\Delta(J)$, and the row player receives ${}^t x A y$. A number $w$ is the **value** of $A$, written $\mathrm{val}(A)=w$, when some $x\in\Delta(I)$ guarantees $\sum_i x_i A_{ij}\ge w$ for every column $j$ and some $y\in\Delta(J)$ guarantees $\sum_j A_{ij}y_j\le w$ for every row $i$.
--   2. **Optimal strategies.** $X^*\subset\Delta(I)$ and $Y^*\subset\Delta(J)$ are the strategies that guarantee the value.
--   3. **Ones, sums, cofactors.** $U$ is the matrix of ones, $S(M)$ the sum of the entries of $M$, and for a square $M$ the cofactor matrix $\mathrm{co}(M)$ has entries $\mathrm{co}(M)_{ij}=(-1)^{i+j}M_{ij}$, where $M_{ij}$ is the minor obtained by deleting row $i$ and column $j$; thus $M\,{}^t\mathrm{co}(M)=\det(M)\,\mathrm{Id}$ and $\mathrm{co}(M)=1$ for a $1\times1$ matrix.
--   4. **Shapley–Snow kernel.** A square sub-matrix $\dot G$ of $G$, with rows $\dot I\subset I$ and columns $\dot J\subset J$ of equal size, is a **Shapley–Snow kernel** (SSK) when $S(\mathrm{co}(\dot G))\neq0$ and the vectors
--   $$\dot x=\frac{\mathrm{co}(\dot G)}{S(\mathrm{co}(\dot G))}\mathbf 1,\qquad \dot y=\frac{{}^t\mathrm{co}(\dot G)}{S(\mathrm{co}(\dot G))}\mathbf 1,$$
--   completed with zeros outside $\dot I$ and $\dot J$, are optimal strategies of $G$.
--
--   Every object of the paper's §2.3 and §3 is built from these: the kernels of the local games select the reduced array of the stochastic game.
--
--   **Formalization Note** The value is a relation `IsMatVal A w`, not a function, so no supremum over an empty or unbounded set is ever taken; its existence and uniqueness for nonempty action sets are standard and left to solvers. `co M` is the transpose of Mathlib's `adjugate`. A square sub-game is given by two embeddings `r : Fin s ↪ I`, `c : Fin s ↪ J` (the pairing of rows with columns only changes the sign of `co`, not $\dot x$, $\dot y$). Definition 2.3.3 asks for the four conditions of Theorem 2.3.1 "for some basic solution"; here only conditions (1)–(2) and optimality are required. This is equivalent: by the "if" part of Theorem 2.3.1 such a pair is basic, and (3)–(4) follow from (1)–(2) and optimality.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 5 (notation), p. 10, §2.3, Theorem 2.3.1 and Definition 2.3.3

import Mathlib

namespace ShapleySnowSG.Kernel

open Matrix

/-- `IsMatVal A w`: the matrix game `A` (row player maximizes the payoff `ᵗx A y`, mixed
strategies are probability vectors) has value `w`, i.e. some mixed strategy `x` of the row
player guarantees at least `w` against every column, and some mixed strategy `y` of the column
player concedes at most `w` against every row (p. 5). -/
def IsMatVal {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (w : ℝ) : Prop :=
  ∃ x ∈ stdSimplex ℝ ι, ∃ y ∈ stdSimplex ℝ κ,
    (∀ j, w ≤ ∑ i, x i * A i j) ∧ (∀ i, ∑ j, A i j * y j ≤ w)

/-- `X*`: the optimal mixed strategies of the row player of `A` (§2.3, p. 10). -/
def optRow {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : Set (ι → ℝ) :=
  {x | x ∈ stdSimplex ℝ ι ∧ ∃ w, IsMatVal A w ∧ ∀ j, w ≤ ∑ i, x i * A i j}

/-- `Y*`: the optimal mixed strategies of the column player of `A` (§2.3, p. 10). -/
def optCol {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : Set (κ → ℝ) :=
  {y | y ∈ stdSimplex ℝ κ ∧ ∃ w, IsMatVal A w ∧ ∀ i, ∑ j, A i j * y j ≤ w}

/-- `U`: the matrix of ones (p. 5). -/
def onesMat (ι κ : Type*) : Matrix ι κ ℝ := Matrix.of fun _ _ => 1

/-- `S(M)`: the sum of the entries of `M` (p. 5). -/
def Ssum {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, M i j

/-- `co(M)`: the matrix of cofactors, `co(M)_{ij} = (-1)^{i+j} M_{ij}` with `M_{ij}` the minor
obtained by deleting row `i` and column `j`, so that `M ᵗco(M) = det(M) Id`, and `co(M) = 1` for a
`1 × 1` matrix (p. 5). It is the transpose of Mathlib's adjugate. -/
def co {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) : Matrix m m ℝ :=
  (Matrix.adjugate M)ᵀ

/-- The square sub-game `Ġ` of `G` with rows `r 0, …, r (s-1)` and columns `c 0, …, c (s-1)`. -/
def subGame {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ) :
    Matrix (Fin s) (Fin s) ℝ :=
  G.submatrix r c

/-- `ẋ = co(Ġ) 1 / S(co(Ġ))` of Theorem 2.3.1 (2), a vector indexed by the rows of `Ġ`. -/
noncomputable def ssRow {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι)
    (c : Fin s ↪ κ) : Fin s → ℝ :=
  fun a => (co (subGame G s r c) *ᵥ fun _ => (1 : ℝ)) a / Ssum (co (subGame G s r c))

/-- `ẏ = ᵗco(Ġ) 1 / S(co(Ġ))` of Theorem 2.3.1 (2), a vector indexed by the columns of `Ġ`. -/
noncomputable def ssCol {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι)
    (c : Fin s ↪ κ) : Fin s → ℝ :=
  fun b => ((co (subGame G s r c))ᵀ *ᵥ fun _ => (1 : ℝ)) b / Ssum (co (subGame G s r c))

/-- The row strategy `x` of the full game obtained by completing `ẋ` with zeros outside `İ`. -/
noncomputable def padRow {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι)
    (c : Fin s ↪ κ) : ι → ℝ :=
  Function.extend r (ssRow G s r c) 0

/-- The column strategy `y` of the full game obtained by completing `ẏ` with zeros outside `J̇`. -/
noncomputable def padCol {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι)
    (c : Fin s ↪ κ) : κ → ℝ :=
  Function.extend c (ssCol G s r c) 0

/-- Definition 2.3.3 (p. 10): the square sub-matrix `Ġ = G.submatrix r c` is a Shapley–Snow
kernel of `G`: `S(co(Ġ)) ≠ 0`, and the strategies `ẋ`, `ẏ` of Theorem 2.3.1 (2), completed with
zeros, are optimal strategies of `G` (they are then a basic solution by Theorem 2.3.1, and
conditions (3)–(4) follow). -/
def IsSSK {ι κ : Type*} [Fintype ι] [Fintype κ] (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι)
    (c : Fin s ↪ κ) : Prop :=
  Ssum (co (subGame G s r c)) ≠ 0 ∧ padRow G s r c ∈ optRow G ∧ padCol G s r c ∈ optCol G

end ShapleySnowSG.Kernel


