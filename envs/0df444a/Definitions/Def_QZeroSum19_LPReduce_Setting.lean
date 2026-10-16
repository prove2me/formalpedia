-- Prove2me | Definitions.Def_QZeroSum19_LPReduce_Setting
-- name    : QZeroSum19_LPReduce_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:12.803266+00:00
-- url     : https://prove2.me/theorems/f4e449e5-6998-4fce-90c9-4a8bfa6879b6
-- title:
--   §1 LP (1) and §4, pp. 2, 12–14 — game value, the LP pair (4)/(5) with its standing assumptions, the game matrix (6) (row 2 corrected) and ε‴
-- statement:
--   This file fixes the objects of the reduction of a linear program to a zero-sum game in §4 of van Apeldoorn and Gilyén.
--
--   1. **Value of a matrix game** (LP (1), p. 2). For a real matrix $M$ with finite row set $I$ and finite column set $K$, the column player chooses a mixed strategy $y$ in the standard simplex $\Delta^K = \{y \in \mathbb R^K : y \ge 0,\ \sum_k y_k = 1\}$ and the row player answers with the best row. The value is
--   $$\lambda^*(M) = \inf_{y \in \Delta^K}\ \max_{i \in I}\ (My)_i .$$
--   2. **The LP pair** (p. 12). For $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, the primal LP (4) is $\max\{b^{\mathsf T}y : Ay \le c,\ y \ge 0\}$ and the dual LP (5) is $\min\{c^{\mathsf T}x : A^{\mathsf T}x \ge b,\ x \ge 0\}$. A vector $y$ is *primal feasible* if $Ay \le c$ and $y \ge 0$; a vector $x$ is *dual feasible* if $A^{\mathsf T}x \ge b$ and $x \ge 0$.
--   3. **Standing assumptions** (p. 12), for constants $R$, $r$ and a number $\mathrm{OPT}$:
--      - every entry of $A$, $b$ and $c$ lies in $[-1,1]$;
--      - $R > 0$ and $|c_i| \le R$ for every $i \in [n]$;
--      - $\mathrm{OPT}$ is the optimal value of (4), attained within the extra constraint $\sum_j y_j \le R$: every primal feasible $y$ has $b^{\mathsf T}y \le \mathrm{OPT}$, and some primal feasible $y$ with $\sum_j y_j \le R$ has $b^{\mathsf T}y = \mathrm{OPT}$;
--      - $\mathrm{OPT}$ is also the optimal value of (5), attained within $\sum_i x_i \le r$: some dual feasible $x$ with $\sum_i x_i \le r$ has $c^{\mathsf T}x = \mathrm{OPT}$ (strong duality).
--   4. **The game matrix** (6) (p. 14), for a threshold $\alpha$: over the variables $(y, z, h) \in \mathbb R^m \times \mathbb R \times \mathbb R$,
--   $$A''' = \begin{pmatrix} e^{\mathsf T} & 1 & -1 \\ -e^{\mathsf T} & -1 & 1 \\ -b^{\mathsf T} & 0 & \alpha/R \\ A & 0 & -c/R \end{pmatrix},$$
--   where $e$ is the all-ones vector of length $m$. The value of the game (6) is $\lambda^* = \lambda^*(A''')$.
--   5. **The error level** of Lemma 12: $\varepsilon''' = \varepsilon / (6R(r+1))$.
--
--   These are the objects of Lemma 12: an approximation of $\lambda^*$ to within $\varepsilon'''$ decides between $\mathrm{OPT} < \alpha$ and $\mathrm{OPT} \ge \alpha - \varepsilon$.
--
--   **Formalization Note** The second row of (6) is printed on p. 14 as $(-e^{\mathsf T}, 1, 1)$; the derivation on p. 13 ($A''' = (e^{\mathsf T}\ {-1};\ -e^{\mathsf T}\ 1;\ A''\ {-c''})$ over $y''' = (y, z, h)$, where $e^{\mathsf T}$ spans $(y, z)$) gives $(-e^{\mathsf T}, -1, 1)$, which is used here; with the printed row the proof's identity $A'''\hat y = (0, 0, \dots)^{\mathsf T}$ fails. The value is the infimum of the image of the simplex (never an infimum over a membership condition, which would be $\min(0,\cdot)$ of the value in Lean); the simplex over the $m+2$ columns is nonempty, so the infimum is a genuine one. LP (1)'s extra constraint $\lambda \in [-1,1]$ is not encoded: for a matrix with entries in $[-1,1]$ it is inactive. Rows of (6) are indexed by `Fin 2 ⊕ (Unit ⊕ Fin n)` (the two $e^{\mathsf T}$ rows, the $-b^{\mathsf T}$ row, the rows of $A$), columns by `Fin m ⊕ Fin 2` ($y$, then $z$ = `inr 0`, $h$ = `inr 1`). The constraint rows of $A$ are indexed by `Fin n` and the variables by `Fin m`, as in (4) (the page's index letters in §4 vary). The requirement that $\mathrm{OPT}$ bounds every primal feasible point is implied by the dual attainment through weak duality; it is kept because it says that $\mathrm{OPT}$ is the primal optimal value.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 2, LP (1); p. 12, LP (4), (5) and the standing assumptions; p. 13, A″ and A‴; p. 14, (6) and Lemma 12 (ε‴)

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

namespace QZeroSum19.LPReduce

open Matrix

/-- Feasibility for the primal LP (4), p. 12: `A y ≤ c` and `y ≥ 0`. -/
def IsPrimalFeasible {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  (∀ i, (A *ᵥ y) i ≤ c i) ∧ ∀ j, 0 ≤ y j

/-- Feasibility for the dual LP (5), p. 12: `Aᵀ x ≥ b` and `x ≥ 0`. -/
def IsDualFeasible {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ j, b j ≤ (Aᵀ *ᵥ x) j) ∧ ∀ i, 0 ≤ x i

/-- The standing assumptions of §4, p. 12, on the LP pair (4)/(5) with data `A, b, c`, the
known bounds `R` (primal) and `r` (dual), and the common optimal value `OPT`. -/
structure LPStanding {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT : ℝ) : Prop where
  /-- All entries of `A`, `c` and `b` lie in `[-1, 1]`. -/
  entries : (∀ i j, |A i j| ≤ 1) ∧ (∀ j, |b j| ≤ 1) ∧ (∀ i, |c i| ≤ 1)
  /-- The primal bound `R` is positive. -/
  R_pos : 0 < R
  /-- `|c_i| ≤ R` for every constraint `i`. -/
  c_le_R : ∀ i, |c i| ≤ R
  /-- `OPT` bounds the objective of every feasible point of (4). -/
  opt_upper : ∀ y, IsPrimalFeasible A c y → b ⬝ᵥ y ≤ OPT
  /-- `OPT` is attained by a feasible point of (4) with `∑ y ≤ R`. -/
  opt_attained : ∃ y, IsPrimalFeasible A c y ∧ ∑ j, y j ≤ R ∧ b ⬝ᵥ y = OPT
  /-- `OPT` is attained by a feasible point of (5) with `∑ x ≤ r` (strong duality). -/
  dual_attained : ∃ x, IsDualFeasible A b x ∧ ∑ i, x i ≤ r ∧ c ⬝ᵥ x = OPT

/-- The game matrix `A‴` of (6), p. 14, with row 2 corrected to `(−eᵀ, −1, 1)` as the derivation
on p. 13 gives. Rows: `inl 0` (`eᵀ`), `inl 1` (`−eᵀ`), `inr (inl ())` (`−bᵀ`), `inr (inr i)`
(row `i` of `A`). Columns: `inl j` (the variable `y_j`), `inr 0` (the variable `z`), `inr 1`
(the variable `h`). -/
noncomputable def gameMatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (α R : ℝ) : Matrix (Fin 2 ⊕ (Unit ⊕ Fin n)) (Fin m ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks
    -- rows `eᵀ` and `−eᵀ` on the `y` columns
    (Matrix.of fun (t : Fin 2) (_ : Fin m) => ![(1 : ℝ), -1] t)
    -- rows `(1, −1)` and `(−1, 1)` on the columns `z, h`
    !![(1 : ℝ), -1; -1, 1]
    -- rows `−bᵀ` and `A` on the `y` columns
    (Matrix.of fun (s : Unit ⊕ Fin n) (j : Fin m) => Sum.elim (fun _ => -b j) (fun i => A i j) s)
    -- rows `(0, α/R)` and `(0, −c_i/R)` on the columns `z, h`
    (Matrix.of fun (s : Unit ⊕ Fin n) (k : Fin 2) =>
      Sum.elim (fun _ => ![(0 : ℝ), α / R] k) (fun i => ![(0 : ℝ), -c i / R] k) s)

/-- The additive error `ε‴ = ε / (6 R (r + 1))` of Lemma 12, p. 14. -/
noncomputable def epsGame (ε R r : ℝ) : ℝ := ε / (6 * R * (r + 1))

end QZeroSum19.LPReduce


