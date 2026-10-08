-- Prove2me | Definitions.Def_GilmoreGomory61_CuttingStock_Basis
-- name    : GilmoreGomory61_CuttingStock_Basis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:53:58.320524+00:00
-- url     : https://prove2.me/theorems/995226ee-aade-4643-853f-09e88fa3b811
-- title:
--   p. 852 and pp. 854–855 — current basis, bordered tableau, and pricing quantity
-- statement:
--   A **basis** lists $m$ cutting or surplus columns. Its coefficient matrix is $A$, and its cost row is $C$. The paper's bordered matrix, bordered demand, and candidate column are
--
--   $$
--   B=\begin{pmatrix}1&-C\\0&A\end{pmatrix},\qquad N'=(0,N_1,\ldots,N_m)^T,\qquad P=(-c_j,a_{1j},\ldots,a_{mj})^T.
--   $$
--
--   The current tableau column is $\bar N=B^{-1}N'$. The $m$ noninitial entries of the first row of $B^{-1}$ are the pricing multipliers $b_i$, and the first entry of $B^{-1}P$ is the candidate's pricing quantity. The **basic solution** uses the values in the noninitial entries of $\bar N$ on the listed columns and zero elsewhere. A feasible basis has invertible $A$ and nonnegative basic values; a nondegenerate basis has strictly positive basic values. A column improves a basis when a strictly cheaper feasible solution uses only those basic columns and that candidate.
--
--   These objects connect the paper's tableau calculations to the full cutting-stock linear program.
--
--   **Formalization Note** Bordered rows are indexed by a cost coordinate followed by zero-based demand coordinates; the paper's $(i+1)$st row is the demand row for Lean index $i$. Solutions have finite support, and the improvement predicate requires feasibility against the full demand equations.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 852, (4)–(5); pp. 854–855, steps (2)–(5)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Model

namespace GilmoreGomory61.CuttingStock

/-- Matrix A of the current m basic columns, p. 852. -/
def basisMat {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i r => colVec I (β r) i

/-- The cost row C of the basic columns. -/
def costRow {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Fin m → ℝ :=
  fun r => colCost I (β r)

/-- The bordered matrix B of routine step (2), after any basis change. -/
def bordered {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun _ r => -costRow I β r) 0 (basisMat I β)

/-- The bordered demand vector N′, with zero cost coordinate. -/
def Nprime {m k : ℕ} (I : Instance m k) : Unit ⊕ Fin m → ℝ :=
  Sum.elim (fun _ => 0) (fun i => (I.N i : ℝ))

/-- The current tableau right-hand column B⁻¹N′. -/
noncomputable def Nbar {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Unit ⊕ Fin m → ℝ := Matrix.mulVec (bordered I β)⁻¹ (Nprime I)

/-- The last m entries of the first row of B⁻¹, routine step (4). -/
noncomputable def mult {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Fin m → ℝ :=
  fun i => (bordered I β)⁻¹ (Sum.inl ()) (Sum.inr i)

/-- The bordered column P for either an activity or a surplus variable. -/
def extCol {m k : ℕ} (I : Instance m k) (j : Col I) : Unit ⊕ Fin m → ℝ :=
  Sum.elim (fun _ => -colCost I j) (colVec I j)

/-- The first entry of B⁻¹P, the paper's pricing quantity. -/
noncomputable def priceOut {m k : ℕ} (I : Instance m k) (β : Fin m → Col I)
    (j : Col I) : ℝ := (Matrix.mulVec (bordered I β)⁻¹ (extCol I j)) (Sum.inl ())

/-- The current basic solution, using only columns in β. -/
noncomputable def basicSol {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Col I →₀ ℝ :=
  ∑ r : Fin m, Finsupp.single (β r) (Nbar I β (Sum.inr r))

/-- Invertible basic columns with nonnegative basic values. -/
def IsFeasibleBasis {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Prop :=
  IsUnit (basisMat I β).det ∧ ∀ r, 0 ≤ Nbar I β (Sum.inr r)

/-- Strict positivity of every current basic value. -/
def IsNondegenerate {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Prop :=
  ∀ r, 0 < Nbar I β (Sum.inr r)

/-- A strictly cheaper feasible solution using only the current basis and one candidate column. -/
def Improves {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) (j : Col I) : Prop :=
  ∃ z : Col I →₀ ℝ, Feasible I z ∧
    (∀ j' ∈ z.support, j' ∈ Set.range β ∨ j' = j) ∧
    cost I z < cost I (basicSol I β)

end GilmoreGomory61.CuttingStock


