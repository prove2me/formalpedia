-- Prove2me | Definitions.Def_Gomory58_FractionalCut_Tableau
-- name    : Gomory58_FractionalCut_Tableau
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:28:12.023221+00:00
-- url     : https://prove2.me/theorems/78089f7e-111b-4da5-87f9-c668aa1336e4
-- title:
--   Equations (2), (3), and (2*)
-- statement:
--   Let $a'_{i,j}$ be a real tableau with row $0$ for the objective $w$, rows $1,\ldots,m$ for the variables $x'_i$, column $0$ for the constants, and columns $1,\ldots,n$ for the variables $t'_j$. A **tableau solution** satisfies
--
--   $$x'_i=a'_{i,0}+\sum_{j=1}^n a'_{i,j}(-t'_j) \quad (0\le i\le m).$$
--
--   A feasible solution has every $x'_i,t'_j\ge0$; a nonnegative integer solution has every one of these variables, including $w=x'_0$, integral. The **fractional cut** from row $i_0$ uses $f'_{i_0,j}=a'_{i_0,j}-\lfloor a'_{i_0,j}\rfloor$ and sets
--
--   $$s_1=-f'_{i_0,0}-\sum_{j=1}^n f'_{i_0,j}(-t'_j).$$
--
--   The augmented system (2*) adjoins this equation. Its feasible and nonnegative integer solutions also require $s_1\ge0$, and the latter require $s_1$ to be integral. These definitions allow the cut and the old tableau to be compared without assuming the real simplex solution is integral.
--
--   **Formalization Note** Lean uses real variables with an explicit integrality predicate. `Fin (m+1)` row 0 is $w$, and `Fin (n+1)` column 0 is the constant column; `Fin n` indexes $t'_1,\ldots,t'_n$.
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 276, equations (2), (3), and system (2*)

import Mathlib

namespace Gomory58.FractionalCut

def IsInt (r : ℝ) : Prop := ∃ z : ℤ, (z : ℝ) = r

def TableauSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) : Prop :=
  ∀ i, x i = a i 0 + ∑ j : Fin n, a i j.succ * (-t j)

def FeasibleSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) : Prop :=
  TableauSol a x t ∧ (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ t j)

def NonnegIntSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) : Prop :=
  FeasibleSol a x t ∧ (∀ i, IsInt (x i)) ∧ (∀ j, IsInt (t j))

noncomputable def cutValue {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (t : Fin n → ℝ) : ℝ :=
  -Int.fract (a i₀ 0) - ∑ j : Fin n, Int.fract (a i₀ j.succ) * (-t j)

def StarSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) : Prop :=
  TableauSol a x t ∧ s = cutValue a i₀ t

def FeasibleStar {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) : Prop :=
  StarSol a i₀ x t s ∧ (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ t j) ∧ 0 ≤ s

def NonnegIntSolStar {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) : Prop :=
  FeasibleStar a i₀ x t s ∧ (∀ i, IsInt (x i)) ∧ (∀ j, IsInt (t j)) ∧ IsInt s

end Gomory58.FractionalCut


