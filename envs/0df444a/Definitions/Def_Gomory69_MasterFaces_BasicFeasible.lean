-- Prove2me | Definitions.Def_Gomory69_MasterFaces_BasicFeasible
-- name    : Gomory69_MasterFaces_BasicFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:58:23.460673+00:00
-- url     : https://prove2.me/theorems/7a1c0c89-19f0-4600-a149-b2c1cb6f60b0
-- title:
--   Basic feasible solutions and the finite subadditive system (13)
-- statement:
--   A vector $x$ is a **basic feasible solution** of a family of linear equations and inequalities if it satisfies every row and the coefficient vectors of the rows tight at $x$ span the whole space of variables. This definition also covers the infinite family indexed by the integer solutions $t\in T$.
--
--   For the master polyhedron, fix $g_0\ne0$ and $\pi_0>0$. System (13) has one real variable $\pi(g)$ for each nonzero $g\in\mathcal G$ and consists of
--
--   $$\pi(g_0)=\pi_0,\qquad \pi(g)+\pi(g_0-g)=\pi_0\quad(g\ne0,g_0),$$
--   $$\pi(g)+\pi(h)\ge\pi(g+h)\quad(g,h\ne0),\qquad \pi(g)\ge0\quad(g\ne0).$$
--
--   Its basic feasible solutions are the algebraic objects compared with faces in Theorem 18.
--
--   **Formalization Note** The ordered pair rows include $g=h$. All appearances of $\pi(0)$ mean zero, including when $g+h=0$. The constant $\pi_0$ is a parameter, not a variable. Tight rows of any kind, including equation rows, contribute to the rank condition.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 469, definition following THEOREM 7; p. 481, system (13). DOI: 10.1016/0024-3795(69)90017-2

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- A linear row evaluated at its variable vector. -/
def rowEval {κ : Type*} [Fintype κ] (a x : κ → ℝ) : ℝ :=
  ∑ k, a k * x k

/-- A basic feasible solution of equations and inequalities: it satisfies every row,
and the coefficient vectors of all tight rows span the full variable space. -/
def IsBasicFeasible {ι κ : Type*} [Fintype κ]
    (a : ι → κ → ℝ) (b : ι → ℝ) (equation : Set ι) (x : κ → ℝ) : Prop :=
  (∀ r : ι, (r ∈ equation → rowEval (a r) x = b r) ∧
    (r ∉ equation → b r ≤ rowEval (a r) x)) ∧
  Submodule.span ℝ (a '' {r : ι | rowEval (a r) x = b r}) = ⊤

/-- The infinite system of Theorem 7 has one inequality for each integer solution. -/
def IsTBasicFeasible {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) (π₀ : ℝ) (π : N → ℝ) : Prop :=
  IsBasicFeasible
    (fun t : {t : N → ℕ // GroupSolution N g₀ t} => castSolution t.val)
    (fun _ => π₀) (∅ : Set {t : N → ℕ // GroupSolution N g₀ t}) π

/-- A row of Gomory's finite system (13). The pair row is ordered, including equal entries. -/
inductive Row13 (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G) where
  | target : Row13 G g₀
  | complement : (g : MasterIndex G) → (g : G) ≠ g₀ → Row13 G g₀
  | subadd : MasterIndex G → MasterIndex G → Row13 G g₀
  | nonnegative : MasterIndex G → Row13 G g₀

/-- The coefficient vector for evaluation at a group element; at zero it vanishes. -/
def coord {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h : G) : MasterIndex G → ℝ :=
  fun g => if (g : G) = h then 1 else 0

/-- Coefficient vector of a row of (13). -/
def row13Coeff {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) : Row13 G g₀ → MasterIndex G → ℝ
  | .target => coord g₀
  | .complement g _ => coord (g : G) + coord (g₀ - g)
  | .subadd g h => coord (g : G) + coord (h : G) - coord ((g : G) + h)
  | .nonnegative g => coord (g : G)

/-- Right-hand side of a row of (13). -/
def row13Rhs {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π₀ : ℝ) : Row13 G g₀ → ℝ
  | .target => π₀
  | .complement _ _ => π₀
  | .subadd _ _ => 0
  | .nonnegative _ => 0

/-- The first two families in (13) are equations. -/
def row13Equation {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) : Set (Row13 G g₀) :=
  {r | match r with
    | .target => True
    | .complement _ _ => True
    | .subadd _ _ => False
    | .nonnegative _ => False}

/-- Feasibility for the finite subadditive system (13), with fixed `π₀`. -/
def System13Feasible {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π₀ : ℝ) (π : MasterIndex G → ℝ) : Prop :=
  ∀ r : Row13 G g₀,
    (r ∈ row13Equation g₀ → rowEval (row13Coeff g₀ r) π = row13Rhs g₀ π₀ r) ∧
    (r ∉ row13Equation g₀ → row13Rhs g₀ π₀ r ≤ rowEval (row13Coeff g₀ r) π)

/-- A basic feasible solution of (13), with its `D - 1` coefficient variables. -/
def IsSystem13Basic {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π₀ : ℝ) (π : MasterIndex G → ℝ) : Prop :=
  IsBasicFeasible (row13Coeff g₀) (row13Rhs g₀ π₀) (row13Equation g₀) π

end Gomory69.MasterFaces


