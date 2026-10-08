-- Prove2me | Definitions.Def_Disjunctive_GeneralDisjunctions_SIC
-- name    : Disjunctive_GeneralDisjunctions_SIC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:00:41.666299+00:00
-- url     : https://prove2.me/theorems/cf2e367b-4b85-4a72-ba27-efe7d7fc31df
-- title:
--   LP in standard form, basic solutions with tableau, and standard intersection cuts with $1/\lambda^*_j$ coefficients
-- statement:
--   Setting of Balas Ch. 1/11 in the space $\mathbb R^\iota$ of structural and surplus variables: the LP relaxation $P=\{x: Ax=b,\ x\ge 0\}$; the mixed-integer set $P_I=P\cap\{x_j\in\mathbb Z,\ j\in N'\}$; rationality of the data; a basic (feasible) solution $\bar x$ with basic set $I$, nonbasic set $J$ and simplex tableau $x_i=\bar x_i-\sum_{j\in J}\bar a_{ij}x_j$ ($i\in I$) equivalent to $Ax=b$, $\bar x_J=0$; and the standard intersection cut $\sum_{j\in J}x_j/\lambda^*_j\ge 1$ from a convex set $S\ni\bar x$ and the LP cone $C(J)$, where $\lambda^*_j=\sup\{t\ge 0:\bar x+tr^j\in S\}$ and $1/\lambda^*_j:=0$ when the ray never leaves $S$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §1.2 (Theorem 1.1) and §11.2; Balas–Kis (2016) §1

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Corner

namespace Disjunctive.GeneralDisjunctions

/-- The LP relaxation in the space of structural *and* surplus variables (Balas §11.1-11.2;
Balas–Kis 2016, §1): `P := {x ∈ ℝ^ι : Ax = b, x ≥ 0}`, where the equations `Ax = b` define the
surplus variables `x_{n+i} = ∑_j a_ij x_j - b_i` and all variables are nonnegative. -/
def LPFeasible {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    Set (ι → ℝ) :=
  {x | A.mulVec x = b ∧ ∀ i, 0 ≤ x i}

/-- The mixed-integer feasible set `P_I := P ∩ {x : x_j ∈ ℤ, j ∈ N'}` (Balas §1.2, §11.2). -/
def MixedIntegerSet {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ)
    (Nprime : Finset ι) : Set (ι → ℝ) :=
  LPFeasible A b ∩ {x | IntegerPoint Nprime x}

/-- All data of the LP are rational (Balas–Kis 2016, §1: "All data are assumed to be
rational"; standard in Balas Ch. 11, needed e.g. for `conv P_I` to be a polyhedron). -/
def IsRationalData {ι : Type*} {m : ℕ} (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) : Prop :=
  (∀ r j, ∃ q : ℚ, A r j = q) ∧ ∀ r, ∃ q : ℚ, b r = q

/-- `(I, J, ā, x̄)` is a basic solution of the system `Ax = b` with basic set `I` and nonbasic set
`J` (Balas §1.2, §11.2): `I, J` partition the variables, `x̄_J = 0`, and the simplex tableau
`x_i = x̄_i - ∑_{j∈J} ā_ij x_j` (`i ∈ I`) is an equivalent rewriting of `Ax = b`. -/
def IsTableau {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (A : Matrix (Fin m) ι ℝ)
    (b : Fin m → ℝ) (I J : Finset ι) (abar : ι → ι → ℝ) (xbar : ι → ℝ) : Prop :=
  Disjoint I J ∧ I ∪ J = Finset.univ ∧ (∀ j ∈ J, xbar j = 0) ∧
    ∀ x : ι → ℝ, A.mulVec x = b ↔ ∀ i ∈ I, x i = xbar i - ∑ j ∈ J, abar i j * x j

/-- `(I, J, ā, x̄)` is a basic *feasible* solution of the LP (a vertex of `P` with its cobasis
`J` and tableau `ā`): a basic solution with `x̄ ≥ 0`. -/
def IsBasicFeasibleSolution {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (I J : Finset ι) (abar : ι → ι → ℝ)
    (xbar : ι → ℝ) : Prop :=
  IsTableau A b I J abar xbar ∧ xbar ∈ LPFeasible A b

/-- The coefficient `1/λ*_j` of the standard intersection cut (Balas §1.2, Theorem 1.1; Balas–Kis
2016, eq. (1)): `λ*_j := sup{t ≥ 0 : x̄ + t r^j ∈ S}` is the parameter at which the extreme ray
`x̄ + t r^j` of the LP cone `C(J)` meets the boundary of the convex set `S ∋ x̄`, and the
coefficient is `1/λ*_j`, with the usual convention `1/λ*_j = 0` when the ray never leaves `S`
(`λ*_j = ∞`). -/
noncomputable def sicCoef {ι : Type*} [DecidableEq ι] (S : Set (ι → ℝ)) (I : Finset ι)
    (abar : ι → ι → ℝ) (xbar : ι → ℝ) (j : ι) : ℝ :=
  open Classical in
  if BddAbove {t : ℝ | 0 ≤ t ∧ xbar + t • extremeRay I abar j ∈ S} then
    (sSup {t : ℝ | 0 ≤ t ∧ xbar + t • extremeRay I abar j ∈ S})⁻¹
  else 0

/-- The standard intersection cut `∑_{j∈J} (1/λ*_j) x_j ≥ 1` derived from the convex set `S` and
the LP cone `C(J)` at the basic solution `x̄` with tableau `ā` (Balas §1.2, Theorem 1.1), as a
subset of `ℝ^ι` (the nonbasic variables `x_J` are coordinates of `x ∈ ℝ^ι`; on the solution set of
`Ax = b` this is the cut expressed after substituting the tableau). -/
noncomputable def SICSet {ι : Type*} [DecidableEq ι] (S : Set (ι → ℝ)) (I J : Finset ι)
    (abar : ι → ι → ℝ) (xbar : ι → ℝ) : Set (ι → ℝ) :=
  {x | 1 ≤ ∑ j ∈ J, sicCoef S I abar xbar j * x j}

end Disjunctive.GeneralDisjunctions


