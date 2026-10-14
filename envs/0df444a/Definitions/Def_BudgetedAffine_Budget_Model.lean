-- Prove2me | Definitions.Def_BudgetedAffine_Budget_Model
-- name    : BudgetedAffine_Budget_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:07.437313+00:00
-- url     : https://prove2.me/theorems/4e59a7c4-058b-424f-82d5-6752f6ee783f
-- title:
--   (1.1), (1.2), (2.1), (3.2) — two-stage adjustable robust problem, z_AR, z_Aff, budget set, covering value
-- statement:
--   **The two-stage adjustable robust problem (1.1).** Let $A\in\mathbb R^{m\times n}$, a non-negative recourse matrix $B\in\mathbb R^{m\times n}_+$, costs $c,d\in\mathbb R^n_+$, a polyhedral set $\mathcal X\subseteq\mathbb R^n$ (the solution set of finitely many linear inequalities $Gx\le g$), and an uncertainty set $\mathcal U\subseteq\mathbb R^m$ of right-hand sides be given. A **two-stage solution** is a first-stage decision $x\in\mathbb R^n$ together with a second-stage rule $y:\mathbb R^m\to\mathbb R^n$, chosen after $h$ is revealed. It is **feasible** when
--   $$x\in\mathcal X,\qquad y(h)\ge 0,\qquad Ax+By(h)\ge h\quad\text{for every } h\in\mathcal U,$$
--   with all inequalities componentwise. Its **worst-case cost** is $\sup_{h\in\mathcal U}\big(c^Tx+d^Ty(h)\big)$, and
--   $$z_{AR}(\mathcal U)=\inf\Big\{\sup_{h\in\mathcal U}\big(c^Tx+d^Ty(h)\big)\ :\ (x,y)\text{ feasible}\Big\}.$$
--   A feasible $(x^*,y^*)$ is **optimal** when its worst-case cost equals $z_{AR}(\mathcal U)$.
--
--   **Affine policies (2.1).** $z_{Aff}(\mathcal U)$ is the same infimum restricted to second-stage rules of the form $y(h)=Ph+q$ with $P\in\mathbb R^{n\times m}$, $q\in\mathbb R^n$; feasibility still requires $Ph+q\ge 0$ and $Ax+B(Ph+q)\ge h$ for every $h\in\mathcal U$.
--
--   **Budget of uncertainty set (1.2).** For weights $w\in\mathbb R^m$,
--   $$\mathcal U=\Big\{h\in[0,1]^m\ :\ \sum_{i=1}^m w_ih_i\le 1\Big\}.$$
--
--   **Fractional covering value (3.2).** For a requirement $h\in\mathbb R^m$,
--   $$z(h)=\min_{y\ge 0}\big\{d^Ty\ :\ By\ge h\big\},$$
--   and for $\mathcal W\subseteq[m]$ we write $z(\mathcal W)=z(\mathbb 1(\mathcal W))$ with $\mathbb 1(\mathcal W)=\sum_{i\in\mathcal W}e_i$. A vector $y$ is an optimal solution of (3.2) when $y\ge0$, $By\ge h$ and $d^Ty=z(h)$.
--
--   These are the objects of Sections 1–3 of the paper on which every statement of the mission is built.
--
--   **Formalization Note** Vectors are functions on `Fin m` / `Fin n` with the componentwise order; Lean index $i$ is the paper's $i+1$. The values $z_{AR}$, $z_{Aff}$ and $z(h)$ are infima in the extended reals, so an infeasible problem has value $+\infty$ (never a default $0$). The paper writes $z_{AR}=\min_x c^Tx+\max_{h}\min_{y(h)}d^Ty(h)$; taking the infimum over second-stage rules $y(\cdot)$ gives the same value, because $y(h)$ may be chosen separately for each $h$. The data hypotheses ($B\ge0$, $c,d\ge0$, $\mathcal X$ polyhedral, $w_i\in[0,1]$) are not part of the definitions; each theorem states them.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, (1.1) p. 1, (1.2) pp. 2–3, (2.1) p. 5, Sec. 3.1 notation and (3.2) p. 7

import Mathlib

namespace BudgetedAffine.Budget

open Matrix

/-- `X ⊆ ℝⁿ` is a polyhedron: the solution set of finitely many linear inequalities `G x ≤ g`. -/
def IsPolyhedral {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  ∃ (k : ℕ) (G : Matrix (Fin k) (Fin n) ℝ) (g : Fin k → ℝ), X = {x | G *ᵥ x ≤ g}

/-- `(x, y)` is feasible for the two-stage problem (1.1) over the uncertainty set `U`:
`x ∈ X` and, for every `h ∈ U`, `y(h) ≥ 0` and `A x + B y(h) ≥ h` (componentwise). -/
def Feasible {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (X : Set (Fin n → ℝ))
    (U : Set (Fin m → ℝ)) (x : Fin n → ℝ) (y : (Fin m → ℝ) → Fin n → ℝ) : Prop :=
  x ∈ X ∧ ∀ h ∈ U, 0 ≤ y h ∧ h ≤ A *ᵥ x + B *ᵥ y h

/-- Worst-case cost `sup_{h ∈ U} (cᵀx + dᵀy(h))` of a two-stage solution, in `EReal`. -/
noncomputable def worstCost {m n : ℕ} (c d : Fin n → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n → ℝ) (y : (Fin m → ℝ) → Fin n → ℝ) : EReal :=
  ⨆ h ∈ U, ((c ⬝ᵥ x + d ⬝ᵥ y h : ℝ) : EReal)

/-- `z_AR(U)` of (1.1): the infimum of the worst-case cost over all feasible two-stage solutions
(`+∞` if there is none). -/
noncomputable def zAR {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (U : Set (Fin m → ℝ)) : EReal :=
  ⨅ (x : Fin n → ℝ) (y : (Fin m → ℝ) → Fin n → ℝ) (_ : Feasible A B X U x y),
    worstCost c d U x y

/-- `z_Aff(U)` of (2.1): the same infimum over solutions whose second stage is an affine policy
`h ↦ P h + q` (feasibility includes `P h + q ≥ 0` on `U`). -/
noncomputable def zAff {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (U : Set (Fin m → ℝ)) : EReal :=
  ⨅ (x : Fin n → ℝ) (P : Matrix (Fin n) (Fin m) ℝ) (q : Fin n → ℝ)
    (_ : Feasible A B X U x (fun h => P *ᵥ h + q)),
    worstCost c d U x (fun h => P *ᵥ h + q)

/-- `(x, y)` is an optimal solution of (1.1): feasible and attaining `z_AR(U)`. -/
def IsOptimalAR {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (U : Set (Fin m → ℝ)) (x : Fin n → ℝ)
    (y : (Fin m → ℝ) → Fin n → ℝ) : Prop :=
  Feasible A B X U x y ∧ worstCost c d U x y = zAR A B c d X U

/-- The budget of uncertainty set (1.2): `{h ∈ [0,1]ᵐ | ∑ᵢ wᵢ hᵢ ≤ 1}`. -/
def budgetSet {m : ℕ} (w : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {h | (∀ i, 0 ≤ h i ∧ h i ≤ 1) ∧ ∑ i, w i * h i ≤ 1}

/-- The fractional covering value (3.2): `z(h) = min_{y ≥ 0} {dᵀy | B y ≥ h}`, in `EReal`
(`+∞` when infeasible). -/
noncomputable def coverCost {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (h : Fin m → ℝ) : EReal :=
  ⨅ (y : Fin n → ℝ) (_ : 0 ≤ y ∧ h ≤ B *ᵥ y), ((d ⬝ᵥ y : ℝ) : EReal)

/-- The indicator vector `𝟙(W) = ∑_{i ∈ W} eᵢ`. -/
def indic {m : ℕ} (W : Finset (Fin m)) : Fin m → ℝ :=
  fun i => if i ∈ W then 1 else 0

/-- `y` is an optimal solution of the covering problem (3.2) with requirement `h`. -/
def IsCoverOpt {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) (h : Fin m → ℝ)
    (y : Fin n → ℝ) : Prop :=
  0 ≤ y ∧ h ≤ B *ᵥ y ∧ ((d ⬝ᵥ y : ℝ) : EReal) = coverCost B d h

end BudgetedAffine.Budget


