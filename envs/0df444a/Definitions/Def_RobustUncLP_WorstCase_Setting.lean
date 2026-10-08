-- Prove2me | Definitions.Def_RobustUncLP_WorstCase_Setting
-- name    : RobustUncLP_WorstCase_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:27:32.039572+00:00
-- url     : https://prove2.me/theorems/9988868c-8084-4c92-9ef6-8505d47b345c
-- title:
--   §2.1–§2.2, pp. 3–4 — uncertain LP (6), robust counterpart (7)/(12), instances, row projections 𝒰_i, constraint-wise uncertainty, Boundedness Assumption
-- statement:
--   This file fixes the vocabulary of §2.1–§2.2 of Ben-Tal and Nemirovski.
--
--   An **uncertain linear program** is written in the homogeneous form (6)
--   $$(P)\qquad \min\{c^{T}x \mid Ax \ge 0,\ f^{T}x = 1\},$$
--   where $c, f \in \mathbb R^{n}$ are fixed data and the $m\times n$ real matrix $A$ is only known to belong to an **uncertainty set** $\mathcal U$ of $m\times n$ matrices. Each $A \in \mathcal U$ gives an **instance** of the uncertain program.
--
--   1. `instFeas f A` is the feasible set $\{x \in \mathbb R^{n} \mid Ax \ge 0,\ f^{T}x = 1\}$ of the instance with matrix $A$ ($Ax \ge 0$ is meant componentwise).
--   2. `robustFeas U f` is the feasible set (12) of the **robust counterpart** (7),
--   $$G_{\mathcal U} = \{x \mid Ax \ge 0\ \ \forall A \in \mathcal U;\ f^{T}x = 1\},$$
--   whose points are the robust feasible (r-feasible) solutions.
--   3. `rowProj U i` is the set $\mathcal U_i \subseteq \mathbb R^{n}$ of all realizations of the $i$-th row: the projection of $\mathcal U$ onto the data of the $i$-th constraint (rows are written as vectors of $\mathbb R^{n}$, as in footnote 3 of the paper).
--   4. `rowProduct U` is the direct product $\widehat{\mathcal U} = \mathcal U_1\times\cdots\times\mathcal U_m$ of these projections: the matrices each of whose rows $a_i$ lies in $\mathcal U_i$.
--   5. The uncertainty is **constraint-wise** (`IsConstraintWise U`) if $\mathcal U = \mathcal U_1\times\cdots\times\mathcal U_m$.
--   6. The **Boundedness Assumption** (`BoundednessAssumption U f`) holds if there is a convex compact set $Q \subseteq \mathbb R^{n}$ that contains the feasible set of every instance $A \in \mathcal U$.
--   7. `gapFeas a11 a22 x` is feasibility of $x = (x_1, x_2)$ in the two-variable example of §2.2: $a_{11}x_1 + x_2 \ge 1$, $x_1 + a_{22}x_2 \ge 1$, $x_1 + x_2 = 1$, $x_1, x_2 \ge 0$.
--
--   These objects are the setting of Proposition 2.1, which compares the robust counterpart with the worst instance.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`, and the paper's indices $i = 1,\dots,m$ become `Fin m`. The $i$-th row of `A` is `A i`, and $a^{T}x$ is the dot product `a ⬝ᵥ x`. Because $\mathcal U \subseteq \widehat{\mathcal U}$ always holds, constraint-wise uncertainty is stated as the inclusion $\widehat{\mathcal U} \subseteq \mathcal U$. In the example the variables $x_1, x_2$ are `x 0`, `x 1`.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, pp. 3–5, §2.1 (6), (7), §2.2 example, constraint-wise uncertainty, Boundedness Assumption, footnote 3, §2.3 (12)

import Mathlib
open Matrix

namespace RobustUncLP.WorstCase

/-- Feasible set of the instance (6) of the uncertain LP with constraint matrix `A`:
`{x | Ax ≥ 0, fᵀx = 1}` (componentwise order on `Fin m → ℝ`). -/
def instFeas {m n : ℕ} (f : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | 0 ≤ A *ᵥ x ∧ f ⬝ᵥ x = 1}

/-- The robust feasible set `G_𝒰 = {x | Ax ≥ 0 ∀ A ∈ 𝒰; fᵀx = 1}` of (7)/(12):
the feasible set of the robust counterpart `(P_𝒰)`. -/
def robustFeas {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ A ∈ U, 0 ≤ A *ᵥ x) ∧ f ⬝ᵥ x = 1}

/-- `𝒰_i`: the projection of `𝒰` onto the data of the `i`-th constraint, i.e. the set of
all realizations of the `i`-th row (a row is written as a vector of `ℝⁿ`). -/
def rowProj {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (i : Fin m) : Set (Fin n → ℝ) :=
  (fun A : Matrix (Fin m) (Fin n) ℝ => A i) '' U

/-- `𝒰̂ = 𝒰₁ × ⋯ × 𝒰_m`: the direct product of the row projections of `𝒰`. -/
def rowProduct {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∀ i, A i ∈ rowProj U i}

/-- Constraint-wise uncertainty: `𝒰 = 𝒰₁ × ⋯ × 𝒰_m`. Since `𝒰 ⊆ 𝒰̂` always holds, this is
stated as the inclusion `𝒰̂ ⊆ 𝒰`. -/
def IsConstraintWise {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  rowProduct U ⊆ U

/-- Boundedness Assumption (§2.2): there is a convex compact `Q ⊆ ℝⁿ` containing the
feasible set of every instance `A ∈ 𝒰`. -/
def BoundednessAssumption {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f : Fin n → ℝ) :
    Prop :=
  ∃ Q : Set (Fin n → ℝ), Convex ℝ Q ∧ IsCompact Q ∧ ∀ A ∈ U, instFeas f A ⊆ Q

/-- Feasibility in the §2.2 example (printed form, variables `x = (x₁, x₂)` as `x 0, x 1`):
`a₁₁x₁ + x₂ ≥ 1`, `x₁ + a₂₂x₂ ≥ 1`, `x₁ + x₂ = 1`, `x₁, x₂ ≥ 0`. -/
def gapFeas (a11 a22 : ℝ) (x : Fin 2 → ℝ) : Prop :=
  1 ≤ a11 * x 0 + x 1 ∧ 1 ≤ x 0 + a22 * x 1 ∧ x 0 + x 1 = 1 ∧ 0 ≤ x 0 ∧ 0 ≤ x 1

end RobustUncLP.WorstCase


