-- Prove2me | Definitions.Def_LPResolvingRM_SFOptimal
-- name    : LPResolvingRM_SFOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:21.92207+00:00
-- url     : https://prove2.me/theorems/6beb1484-0906-49b3-92a7-75b53a4f54e4
-- title:
--   Standard-form LP (35), its dual, the smallest singular value and reduced costs
-- statement:
--   For $c\in\mathbb R^n$, $A\in\mathbb R^{m\times n}$ and $b\in\mathbb R^m$, the standard-form LP is
--   $$\min\ c^\top x\quad\text{s.t.}\quad Ax=b,\quad x\ge0, \tag{35}$$
--   with dual $\max\ b^\top\lambda$ s.t. $A^\top\lambda\le c$. The **reduced cost** of variable $j$ for a dual vector $\lambda$ is $\Psi_j=c_j-A_j^\top\lambda$, and the **smallest singular value** of a matrix $M$ with $m$ rows is $\sigma_{\min}(M)=\inf_{\|v\|_2=1}\|Mv\|_2$.
--
--   These objects state Proposition 5, the general LP-perturbation result behind Lemma 1.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Appendix E, (35)–(36), p.46; (39), p.48

import Mathlib

open scoped Classical
open Matrix

namespace LPResolvingRM

/-- Feasibility for the **standard-form LP (35)** `min cᵀx s.t. Ax = b, x ≥ 0`
(arXiv:2101.11092v3, Appendix E, p.46), with `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`. -/
def SFFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Prop :=
  (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b

/-- **Optimal solution of the standard-form LP (35)** `min cᵀx s.t. Ax = b, x ≥ 0`
(arXiv:2101.11092v3, p.46). -/
def SFOptimal {m n : ℕ} (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  SFFeasible A b x ∧ ∀ x', SFFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- **Dual optimal solution of (35)**: an optimal solution of `max bᵀλ s.t. Aᵀλ ≤ c`
(arXiv:2101.11092v3, p.46, "λ∗ is the dual optimal solution of (35)"). -/
def SFDualOptimal {m n : ℕ} (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (lam : Fin m → ℝ) : Prop :=
  (∀ j, (A.transpose *ᵥ lam) j ≤ c j) ∧
    ∀ lam', (∀ j, (A.transpose *ᵥ lam') j ≤ c j) → b ⬝ᵥ lam' ≤ b ⬝ᵥ lam

/-- The **smallest singular value** `σ_min(M) := inf_{‖v‖₂ = 1} ‖Mv‖₂` of a real matrix with
`m` rows and columns indexed by `ι` (arXiv:2101.11092v3, Proposition 5, p.46).

**Formalization Note.** For a square matrix this is the smallest singular value; it is applied
to the basic submatrix `A_{B*}`, which is `m × m` under nondegeneracy. -/
noncomputable def sigmaMin {m : ℕ} {ι : Type*} [Fintype ι] (M : Matrix (Fin m) ι ℝ) : ℝ :=
  ⨅ v : {v : EuclideanSpace ℝ ι // ‖v‖ = 1},
    ‖(WithLp.toLp 2 (M *ᵥ WithLp.ofLp v.1) : EuclideanSpace ℝ (Fin m))‖

/-- The **reduced cost** `Ψ_j := c_j − A_jᵀλ` of variable `j` in the standard-form LP (35) for
the dual vector `λ` (arXiv:2101.11092v3, E.1, (39), p.48). -/
def reducedCost {m n : ℕ} (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (lam : Fin m → ℝ)
    (j : Fin n) : ℝ :=
  c j - (A.transpose *ᵥ lam) j

end LPResolvingRM


