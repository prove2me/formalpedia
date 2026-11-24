-- Prove2me | Definitions.Def_ALADIN_LocalStab_Supplement_Values
-- name    : ALADIN_LocalStab_Supplement_Values
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:07:03.341597+00:00
-- url     : https://prove2.me/theorems/a0f2a65a-8140-4f5d-8ce8-a80791a97b8e
-- title:
--   (6.4)–(6.7): extended-real dual and proximal values, projection, and the exact L1 penalty
-- statement:
--   For the published block problem, let $F$ be the original feasible set and $F_b$ the set satisfying only the block inequalities. For positive definite scaling matrices $\Sigma_i$, write $Q_x(z)=\frac12\sum_i(z_i-x_i)^T\Sigma_i(z_i-x_i)$ and $r(z)=\sum_i A_i z_i-b$. Define
--   $$V_\rho(x,\lambda)=\inf_{z\in F_b}\{f(z)+\rho Q_x(z)+\lambda^T r(z)\},\qquad Z_\rho(x)=\inf_{z\in F}\{f(z)+\rho Q_x(z)\}.$$
--   The projection problem keeps the original constraints and replaces its objective by $Q_x$. Its KKT predicates are the published predicates applied to that new problem. The penalty is $\Phi=f+L\|r\|_1+K\sum_{i,j}\max(0,h_{ij})$ for scalar weights $L,K$. ExactPenalty records local exactness at every original local minimum and equality of global minimizers; it asserts no successful algorithmic step. SmoothRegularProblem and BoundedObjectiveHessians collect the stated smoothness, original-minimum regularity and objective Hessian bound.
--
--   **Formalization Note** Values live in EReal: an empty infimum is $+\infty$ and a value unbounded below is $-\infty$. No finiteness or attainment is inferred by converting a default real infimum. The base carrier is retained verbatim; squared Euclidean length and the one-norm are written explicitly.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), DOI 10.1137/140975991, pp. 1112–1115, (6.1), (6.4)–(6.7); §3, p. 1107

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

noncomputable section

namespace ALADIN.LocalStab.Supplement

open Matrix

variable {N n m nh : ℕ}

/-- Euclidean squared length, independently of the sup norm on the base carrier. -/
def sq {d : ℕ} (v : Fin d → ℝ) : ℝ := v ⬝ᵥ v

def oneNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ j, |v j|

def residual (P : Problem N n m nh) (x : Fin N → Fin n → ℝ) : Fin m → ℝ :=
  ∑ i, P.A i *ᵥ x i - P.b

def blockFeasible (P : Problem N n m nh) : Set (Fin N → Fin n → ℝ) :=
  {y | ∀ i j, P.h i (y i) j ≤ 0}

def proxTerm (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin N → Fin n → ℝ) : ℝ :=
  ∑ i, (y i - x i) ⬝ᵥ (Sig i *ᵥ (y i - x i)) / 2

/-- (6.4): extended-real infimum over all block-feasible points, not local solutions. -/
noncomputable def dualValue (P : Problem N n m nh) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) : EReal :=
  ⨅ y : blockFeasible P,
    ((P.objective y + ρ * proxTerm Sig x y + lam ⬝ᵥ residual P y : ℝ) : EReal)

/-- (6.5), with the original coupling equality and all inequalities retained. -/
noncomputable def primalValue (P : Problem N n m nh) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) (x : Fin N → Fin n → ℝ) : EReal :=
  ⨅ z : P.feasibleSet, ((P.objective z + ρ * proxTerm Sig x z : ℝ) : EReal)

/-- (6.7) is a different objective on the same constraint system. -/
def projectionProblem (P : Problem N n m nh)
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (x : Fin N → Fin n → ℝ) : Problem N n m nh :=
  { P with f := fun i z => (z - x i) ⬝ᵥ (Sig i *ᵥ (z - x i)) / 2 }

def GlobalMin (P : Problem N n m nh) (z : Fin N → Fin n → ℝ) : Prop :=
  z ∈ P.feasibleSet ∧ ∀ w ∈ P.feasibleSet, P.objective z ≤ P.objective w

/-- The printed bound is on objective Hessians, not constraint Hessians. -/
noncomputable def BoundedObjectiveHessians (P : Problem N n m nh) : Prop :=
  ∃ B : ℝ, ∀ i z, z ∈ decoupledFeasibleSet P i → ‖fderiv ℝ (fderiv ℝ (P.f i)) z‖ ≤ B

noncomputable def SmoothRegularProblem (P : Problem N n m nh) : Prop :=
  (∀ i, ContDiff ℝ 2 (P.f i)) ∧ (∀ i, ContDiff ℝ 2 (P.h i)) ∧
  (∀ z, P.IsLocalMinimizer z → ∃ lam κ, P.IsRegularKKTPoint z lam κ)

def phi (P : Problem N n m nh) (L K : ℝ) (x : Fin N → Fin n → ℝ) : ℝ :=
  P.objective x + L * oneNorm (residual P x) +
    K * ∑ i, ∑ j, max 0 (P.h i (x i) j)

/-- Local exactness at every original local minimizer, plus agreement of the global minimizers.
This concerns the original NLP only, and assumes no algorithmic progress. -/
def ExactPenalty (P : Problem N n m nh) (L K : ℝ) : Prop :=
  0 < L ∧ 0 < K ∧
  (∀ z, P.IsLocalMinimizer z → IsLocalMin (phi P L K) z) ∧
  (∀ z, (∀ w, phi P L K z ≤ phi P L K w) ↔ GlobalMin P z)

end ALADIN.LocalStab.Supplement


