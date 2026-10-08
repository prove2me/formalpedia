-- Prove2me | Definitions.Def_VarStorageQN_LeastChange_SecantProblem
-- name    : VarStorageQN_LeastChange_SecantProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:29.75731+00:00
-- url     : https://prove2.me/theorems/fa27101e-581c-4eda-9f5b-d91f605ea7a5
-- title:
--   Feasible secant perturbations and the weight vector
-- statement:
--   Let $B$ be a bounded operator on a real Hilbert space, and let $s,y$ be vectors. The feasible Hilbert–Schmidt perturbations for the nonsymmetric problem (A.4) and symmetric problem (A.6) are, respectively,
--
--   $$\Pi=\{P\in L_2(\mathcal H):(B+P)s=y\},\qquad
--   \Pi_S=\{P\in L_2(\mathcal H):P=P^*,\ (B+P)s=y\}. $$
--
--   For a bijective bounded operator $R$, the weight vector appearing in the update formula is $c=R^{-*}R^{-1}s$. These definitions place summability and the secant equation inside the feasible sets used in the two minimization theorems.
--
--   **Formalization Note** `Feas` and `FeasSym` use an arbitrary Hilbert basis to test Hilbert–Schmidt membership. A continuous linear equivalence represents the paper's bijective bounded operator, whose inverse is bounded. `weight R s` applies the adjoint of $R^{-1}$ to $R^{-1}s$.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), pp. 27–28, Annex, Π, (A.4), Π_S, (A.6), and Proposition A.2

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The feasible Hilbert–Schmidt perturbations Π of (A.4). -/
def Feas {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H) (y s : H) :
    Set (H →L[ℝ] H) :=
  {P | HSSummable b P ∧ (B + P) s = y}

/-- The feasible self-adjoint Hilbert–Schmidt perturbations Π_S of (A.6). -/
def FeasSym {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H) (y s : H) :
    Set (H →L[ℝ] H) :=
  {P | HSSummable b P ∧ IsSelfAdjoint P ∧ (B + P) s = y}

/-- The weight `c = R^{-*} R^{-1} s` in Propositions A.1 and A.2. -/
noncomputable def weight (R : H ≃L[ℝ] H) (s : H) : H :=
  adjoint (R.symm : H →L[ℝ] H) (R.symm s)

end VarStorageQN.LeastChange


