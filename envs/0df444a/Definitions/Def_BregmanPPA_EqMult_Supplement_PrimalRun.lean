-- Prove2me | Definitions.Def_BregmanPPA_EqMult_Supplement_PrimalRun
-- name    : BregmanPPA_EqMult_Supplement_PrimalRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:21:19.688801+00:00
-- url     : https://prove2.me/theorems/0622756e-5598-46a9-a36c-48535561b332
-- title:
--   Recursion (6) — primal Bregman minimization runs and Theorem 5 alternatives
-- statement:
--   Let $X$ be a subset of a finite-dimensional real inner-product space, let $f$ take values in $(-\infty,+\infty]$, and let $h$ be a Bregman function with open zone $S$. The effective feasible set is $F=\{z\in X:f(z)<+\infty\}$. A minimizer is a finite-valued point of $X$ attaining its smallest objective value. With positive steps $c_k$, a primal run consists of points $x^k\in S$ satisfying
--
--   $$x^{k+1}\in\operatorname*{argmin}_{z\in X}\left\{f(z)+c_k^{-1}D_h(z,x^k)\right\},\qquad k\ge0.$$
--
--   The objective is extended by $+\infty$ outside $\overline S$, the natural first-argument domain of $D_h$. Each selected successor has finite $f$ value; the initial point need only belong to $S$. Alternative (i) means $\overline F\subseteq S$ and $\nabla h(S)$ is the whole ambient space. Alternative (ii) means $f$ is finite, continuous and bounded below on $X$.
--
--   This vocabulary expresses all four clauses of Theorem 5, including the boundary obstruction to its printed alternative (ii).
--
--   **Formalization Note** The general Bregman and convex-program objects are the published definitions. Real-valued $h$ is read only on $\overline S$, and gradients only on $S$. The finite-real part of $f$ is used for continuity only together with its explicit finiteness. Under the standing convexity and relative-interior condition, $F\subseteq\overline S$, so extending the objective adds no restriction to the source minimization problem. The predicates themselves do not assert any convergence or existence theorem.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 210–211, problem (5), recursion (6), Theorem 5; DOI 10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_EqMult_EqConstrainedProgram

open BregmanPPA.Convergence

namespace BregmanPPA.EqMult.Supplement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The effective feasible set `(dom f) ∩ X`; all uses assume `f` never equals bottom. -/
def effectiveFeasible (X : Set H) (f : H → EReal) : Set H :=
  {z | z ∈ X ∧ f z ≠ ⊤}

/-- An attained finite minimum of problem (5). -/
def IsMinimizer (X : Set H) (f : H → EReal) (z : H) : Prop :=
  z ∈ X ∧ f z ≠ ⊤ ∧ ∀ y ∈ X, f z ≤ f y

/-- The objective in (6), extended by top outside the natural first-argument domain of D. -/
noncomputable def primalObjective (S : Set H) (h : H → ℝ) (f : H → EReal)
    (c : ℝ) (y z : H) : EReal :=
  open Classical in
  if z ∈ closure S then f z + ((c⁻¹ * bregmanD h z y : ℝ) : EReal) else ⊤

/-- Recursion (6): all iterates are in S; each successor is a finite minimizer over X.
The initial iterate need not be in X or dom f. -/
noncomputable def IsPrimalRun (S X : Set H) (h : H → ℝ) (f : H → EReal)
    (c : ℕ → ℝ) (x : ℕ → H) : Prop :=
  (∀ k, x k ∈ S) ∧ ∀ k, x (k + 1) ∈ X ∧ f (x (k + 1)) ≠ ⊤ ∧
    ∀ y ∈ X, primalObjective S h f (c k) (x k) (x (k + 1)) ≤
      primalObjective S h f (c k) (x k) y

/-- Theorem 5(i): one closure of the entire effective feasible set, and the zone gradient image. -/
def AlternativeI (S X : Set H) (h : H → ℝ) (f : H → EReal) : Prop :=
  closure (effectiveFeasible X f) ⊆ S ∧ gradient h '' S = Set.univ

/-- Theorem 5(ii): finiteness, continuity and a real lower bound, only on X. -/
def AlternativeII (X : Set H) (f : H → EReal) : Prop :=
  (∀ z ∈ X, f z ≠ ⊤ ∧ f z ≠ ⊥) ∧ ContinuousOn (fun z => (f z).toReal) X ∧
    ∃ b : ℝ, ∀ z ∈ X, (b : EReal) ≤ f z

end BregmanPPA.EqMult.Supplement


