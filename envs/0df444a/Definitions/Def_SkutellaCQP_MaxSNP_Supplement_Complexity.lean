-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Complexity
-- name    : SkutellaCQP_MaxSNP_Supplement_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:48:43.632443+00:00
-- url     : https://prove2.me/theorems/cfc2b557-087b-484f-961c-cfaa87a2e2aa
-- title:
--   Optimization problems, L-reductions and standard MAX SNP hardness
-- statement:
--   An optimization problem specifies encoded inputs and solutions, validity, feasibility, a real objective and an optimization direction. Its optimum is the infimum or supremum of exactly its feasible values. The concrete problems below have nonempty feasible sets and finite attained optima on every valid instance.
--
--   An L-reduction consists of two uniform finite-alphabet polynomial-time maps and constants $\alpha,\beta>0$. Valid source inputs map to valid target inputs, feasible target solutions recover feasible source solutions, and
--   $$\operatorname{OPT}_Q(R(I))\le\alpha\operatorname{OPT}_P(I),\qquad |\operatorname{OPT}_P(I)-\operatorname{val}_P(g(I,S))|\le\beta|\operatorname{OPT}_Q(R(I))-\operatorname{val}_Q(S)|.$$
--   MAX SNP presentations use arbitrary fixed finite relational vocabularies and a quantifier-free formula $\varphi(A,S,x)$, maximizing over guessed relations $S$ the number of tuples $x$ satisfying the formula. Relations are explicit truth tables and the finite universe is explicit in the input. MAX SNP hardness means that every such presentation has an L-reduction to the target; it also covers their closure under L-reductions. It is not defined as an arbitrary predicate or merely as the two numerical inequalities for one gadget.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 32–33; L-reductions, with the standard MAX SNP interpretation cited there

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Encoding

namespace SkutellaCQP.MaxSNP.Supplement

open Finset

/-- A finitely encoded optimization problem. Optimum values below are computed from the
feasible solutions; they are never free parameters. -/
structure OptimizationProblem where
  Input : Type
  Solution : Type
  inputCode : Input → List Bool
  solutionCode : Solution → List Bool
  valid : Input → Prop
  feasible : Input → Solution → Prop
  value : Input → Solution → ℝ
  minimize : Bool

/-- The infimum/supremum over exactly the feasible solutions. Every problem used here has
nonempty feasible sets on valid inputs; source MAX SNP values form a finite bounded set,
and target scheduling values are bounded below by zero and attain their infimum. -/
noncomputable def OptimizationProblem.opt (P : OptimizationProblem) (I : P.Input) : ℝ :=
  if P.minimize then sInf {v | ∃ s, P.feasible I s ∧ P.value I s = v}
  else sSup {v | ∃ s, P.feasible I s ∧ P.value I s = v}

/-- A genuine L-reduction: uniform polynomial-time transformations and both numerical
conditions, including feasibility of the recovered solution. -/
structure LReduction (P Q : OptimizationProblem) where
  α : ℝ
  β : ℝ
  alpha_pos : 0 < α
  beta_pos : 0 < β
  forward : P.Input → Q.Input
  backward : P.Input × Q.Solution → P.Solution
  forward_poly : PolyMapOn P.valid P.inputCode Q.inputCode forward
  backward_poly : PolyMapOn (fun x : P.Input × Q.Solution => P.valid x.1) (fun x => wordPair (P.inputCode x.1) (Q.solutionCode x.2))
    P.solutionCode backward
  valid_forward : ∀ I, P.valid I → Q.valid (forward I)
  optimum_bound : ∀ I, P.valid I → Q.opt (forward I) ≤ α * P.opt I
  error_bound : ∀ I s, P.valid I → Q.feasible (forward I) s →
    P.feasible I (backward (I, s)) ∧
      |P.opt I - P.value I (backward (I, s))| ≤ β * |Q.opt (forward I) - Q.value (forward I) s|

/-- A finite relational vocabulary. -/
structure Vocabulary where
  count : ℕ
  arity : Fin count → ℕ

/-- Quantifier-free formulas used in the standard MAX SNP presentation:
maximize, over guessed relations S, the number of tuples x satisfying φ(A,S,x).
Input vocabularies, guessed vocabularies, tuple arity and formula are fixed for a problem. -/
inductive SNPFormula (A S : Vocabulary) (v : ℕ) where
  | truth : SNPFormula A S v
  | equal : Fin v → Fin v → SNPFormula A S v
  | input (r : Fin A.count) : (Fin (A.arity r) → Fin v) → SNPFormula A S v
  | guess (r : Fin S.count) : (Fin (S.arity r) → Fin v) → SNPFormula A S v
  | neg : SNPFormula A S v → SNPFormula A S v
  | conj : SNPFormula A S v → SNPFormula A S v → SNPFormula A S v
  | disj : SNPFormula A S v → SNPFormula A S v → SNPFormula A S v

/-- Explicit finite input structure. Relations are lexicographic truth tables. -/
structure RelationalInput (A : Vocabulary) where
  size : ℕ
  table : Fin A.count → List Bool

def RelationalInput.Valid {A : Vocabulary} (I : RelationalInput A) : Prop :=
  ∀ r, (I.table r).length = I.size ^ A.arity r

/-- Explicit universe (unary size) and binary relation tables, the standard encoding of a
finite relational structure. It does not encode a huge implicit universe in logarithmic size. -/
def RelationalInput.code {A : Vocabulary} (I : RelationalInput A) : List Bool :=
  listCode (fun b : Bool => [b]) (List.replicate I.size true) ++
  listCode (listCode fun b : Bool => [b]) ((List.finRange A.count).map I.table)

/-- Tuple index in a relation truth table. -/
def tupleIndex {n k : ℕ} (x : Fin k → Fin n) : ℕ :=
  (List.ofFn x).foldl (fun a b => a * n + b.val) 0

/-- Evaluation of a quantifier-free formula in a finite input and guessed structure. -/
def SNPFormula.eval {A S : Vocabulary} {v : ℕ} (I : RelationalInput A)
    (guess : Fin S.count → List Bool) (env : Fin v → Fin I.size) : SNPFormula A S v → Bool
  | .truth => true
  | .equal x y => decide (env x = env y)
  | .input r args => (I.table r)[tupleIndex (fun k => env (args k))]?.getD false
  | .guess r args => (guess r)[tupleIndex (fun k => env (args k))]?.getD false
  | .neg φ => !(φ.eval I guess env)
  | .conj φ ψ => φ.eval I guess env && ψ.eval I guess env
  | .disj φ ψ => φ.eval I guess env || ψ.eval I guess env

/-- The canonical optimization problem of a MAX SNP formula. Hardness against these
presentations is hardness against MAX SNP and its closure under L-reductions. -/
noncomputable def snpProblem (A S : Vocabulary) (v : ℕ) (φ : SNPFormula A S v) : OptimizationProblem where
  Input := RelationalInput A
  Solution := Fin S.count → List Bool
  inputCode := RelationalInput.code
  solutionCode := fun s => listCode (listCode fun b : Bool => [b]) ((List.finRange S.count).map s)
  valid := RelationalInput.Valid
  feasible := fun I s => ∀ r, (s r).length = I.size ^ S.arity r
  value := fun I s => ((univ.filter fun env : Fin v → Fin I.size => φ.eval I s env).card : ℝ)
  minimize := false

/-- Standard MAX SNP hardness under L-reductions, quantified over all finite vocabularies
and all quantifier-free MAX SNP formulas. This is not a renamed reduction from one problem. -/
def MaxSNPHard (Q : OptimizationProblem) : Prop :=
  ∀ (A S : Vocabulary) (v : ℕ) (φ : SNPFormula A S v), Nonempty (LReduction (snpProblem A S v φ) Q)

end SkutellaCQP.MaxSNP.Supplement


