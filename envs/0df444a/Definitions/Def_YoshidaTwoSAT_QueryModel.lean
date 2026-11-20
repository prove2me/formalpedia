-- Prove2me | Definitions.Def_YoshidaTwoSAT_QueryModel
-- name    : YoshidaTwoSAT_QueryModel
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-20T01:49:45.098188+00:00
-- url     : https://prove2.me/theorems/d152bded-533d-45b1-b20d-fa55ce96c913
-- title:
--   Bounded-degree incidence queries and randomized testers
-- statement:
--   The oracle reports one incident clause or an empty slot for a selected variable and index. A randomized tester samples an adaptive decision tree of bounded depth. The exact-width subclass consists of clauses on two distinct variables.
-- source:
--   Yuichi Yoshida, A One-Sided Sublinear-Query Tester for Bounded-Degree 2SAT, https://arxiv.org/abs/2611.16176, pp. 1–2, bounded-degree incidence-query model and Section 6.3

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_YoshidaTwoSAT_Formula

namespace TwoSAT

/-- Each binary clause is written in increasing variable order. -/
def Clause.canonical {n} : Clause (Fin n) → Prop
  | .pair a b => a.var < b.var
  | _ => True

abbrev Answer (n : ℕ) := Option (Clause (Fin n))
abbrev Oracle (n d : ℕ) := Fin n → Fin d → Answer n

/-- Soundness and unique coverage tie every non-null slot to the formula. -/
structure Input (n d : ℕ) where
  formula : List (Clause (Fin n))
  distinct : formula.Nodup
  canonical : ∀ c ∈ formula, c.canonical
  oracle : Oracle n d
  sound : ∀ x i c, oracle x i = some c → c ∈ formula ∧ c.incident x
  coverage : ∀ x c, c ∈ formula → c.incident x → ∃! i, oracle x i = some c

/-- An adaptive incidence-query algorithm with a worst-case query budget.
A leaf returns true on rejection. -/
inductive Tree (n d : ℕ) : ℕ → Type where
  | leaf {q} (reject : Bool) : Tree n d q
  | ask {q} (x : Fin n) (i : Fin d) (next : Answer n → Tree n d q) : Tree n d (q + 1)

def Tree.run {n d : ℕ} (o : Oracle n d) : {q : ℕ} → Tree n d q → Bool
  | _, .leaf reject => reject
  | _, .ask x i next => Tree.run o (next (o x i))

/-- The random tree is sampled independently of the unknown input. -/
noncomputable def rejection {n d q} (alg : PMF (Tree n d q)) (F : Input n d) : ENNReal :=
  (alg.map (fun tr => tr.run F.oracle)) true

end TwoSAT

namespace TwoSAT.Reduction

def Exact {n d} (F : Input n d) : Prop :=
  ∀ c ∈ F.formula, ∃ a b, c = .pair a b ∧ a.var < b.var

end TwoSAT.Reduction


