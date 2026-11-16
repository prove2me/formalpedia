-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Formula
-- name    : MultiplierAssoc206_Resolution_Supplement_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:32:52.687081+00:00
-- url     : https://prove2.me/theorems/f4976caf-39d4-4cb4-aa45-5dc6cad147c5
-- title:
--   Frege formulas over negation and unbounded disjunction; depth, size, formula substitutions and the clause translation
-- statement:
--   Following Håstad's conventions, a **Frege formula** over a set of Boolean variables is a variable $x$, a negation $\neg F$, or a disjunction $F_1\vee\cdots\vee F_k$ of any finite number $k\ge 0$ of formulas. A conjunction $F_1\wedge\cdots\wedge F_k$ is the abbreviation $\neg(\neg F_1\vee\cdots\vee\neg F_k)$, and $\bot$ is the empty disjunction, which is false under every assignment.
--
--   The **depth** of a formula is the maximum number of alternations between $\vee$ and $\neg$ on a path from its root to a leaf, an alternation being two adjacent connectives of different kinds on the path. Thus a literal has depth $0$, a clause depth at most $1$, $\neg\neg x$ depth $0$, $\neg(\neg x\vee\neg y)$ depth $2$, and a canonical DNF depth at most $3$. The **size** $|F|$ of a formula is its number of symbols.
--
--   A **formula substitution** $\sigma$ maps each variable $x$ to a formula $\sigma(x)$, possibly over other variables; $F^\sigma$ is the result of replacing every occurrence of each variable $x$ in $F$ by $\sigma(x)$.
--
--   A clause $C=\ell_1\vee\cdots\vee\ell_r$ is read as the Frege formula that is the disjunction of its literals, a positive literal being a variable $x$ and a negative literal the formula $\neg x$; the empty clause becomes $\bot$. A CNF $\Phi$ is read as the set of the formulas of its clauses.
--
--   These objects carry the bounded-depth Frege lower bound for $\mathrm{Assoc}_n$: the formulas $\mathrm{Assoc}_n$ and $\mathrm{PM}(H)$ are refuted as sets of Frege formulas, and depth and size are the two resources being bounded.
--
--   **Formalization Note** Formulas are an inductive type with constructors `var`, `not` and `or` (a list of formulas). Depth is computed recursively: a `not` adds one alternation when its argument is a disjunction, and a disjunction adds one alternation for each argument that is a negation; a path may also end at an empty disjunction, so $\neg\bot$ has depth $1$. Size counts symbols in prefix form: a variable is one symbol, $\neg F$ has $|F|+1$ symbols and $F_1\vee\cdots\vee F_k$ has $|F_1|+\cdots+|F_k|+1$; so $\bot$ has size $1$. The literals of a clause, a finite set, are listed in one fixed order (`Finset.toList`). The clause and CNF types are the published ones of the base mission.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.22–23 (printed pp.21–22), §9.1 "Formulas and depth" and "Formula substitutions"

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

set_option autoImplicit false

namespace MultiplierAssoc206.Resolution.Supplement

open Classical

/-! # Frege formulas: depth, size, formula substitutions and the clause translation

Liew, *Associativity of Multiplication Is Hard for Resolution*, §9.1 "Formulas and depth"
(PDF p. 22) and "Formula substitutions" (PDF p. 23). Following Håstad, formulas are built from
variables by negation and disjunctions of unbounded arity; a conjunction is the abbreviation
`¬(¬F₁ ∨ ⋯ ∨ ¬F_k)`, and `⊥` is the empty disjunction. -/

/-- A Frege formula over the variable type `α`: a variable, a negation, or a disjunction of a
finite list of formulas (of any length, including `0`). -/
inductive Formula (α : Type) where
  | var (x : α) : Formula α
  | not (F : Formula α) : Formula α
  | or (Fs : List (Formula α)) : Formula α

namespace Formula

variable {α β : Type}

/-- `⊥`: the empty disjunction. -/
def bot : Formula α := .or []

/-- The value of a formula under an assignment (the empty disjunction is false). -/
def eval (a : α → Bool) : Formula α → Bool
  | .var x => a x
  | .not F => !(eval a F)
  | .or Fs => (Fs.map (eval a)).any id

/-- The root of the formula is a disjunction. -/
def IsOr : Formula α → Bool
  | .or _ => true
  | _ => false

/-- The root of the formula is a negation. -/
def IsNot : Formula α → Bool
  | .not _ => true
  | _ => false

/-- The depth of a formula: the maximum number of alternations between `∨` and `¬` on a path
from its root to a leaf (a variable, or an empty disjunction). An alternation is a pair of
adjacent connective nodes of different kinds on the path. So a literal has depth `0`, a clause
depth at most `1`, `¬¬x` depth `0` and `¬(¬x ∨ ¬y)` depth `2`. -/
def depth : Formula α → ℕ
  | .var _ => 0
  | .not F => depth F + (if F.IsOr then 1 else 0)
  | .or Fs => (Fs.map fun G => depth G + (if G.IsNot then 1 else 0)).foldr max 0

/-- The size of a formula: its number of symbols, counted in prefix form (a variable is one
symbol, `¬F` has one symbol more than `F`, and `∨(F₁,…,F_k)` one more than `F₁,…,F_k`
together). In particular `⊥` has size `1`. -/
def size : Formula α → ℕ
  | .var _ => 1
  | .not F => size F + 1
  | .or Fs => (Fs.map size).sum + 1

/-- `F^σ`: apply the formula substitution `σ` (each variable `x` is replaced by `σ x`). -/
def subst (σ : α → Formula β) : Formula α → Formula β
  | .var x => σ x
  | .not F => .not (subst σ F)
  | .or Fs => .or (Fs.map (subst σ))

end Formula

/-- The formula of a literal: `(x, true)` is `x` and `(x, false)` is `¬x`. -/
def litFormula {α : Type} (l : Literal α) : Formula α :=
  if l.2 then .var l.1 else .not (.var l.1)

/-- The formula of a clause: the disjunction of its literals, listed in one fixed order
(`Finset.toList`). The empty clause becomes `⊥`. -/
noncomputable def clauseFormula {α : Type} (C : Clause α) : Formula α :=
  .or (C.toList.map litFormula)

/-- A CNF read as a set of Frege formulas: the formulas of its clauses. -/
noncomputable def cnfFormulas {α : Type} (Φ : CNF α) : Set (Formula α) :=
  clauseFormula '' (Φ : Set (Clause α))

end MultiplierAssoc206.Resolution.Supplement


