-- Prove2me | Definitions.Def_leantt_syntax
-- name    : leantt_syntax
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T19:11:16.197477+00:00
-- url     : https://prove2.me/theorems/90b0fd73-c91c-4bab-ba2b-beec472ee728
-- title:
--   Syntax and universe levels of the Lean type theory fragment
-- statement:
--   This bundle introduces the abstract syntax layer of the mission: the expressions and the universe level expressions of the base Lean type theory, as presented in section 2.1 of the thesis.
--
--   A **universe level** ℓ is one of five forms: a level variable, zero, the successor of a level, the maximum of two levels, or the impredicative maximum imax(ℓ₁, ℓ₂), which is zero when ℓ₂ is zero and the maximum of the two otherwise. Levels are given semantics by valuation: for a valuation v of level variables by natural numbers, the evaluation eval(v, ℓ) of a level is a natural number.
--
--   **Definitional equality of levels is semantic.** Two levels are definitionally equal when every valuation of their variables by natural numbers agrees on them. The thesis states this characterization in section 2.2 and justifies it by the set-theoretic model construction of its section 6.
--
--   An **expression** is either a bound variable — a de Bruijn index — a universe sort U_ℓ, an application, a lambda, or a pi (dependent function) type. Let binders, definitions, inductive types, recursors, and quotient operations are out of scope for this fragment.
--
--   Two operations manage de Bruijn indices. **Lifting**, liftN(k, n, e), shifts by n those indices of e that are at least k, leaving smaller indices alone; it prepares a term for the insertion of n new binders at index k. **Substitution**, substAt(d, a, e), substitutes a for the de Bruijn index d in e, lifting a by d at the point of use and decrementing the indices above d.
--
--   A **typing context** is a list of type expressions; by convention the head of the list is the innermost binder. The auxiliary operation substCtx(a, Δ) pointwise-substitutes a, for the variable it displaces, into each entry of a context segment Δ, so that substitution can pass through intermediate binders.
--
--   **Formalization Note** With de Bruijn indices in place of the thesis's named variables, the weakening and substitution milestones of the mission are stated with the explicit index arithmetic of liftN, substAt and substCtx, and their proofs live or die on that arithmetic.
-- source:
--   Carneiro 2019, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, https://github.com/digama0/lean-type-theory/releases/tag/v1.0, Section 2.1, p. 6 (expressions and levels); Section 2.2, pp. 6-7 (definitional equality of levels)

import Mathlib

namespace LeanTT

/-- Universe level expressions of the Lean type theory fragment: a
variable, zero, successor, maximum, or impredicative maximum
(thesis section 2.1). -/
inductive Lvl : Type where
  | var : ℕ → Lvl
  | zero : Lvl
  | succ : Lvl → Lvl
  | max : Lvl → Lvl → Lvl
  | imax : Lvl → Lvl → Lvl

namespace Lvl

/-- The denotation of a level under a valuation of its variables by
natural numbers (thesis section 2.2, semantics of level expressions). -/
def eval (v : ℕ → ℕ) : Lvl → ℕ
  | .var n => v n
  | .zero => 0
  | .succ ℓ => eval v ℓ + 1
  | .max a b => Nat.max (eval v a) (eval v b)
  | .imax a b => if eval v b = 0 then 0 else Nat.max (eval v a) (eval v b)

end Lvl

/-- Definitional equality of level expressions, defined semantically:
two levels are equal when every valuation of their variables by natural
numbers agrees on them (thesis section 2.2; the characterization is
justified by the model construction of thesis section 6). -/
def LvlEq (a b : Lvl) : Prop := ∀ v : ℕ → ℕ, Lvl.eval v a = Lvl.eval v b

/-- Expressions of the Lean type theory fragment: bound variables (as
de Bruijn indices), universe sorts, application, lambda, and pi
(thesis section 2.1).  Let binders, definitions, inductive types,
recursors and quotients are out of scope for this fragment. -/
inductive Expr : Type where
  | bvar : ℕ → Expr
  | sort : Lvl → Expr
  | app : Expr → Expr → Expr
  | lam : Expr → Expr → Expr
  | pi : Expr → Expr → Expr

namespace Expr

/-- `liftN k n e` shifts the de Bruijn indices of `e` that are at least
`k` up by `n`; indices below `k` are left alone. -/
def liftN (k n : ℕ) : Expr → Expr
  | .bvar m => if m < k then .bvar m else .bvar (m + n)
  | .sort ℓ => .sort ℓ
  | .app f a => .app (liftN k n f) (liftN k n a)
  | .lam α e => .lam (liftN k n α) (liftN (k + 1) n e)
  | .pi α β => .pi (liftN k n α) (liftN (k + 1) n β)

/-- `substAt d a e` substitutes `a` for the de Bruijn index `d` in `e`,
where `a` is lifted by `d` at the point of use; indices above `d` are
decremented. -/
def substAt (d : ℕ) (a : Expr) : Expr → Expr
  | .bvar m => if m < d then .bvar m else if m = d then liftN 0 d a else .bvar (m - 1)
  | .sort ℓ => .sort ℓ
  | .app f x => .app (substAt d a f) (substAt d a x)
  | .lam α e => .lam (substAt d a α) (substAt (d + 1) a e)
  | .pi α β => .pi (substAt d a α) (substAt (d + 1) a β)

end Expr

/-- A typing context is a list of type expressions; by convention the
head of the list is the innermost binder (de Bruijn convention). -/
abbrev Ctx := List Expr

/-- `substCtx a Δ` substitutes `a` for the variable it displaces in each
entry of `Δ`: the entry at list position `i` sees the displaced variable
at de Bruijn index `Δ.length - i - 1`. -/
def substCtx (a : Expr) : Ctx → Ctx
  | [] => []
  | δ :: Δ => Expr.substAt Δ.length a δ :: substCtx a Δ

end LeanTT


