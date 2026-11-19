-- Prove2me | Definitions.Def_ltt3_syntax
-- name    : ltt3_syntax
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T14:43:45.843816+00:00
-- url     : https://prove2.me/theorems/3d01ac23-0b5a-4448-9c82-1b94389fa527
-- title:
--   Concrete syntax of the proof-split language (thesis §6.1)
-- statement:
--   The expression grammar of the proof-split language used for the set-theoretic model in Section 6 of Carneiro's thesis. Expressions include de Bruijn variables, concrete-number universes $\mathsf{U}_n$, the split function types $\forall x:\alpha.\beta$ (propositional) and $\Pi x:\alpha.\beta$ (non-propositional) with their proof/type lambdas and applications, $\mathsf{let}$ binders, and the menagerie of basic inductive types taken as primitive: the empty type, unit, dependent sum $\Sigma$, binary sum, universe lift, propositional truncation, $\mathsf{W}$-types, equality, and accessibility, each with constructors and recursors, together with quotient types, $\mathsf{propext}$, $\mathsf{nonempty}$ and $\mathsf{choice}$. The operations $\mathrm{lift}$ and $\mathrm{subst}$ implement de Bruijn index shifting and capture-avoiding substitution; $\mathrm{inst}$ instantiates the outermost binder. A context is a list of type expressions with the head as the innermost binder. **Formalization Note.** Following Section 6.1, levels are concrete natural numbers rather than level expressions, and the propositional/non-propositional split is syntactic; the menagerie is primitive here, with the reduction of general inductive specifications to it established separately (Part II).
-- source:
--   M. Carneiro, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, 2019, https://github.com/digama0/lean-type-theory, Section 6.1 (proof-split language) and Section 5.1 (the menagerie).

import Mathlib

/-!
# The Type Theory of Lean, part III: concrete syntax of the proof-split language

Concrete syntax of the proof-split language of Mario Carneiro's thesis
"The Type Theory of Lean" (Carnegie Mellon University, 2019), section 6.1:
the propositional forall (`piP`) and the non-propositional Pi type (`piT`)
are syntactically separate, proof and type lambdas/applications are
distinguished, universe levels are concrete natural numbers (`sort n`),
and the menagerie of basic inductive types (section 5.1) is taken as
primitive. Bound variables use de Bruijn indices. This is the source
language for the set-theoretic interpretation of section 6.
-/

namespace LeanTT3

inductive E : Type where
  | bvar : Nat → E
  | sort : Nat → E
  | ulift : Nat → Nat → E → E
  | appP : E → E → E
  | appT : E → E → E
  | lamP : E → E → E
  | lamT : E → E → E
  | piP : E → E → E
  | piT : E → E → E
  | letE : E → E → E → E
  | empty : E
  | recEmpty : E → E
  | unit : E
  | tt : E
  | sigma : E → E → E
  | pair : E → E → E
  | fst : E → E
  | snd : E → E
  | sum : E → E → E
  | inl : E → E
  | inr : E → E
  | recSum : E → E → E → E
  | up : E → E
  | down : E → E
  | trunc : E → E
  | abs : E → E
  | recTrunc : E → E → E → E
  | wT : E → E → E
  | sup : E → E → E
  | recW : E → E → E
  | eq : E → E → E → E
  | refl : E → E
  | recEq : E → E → E → E → E
  | acc : E → E → E → E
  | introAcc : E → E → E
  | recAcc : E → E → E → E
  | quot : E → E → E
  | mkQuot : E → E → E → E
  | liftQuot : E → E → E → E → E
  | soundQuot : E → E
  | propext : E
  | nonempty : E → E
  | choice : E

namespace E

def lift (k n : Nat) : E → E
  | .bvar m => if m < k then .bvar m else .bvar (m + n)
  | .sort u => .sort u
  | .ulift u v e => .ulift u v (lift k n e)
  | .appP x0 x1 => E.appP (lift k n x0) (lift k n x1)
  | .appT x0 x1 => E.appT (lift k n x0) (lift k n x1)
  | .lamP x0 x1 => E.lamP (lift k n x0) (lift (k+1) n x1)
  | .lamT x0 x1 => E.lamT (lift k n x0) (lift (k+1) n x1)
  | .piP x0 x1 => E.piP (lift k n x0) (lift (k+1) n x1)
  | .piT x0 x1 => E.piT (lift k n x0) (lift (k+1) n x1)
  | .letE x0 x1 x2 => E.letE (lift k n x0) (lift k n x1) (lift (k+1) n x2)
  | .empty => E.empty
  | .recEmpty x0 => E.recEmpty (lift k n x0)
  | .unit => E.unit
  | .tt => E.tt
  | .sigma x0 x1 => E.sigma (lift k n x0) (lift (k+1) n x1)
  | .pair x0 x1 => E.pair (lift k n x0) (lift k n x1)
  | .fst x0 => E.fst (lift k n x0)
  | .snd x0 => E.snd (lift k n x0)
  | .sum x0 x1 => E.sum (lift k n x0) (lift k n x1)
  | .inl x0 => E.inl (lift k n x0)
  | .inr x0 => E.inr (lift k n x0)
  | .recSum x0 x1 x2 => E.recSum (lift k n x0) (lift k n x1) (lift k n x2)
  | .up x0 => E.up (lift k n x0)
  | .down x0 => E.down (lift k n x0)
  | .trunc x0 => E.trunc (lift k n x0)
  | .abs x0 => E.abs (lift k n x0)
  | .recTrunc x0 x1 x2 => E.recTrunc (lift k n x0) (lift k n x1) (lift k n x2)
  | .wT x0 x1 => E.wT (lift k n x0) (lift (k+1) n x1)
  | .sup x0 x1 => E.sup (lift k n x0) (lift k n x1)
  | .recW x0 x1 => E.recW (lift k n x0) (lift k n x1)
  | .eq x0 x1 x2 => E.eq (lift k n x0) (lift k n x1) (lift k n x2)
  | .refl x0 => E.refl (lift k n x0)
  | .recEq x0 x1 x2 x3 => E.recEq (lift k n x0) (lift k n x1) (lift k n x2) (lift k n x3)
  | .acc x0 x1 x2 => E.acc (lift k n x0) (lift k n x1) (lift k n x2)
  | .introAcc x0 x1 => E.introAcc (lift k n x0) (lift k n x1)
  | .recAcc x0 x1 x2 => E.recAcc (lift k n x0) (lift k n x1) (lift k n x2)
  | .quot x0 x1 => E.quot (lift k n x0) (lift k n x1)
  | .mkQuot x0 x1 x2 => E.mkQuot (lift k n x0) (lift k n x1) (lift k n x2)
  | .liftQuot x0 x1 x2 x3 => E.liftQuot (lift k n x0) (lift k n x1) (lift k n x2) (lift k n x3)
  | .soundQuot x0 => E.soundQuot (lift k n x0)
  | .propext => E.propext
  | .nonempty x0 => E.nonempty (lift k n x0)
  | .choice => E.choice

def subst (d : Nat) (a : E) : E → E
  | .bvar m => if m < d then .bvar m else if m = d then lift 0 d a else .bvar (m - 1)
  | .sort u => .sort u
  | .ulift u v e => .ulift u v (subst d a e)
  | .appP x0 x1 => E.appP (subst d a x0) (subst d a x1)
  | .appT x0 x1 => E.appT (subst d a x0) (subst d a x1)
  | .lamP x0 x1 => E.lamP (subst d a x0) (subst (d+1) a x1)
  | .lamT x0 x1 => E.lamT (subst d a x0) (subst (d+1) a x1)
  | .piP x0 x1 => E.piP (subst d a x0) (subst (d+1) a x1)
  | .piT x0 x1 => E.piT (subst d a x0) (subst (d+1) a x1)
  | .letE x0 x1 x2 => E.letE (subst d a x0) (subst d a x1) (subst (d+1) a x2)
  | .empty => E.empty
  | .recEmpty x0 => E.recEmpty (subst d a x0)
  | .unit => E.unit
  | .tt => E.tt
  | .sigma x0 x1 => E.sigma (subst d a x0) (subst (d+1) a x1)
  | .pair x0 x1 => E.pair (subst d a x0) (subst d a x1)
  | .fst x0 => E.fst (subst d a x0)
  | .snd x0 => E.snd (subst d a x0)
  | .sum x0 x1 => E.sum (subst d a x0) (subst d a x1)
  | .inl x0 => E.inl (subst d a x0)
  | .inr x0 => E.inr (subst d a x0)
  | .recSum x0 x1 x2 => E.recSum (subst d a x0) (subst d a x1) (subst d a x2)
  | .up x0 => E.up (subst d a x0)
  | .down x0 => E.down (subst d a x0)
  | .trunc x0 => E.trunc (subst d a x0)
  | .abs x0 => E.abs (subst d a x0)
  | .recTrunc x0 x1 x2 => E.recTrunc (subst d a x0) (subst d a x1) (subst d a x2)
  | .wT x0 x1 => E.wT (subst d a x0) (subst (d+1) a x1)
  | .sup x0 x1 => E.sup (subst d a x0) (subst d a x1)
  | .recW x0 x1 => E.recW (subst d a x0) (subst d a x1)
  | .eq x0 x1 x2 => E.eq (subst d a x0) (subst d a x1) (subst d a x2)
  | .refl x0 => E.refl (subst d a x0)
  | .recEq x0 x1 x2 x3 => E.recEq (subst d a x0) (subst d a x1) (subst d a x2) (subst d a x3)
  | .acc x0 x1 x2 => E.acc (subst d a x0) (subst d a x1) (subst d a x2)
  | .introAcc x0 x1 => E.introAcc (subst d a x0) (subst d a x1)
  | .recAcc x0 x1 x2 => E.recAcc (subst d a x0) (subst d a x1) (subst d a x2)
  | .quot x0 x1 => E.quot (subst d a x0) (subst d a x1)
  | .mkQuot x0 x1 x2 => E.mkQuot (subst d a x0) (subst d a x1) (subst d a x2)
  | .liftQuot x0 x1 x2 x3 => E.liftQuot (subst d a x0) (subst d a x1) (subst d a x2) (subst d a x3)
  | .soundQuot x0 => E.soundQuot (subst d a x0)
  | .propext => E.propext
  | .nonempty x0 => E.nonempty (subst d a x0)
  | .choice => E.choice

def inst (b a : E) : E := subst 0 a b

end E

abbrev Ctx := List E

end LeanTT3


