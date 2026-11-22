-- Prove2me | Definitions.Def_K230_fol
-- name    : K230_fol
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:12:51.068811+00:00
-- url     : https://prove2.me/theorems/c1b042c4-8a06-41e4-9c10-6a6f1b809236
-- title:
--   K230: first-order set-theoretic syntax
-- statement:
--   The first-order language of set theory used by K230: a binary membership predicate $\in$ and a binary equality predicate $\equiv$, with no function symbols, so terms are de Bruijn variable indices. Formulas are built from falsity $\bot$, atoms, conjunction, disjunction, implication, and the universal and existential quantifiers. The file defines capture-avoiding substitution `subst`, the shift `up`/`shift`, iterated universal closure `forallTimes`, the free-variable bound `fb`, closedness `closedf`, and the four equality axioms. This specializes the Coq Library of Undecidability's `FOL.Syntax.Core`/`Subst` to the minimal set signature (`sig_empty` + `ZF_pred_sig`) and `Std_tr.v`'s `fb`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KP0.v

namespace K230
inductive Pred where | elem | equal
inductive Form where
  | falsity : Form
  | atom : Pred → Nat → Nat → Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | impl : Form → Form → Form
  | all : Form → Form
  | ex : Form → Form
def mem (x y : Nat) : Form := .atom .elem x y
def eqf (x y : Nat) : Form := .atom .equal x y
def bot : Form := .falsity
def neg (a : Form) : Form := .impl a .falsity
def iff' (a b : Form) : Form := .conj (.impl a b) (.impl b a)
def scons (x : Nat) (σ : Nat → Nat) : Nat → Nat
  | 0 => x
  | n + 1 => σ n
def up (σ : Nat → Nat) : Nat → Nat := scons 0 (fun n => σ n + 1)
def shift : Nat → Nat := fun n => n + 1
def subst (φ : Form) (σ : Nat → Nat) : Form :=
  match φ with
  | .falsity => .falsity
  | .atom p x y => .atom p (σ x) (σ y)
  | .conj a b => .conj (subst a σ) (subst b σ)
  | .disj a b => .disj (subst a σ) (subst b σ)
  | .impl a b => .impl (subst a σ) (subst b σ)
  | .all a => .all (subst a (up σ))
  | .ex a => .ex (subst a (up σ))
def forallTimes : Nat → Form → Form
  | 0, φ => φ
  | n + 1, φ => .all (forallTimes n φ)
def fb : Nat → Form → Prop
  | _, .falsity => True
  | N, .atom _ x y => x < N ∧ y < N
  | N, .conj a b => fb N a ∧ fb N b
  | N, .disj a b => fb N a ∧ fb N b
  | N, .impl a b => fb N a ∧ fb N b
  | N, .all a => fb (N + 1) a
  | N, .ex a => fb (N + 1) a
def closedf (φ : Form) : Prop := fb 0 φ
def axRefl' : Form := .all (eqf 0 0)
def axSym' : Form := .all (.all (.impl (eqf 1 0) (eqf 0 1)))
def axTrans' : Form := .all (.all (.all (.impl (eqf 2 1) (.impl (eqf 1 0) (eqf 2 0)))))
def axEqElem' : Form := .all (.all (.all (.all (.impl (eqf 3 1) (.impl (eqf 2 0) (.impl (mem 3 2) (mem 1 0)))))))
def equalityAxioms : List Form := [axRefl', axSym', axTrans', axEqElem']
end K230


