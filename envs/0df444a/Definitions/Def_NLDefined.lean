-- Prove2me | Definitions.Def_NLDefined
-- name    : NLDefined
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T19:17:47.715308+00:00
-- url     : https://prove2.me/theorems/b6dde234-35d8-47b1-9fff-20a3f7e069c7
-- title:
--   NLDefined
-- statement:
--   Definitions and structural lemmas for NLDefined, from Thiago V. S. Coelho's pinned Soundness and completeness for Nelson’s logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean

import Std
set_option autoImplicit true
set_option autoImplicit false
namespace NLDefined
inductive Formula where
  | var : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | compat : Formula → Formula → Formula
  deriving DecidableEq, Repr
structure Ops (α : Type) where
  neg : α → α
  conj : α → α → α
  compat : α → α → α
def Ops.arr {α : Type} (o : Ops α) (a b : α) : α :=
  o.neg (o.compat a (o.neg b))
def formulaOps : Ops Formula where
  neg := Formula.neg
  conj := Formula.conj
  compat := Formula.compat
def Ops.inc {α : Type} (o : Ops α) (a b : α) : α :=
  o.neg (o.compat a b)
def Ops.eqv {α : Type} (o : Ops α) (a b : α) : α :=
  o.conj (o.arr a b) (o.arr b a)
def Ops.neq {α : Type} (o : Ops α) (a b : α) : α :=
  o.neg (o.eqv a b)
def Ops.distinct3 {α : Type} (o : Ops α) (a b c : α) : α :=
  o.conj (o.conj (o.neq a b) (o.neq b c)) (o.neq a c)
def s1 {α : Type} (o : Ops α) (a : α) : α :=
  o.arr a a
def s2 {α : Type} (o : Ops α) (a b : α) : α :=
  o.arr (o.inc a b) (o.inc b a)
def s3 {α : Type} (o : Ops α) (a : α) : α :=
  o.arr a (o.neg (o.neg a))
def s4 {α : Type} (o : Ops α) (a b : α) : α :=
  o.arr (o.arr a b) (o.compat a b)
def s5 {α : Type} (o : Ops α) (a b c : α) : α :=
  o.arr (o.distinct3 a b c)
    (o.arr (o.conj (o.arr a b) (o.arr b c)) (o.arr a c))
def s6 {α : Type} (o : Ops α) (a b : α) : α :=
  o.eqv (o.conj a b) (o.conj b a)
def s7 {α : Type} (o : Ops α) (a b c : α) : α :=
  o.arr (o.arr (o.conj a b) c)
    (o.arr (o.conj a (o.neg c)) (o.neg b))
inductive Axiom : Formula → Prop where
  | a1 (a : Formula) : Axiom (s1 formulaOps a)
  | a2 (a b : Formula) : Axiom (s2 formulaOps a b)
  | a3 (a : Formula) : Axiom (s3 formulaOps a)
  | a4 (a b : Formula) : Axiom (s4 formulaOps a b)
  | a5 (a b c : Formula) : Axiom (s5 formulaOps a b c)
  | a6 (a b : Formula) : Axiom (s6 formulaOps a b)
  | a7 (a b c : Formula) : Axiom (s7 formulaOps a b c)
inductive Derives (Γ : Formula → Prop) : Formula → Prop where
  | hyp {a : Formula} : Γ a → Derives Γ a
  | ax {a : Formula} : Axiom a → Derives Γ a
  | mp {a b : Formula} :
      Derives Γ a → Derives Γ (formulaOps.arr a b) → Derives Γ b
  | adj {a b : Formula} :
      Derives Γ a → Derives Γ b → Derives Γ (Formula.conj a b)
structure Matrix (α : Type) where
  nonempty : Nonempty α
  op : Ops α
  D : α → Prop
  a1 : ∀ a, D (s1 op a)
  a2 : ∀ a b, D (s2 op a b)
  a3 : ∀ a, D (s3 op a)
  a4 : ∀ a b, D (s4 op a b)
  a5 : ∀ a b c, D (s5 op a b c)
  a6 : ∀ a b, D (s6 op a b)
  a7 : ∀ a b c, D (s7 op a b c)
  mp : ∀ a b, D a → D (op.arr a b) → D b
  adj : ∀ a b, D a → D b → D (op.conj a b)
def eval {α : Type} (o : Ops α) (v : Nat → α) : Formula → α
  | .var n => v n
  | .neg a => o.neg (eval o v a)
  | .conj a b => o.conj (eval o v a) (eval o v b)
  | .compat a b => o.compat (eval o v a) (eval o v b)
def Entails (Γ : Formula → Prop) (a : Formula) : Prop :=
  ∀ (α : Type) (M : Matrix α) (v : Nat → α),
    (∀ b, Γ b → M.D (eval M.op v b)) → M.D (eval M.op v a)
def canonical (Γ : Formula → Prop) : Matrix Formula where
  nonempty := ⟨Formula.var 0⟩
  op := formulaOps
  D := Derives Γ
  a1 := fun a => Derives.ax (Axiom.a1 a)
  a2 := fun a b => Derives.ax (Axiom.a2 a b)
  a3 := fun a => Derives.ax (Axiom.a3 a)
  a4 := fun a b => Derives.ax (Axiom.a4 a b)
  a5 := fun a b c => Derives.ax (Axiom.a5 a b c)
  a6 := fun a b => Derives.ax (Axiom.a6 a b)
  a7 := fun a b c => Derives.ax (Axiom.a7 a b c)
  mp := fun _ _ ha hab => Derives.mp ha hab
  adj := fun _ _ ha hb => Derives.adj ha hb
def Theorem (a : Formula) : Prop := Derives (fun _ => False) a
def Valid (a : Formula) : Prop := Entails (fun _ => False) a
inductive V where
  | a | b | c | d | e | f
  deriving DecidableEq, Repr
def select6 (a b c d e f : V) : V → V
  | .a => a
  | .b => b
  | .c => c
  | .d => d
  | .e => e
  | .f => f
def neg6 : V → V
  | .a => .a
  | .b => .b
  | .c => .d
  | .d => .c
  | .e => .f
  | .f => .e
def compat6 (x y : V) : V :=
  match x with
  | .a => select6 .a .e .e .a .e .a y
  | .b => select6 .e .a .e .a .e .a y
  | .c => select6 .e .e .e .a .e .e y
  | .d => select6 .a .a .a .a .a .a y
  | .e => select6 .e .e .e .a .c .a y
  | .f => select6 .a .a .e .a .a .a y
def conj6 (x y : V) : V :=
  match x with
  | .a => select6 .c .b .c .d .c .b y
  | .b => select6 .b .d .b .d .b .d y
  | .c => select6 .c .b .c .d .c .b y
  | .d => select6 .d .d .d .d .d .d y
  | .e => select6 .c .b .c .d .c .b y
  | .f => select6 .b .d .b .d .b .d y
def designated6 : V → Bool
  | .a | .c | .e => true
  | .b | .d | .f => false
def sixOps : Ops V where
  neg := neg6
  conj := conj6
  compat := compat6
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def sixMatrix : Matrix V where
  nonempty := ⟨V.a⟩
  op := sixOps
  D := fun x => designated6 x = true
  a1 := by intro a; cases a <;> decide
  a2 := by intro a b; cases a <;> cases b <;> decide
  a3 := by intro a; cases a <;> decide
  a4 := by intro a b; cases a <;> cases b <;> decide
  a5 := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  a6 := by intro a b; cases a <;> cases b <;> decide
  a7 := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  mp := by intro a b; cases a <;> cases b <;> decide
  adj := by intro a b; cases a <;> cases b <;> decide
end NLDefined


