-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
-- name    : Submission_ThreeSumApsp_Lang_Syntax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:51.501776+00:00
-- url     : https://prove2.me/theorems/4df8f25b-a6dc-496c-ad0a-f14716d5611e
-- title:
--   Syntax
-- statement:
--   Definitions and structural lemmas for Syntax, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Syntax.lean

module
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
set_option autoImplicit false
@[expose] public section
namespace Light
inductive Op : Type
  | add | sub | mul
  deriving DecidableEq, Repr
def Op.eval : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
inductive Expr : Type
  | const (n : ℕ)
  | var (x : ℕ)
  | op (o : Op) (a b : Expr)
  | load (a : Expr)
  deriving Repr
inductive Cond : Type
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr
inductive Stmt : Type
  | skip
  | set (x : ℕ) (e : Expr)
  | store (a e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : Cond) (s₁ s₂ : Stmt)
  | while (c : Cond) (s : Stmt)
  | call (p : ℕ) (args : List Expr) (x : ℕ)
  deriving Repr
abbrev Program : Type := List Stmt
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ
def Expr.val (s : State) : Expr → ℤ
  | .const n => n
  | .var x => s.loc x
  | .op o a b => o.eval (a.val s) (b.val s)
  | .load a => s.mem (a.val s).toNat
def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => a.cost + b.cost + 1
  | .load a => a.cost + 1
def Limits.Addr (lim : Limits) (a : ℤ) : Prop := 0 ≤ a ∧ a < lim.space
def Expr.Safe (lim : Limits) (s : State) : Expr → Prop
  | .const n => (n : ℤ) ≤ lim.word
  | .var _ => True
  | .op o a b => a.Safe lim s ∧ b.Safe lim s ∧ |o.eval (a.val s) (b.val s)| ≤ lim.word
  | .load a => a.Safe lim s ∧ lim.Addr (a.val s)
def Cond.Holds (s : State) : Cond → Prop
  | .lt a b => a.val s < b.val s
  | .eq a b => a.val s = b.val s
def Cond.cost : Cond → ℕ
  | .lt a b => a.cost + b.cost + 1
  | .eq a b => a.cost + b.cost + 1
def Cond.Safe (lim : Limits) (s : State) : Cond → Prop
  | .lt a b => a.Safe lim s ∧ b.Safe lim s
  | .eq a b => a.Safe lim s ∧ b.Safe lim s
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0
def memOf (ws : List ℤ) : ℕ → ℤ := fun a => ws.getD a 0
inductive Exec (lim : Limits) (P : Program) : ℕ → Stmt → State → State → ℕ → Prop
  | skip {d σ} : Exec lim P d .skip σ σ 0
  | set {d σ x e} : e.Safe lim σ →
      Exec lim P d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } (e.cost + 1)
  | store {d σ a e} : a.Safe lim σ → e.Safe lim σ → lim.Addr (a.val σ) →
      Exec lim P d (.store a e) σ { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ c₁ c₂} : Exec lim P d s₁ σ σ' c₁ → Exec lim P d s₂ σ' σ'' c₂ →
      Exec lim P d (.seq s₁ s₂) σ σ'' (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ k} : c.Safe lim σ → c.Holds σ → Exec lim P d s₁ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ k} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d s₂ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d (.while c s) σ σ (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s k₁ k₂} : c.Safe lim σ → c.Holds σ → Exec lim P d s σ σ' k₁ →
      Exec lim P d (.while c s) σ' σ'' k₂ → Exec lim P d (.while c s) σ σ'' (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body k} : (∀ e ∈ args, e.Safe lim σ) → P[p]? = some body → d < lim.depth →
      Exec lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k →
      Exec lim P d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
        ((args.map Expr.cost).sum + 2 + k)
def State.Bounded (lim : Limits) (σ : State) : Prop :=
  (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word
end Light


