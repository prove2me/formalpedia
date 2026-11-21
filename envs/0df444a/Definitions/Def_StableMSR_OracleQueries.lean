-- Prove2me | Definitions.Def_StableMSR_OracleQueries
-- name    : StableMSR_OracleQueries
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-20T20:22:18.171804+00:00
-- url     : https://prove2.me/theorems/72ce8272-67f2-47bc-8e6a-9f9774787f71
-- title:
--   Bounded queries on a real distance oracle and an integer table
-- statement:
--   Expressions read nonnegative integer-memory addresses, make distance queries, compare integer or real values, branch, and sum over points, blocks, or table rows. Register-preserving evaluation is charged in the public RAM model.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_StructuredCompiler
import Definitions.Def_StableMSR_BoundedSumRAM
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.OracleQueries
structure World where
  n : ℕ
  k : ℕ
  rows : ℕ
  dist : Point n → Point n → ℝ
  mem : ℕ → ℤ
inductive Axis where | points | blocks | rows
def Axis.reg : Axis → ℕ | .points=>0 | .blocks=>1 | .rows=>2
def World.size (x : World) : Axis → ℕ | .points=>x.n | .blocks=>x.k | .rows=>x.rows
def World.cap (x : World) := x.n+x.k+x.rows+1
abbrev Env := ℕ → ℕ
abbrev Val := ℤ × ℝ
abbrev Term := World → Env → Val
def iv (z : ℤ) : Val := (z,0)
def rv (a : ℝ) : Val := (0,a)
def flag (p : Prop) [Decidable p] : Val := if p then iv 1 else iv 0
def push (i : ℕ) (ρ : Env) : Env := fun j=>Nat.casesOn j i ρ
inductive Prim where | add | read | query | ile | rle
noncomputable def Prim.val (x : World) : Prim → Val → Val → Val
  | .add,a,b => a+b
  | .read,a,_ => iv (x.mem a.1.toNat)
  | .query,a,b => rv (MinSumFPT.oracleAnswer x.dist a.1 b.1)
  | .ile,a,b => flag (a.1 ≤ b.1)
  | .rle,a,b => flag (a.2 ≤ b.2)
inductive Form : Term → Prop where
  | const (z : ℤ) : Form (fun _ _=>iv z)
  | var (i : ℕ) : Form (fun _ ρ=>iv (ρ i))
  | size (a : Axis) : Form (fun x _=>iv (x.size a))
  | bin (p : Prim) {f g : Term} : Form f → Form g → Form (fun x ρ=>p.val x (f x ρ) (g x ρ))
  | branch {f g h : Term} : Form f → Form g → Form h →
      Form (fun x ρ=>if 1 ≤ (f x ρ).1 then g x ρ else h x ρ)
  | rename {f : Term} : Form f → (σ : ℕ → ℕ) → Form (fun x ρ=>f x (ρ ∘ σ))
  | total (a : Axis) {f : Term} : Form f →
      Form (fun x ρ=>∑i ∈ Finset.range (x.size a),f x (push i ρ))
def Ready (x : World) (s : Store) :=
  (∀a : Axis,s.ptrs a.reg=(x.size a:ℤ)) ∧ ∀i : ℕ,s.imem (i:ℤ)=x.mem i
def Keeps (b : ℕ) (s t : Store) :=
  (∀i < b,t.ptrs i=s.ptrs i ∧ t.regs i=s.regs i) ∧ t.imem=s.imem
def Engine (f : Term) :=
  ∃ p : Polynomial ℕ,∀ (b : ℕ) (src : ℕ→ℕ),3 ≤ b → (∀i,src i < b) →
    ∃c : Cmd,∀ (x : World) (s : Store) (ρ : Env),Ready x s →
      (∀i,s.ptrs (src i)=(ρ i:ℤ)) →
      ∃t z,Executes x.dist c s t z ∧ Keeps b s t ∧
        (t.ptrs b,t.regs b)=f x ρ ∧ z ≤ p.eval x.cap
end StableMSR.Recovery.OracleQueries


