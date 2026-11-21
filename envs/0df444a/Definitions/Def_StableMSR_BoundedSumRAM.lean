-- Prove2me | Definitions.Def_StableMSR_BoundedSumRAM
-- name    : StableMSR_BoundedSumRAM
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-20T17:59:27.242186+00:00
-- url     : https://prove2.me/theorems/c2867977-1fbb-4596-b243-b9fec42cd358
-- title:
--   Bounded sums on the deterministic distance RAM
-- statement:
--   Natural arithmetic with comparison, difference, variable renaming, and bounded summation. An implementation uses scratch registers above its inputs, preserves integer memory, and has uniform polynomial bounds on value and charged execution time.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_StructuredCompiler
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
abbrev Env := ℕ→ℕ
def push (i : ℕ) (ρ : Env) : Env := fun j => Nat.casesOn j i ρ
inductive Gate where | add | cut | leFlag
def Gate.val : Gate→ℕ→ℕ→ℕ
  | .add,a,b => a+b
  | .cut,a,b => a-b
  | .leFlag,a,b => if a≤b then 1 else 0
inductive Form : (Env→ℕ)→Prop where
  | lit (a : ℕ) : Form (fun _=>a)
  | var (i : ℕ) : Form (fun ρ=>ρ i)
  | bin (o : Gate) {f g : Env→ℕ} : Form f → Form g → Form (fun ρ=>o.val (f ρ) (g ρ))
  | rename {f : Env→ℕ} : Form f → (σ : ℕ→ℕ) → Form (fun ρ=>f (ρ ∘ σ))
  | sum {f g : Env→ℕ} : Form f → Form g → Form (fun ρ=>∑ i ∈ Finset.range (f ρ),g (push i ρ))
def Keeps (b : ℕ) (s t : Store) := (∀i<b,t.ptrs i=s.ptrs i) ∧ t.imem=s.imem
def Engine (f : Env→ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (src : ℕ→ℕ) (b : ℕ), (∀i,src i<b) →
    ∃ c : Cmd, ∀ (n : ℕ) (d : Point n→Point n→ℝ) (s : Store) (ρ : Env) (M : ℕ),
      (∀i,ρ i≤M) → (∀i,s.ptrs (src i)=(ρ i:ℤ)) →
      ∃ t z, Executes d c s t z ∧ Keeps b s t ∧ t.ptrs b=(f ρ:ℤ) ∧ z≤p.eval M ∧ f ρ≤p.eval M
def LoopBound {n : ℕ} (d : Point n→Point n→ℝ) (c : Cmd) (guard : Cond)
    (A : ℕ→Store→Prop) (N B : ℕ) : Prop :=
  (∀i s,A i s → (guard.test s ↔ i<N)) ∧
  ∀i<N,∀s,A i s → ∃t z,Executes d c s t z ∧ z≤B ∧ A (i+1) t
def inputEnv (m j : ℕ) : Env := fun i => if i=0 then m else if i=1 then j else 0
end StableMSR.Recovery.Compiler.BoundedSum


