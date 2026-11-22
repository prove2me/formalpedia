-- Prove2me | Definitions.Def_SubspaceEvasion312_GMC_core
-- name    : SubspaceEvasion312_GMC_core
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T23:09:59.278077+00:00
-- url     : https://prove2.me/theorems/1129b501-5a33-4f6d-a4fa-e0dca5c7a38d
-- title:
--   Execution calculus for generator-matrix compiler
-- statement:
--   This module provides an elementary execution calculus for the field-register machine used by the explicit subspace-evasion construction. It defines the effect of every instruction, bounded finite reachability, composition of execution segments, and translated memory addresses for a nested computation. These are operational utilities needed to compile repeated generator-matrix entry calls into one fixed program.
-- source:
--   Brakensiek et al., STOC 2027 submission #312, complexity conventions and proof of Theorem 8, printed pp.7–8 (PDF pp.8–9); supporting formal infrastructure for the generic implementation of Theorem 17, printed p.10 (PDF p.11).

import Definitions.Def_SubspaceEvasion312_Explicit_effective

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.GMC
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

def eff (ns : List ℕ) (xs : List F) (z : MachineState F) : Instruction F → MachineState F
  | .halt => z
  | .literal d v => {z with pc := z.pc + 1, natReg := Function.update z.natReg d v}
  | .inputNat d i => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (ns.getD i 0)}
  | .addNat d a b => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a + z.natReg b)}
  | .subNat d a b => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a - z.natReg b)}
  | .mulNat d a b => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a * z.natReg b)}
  | .divNat d a b => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a / z.natReg b)}
  | .modNat d a b => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a % z.natReg b)}
  | .branchNat a b y n => {z with pc := if z.natReg a = z.natReg b then y else n}
  | .constant d v => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d v}
  | .add d a b => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a + z.fieldReg b)}
  | .sub d a b => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a - z.fieldReg b)}
  | .mul d a b => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a * z.fieldReg b)}
  | .inv d a => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a)⁻¹}
  | .load d a => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg (z.natReg a))}
  | .store a s => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg (z.natReg a) (z.fieldReg s)}
  | .input d a => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (xs.getD (z.natReg a) 0)}
  | .branch a b y n => by classical exact {z with pc := if z.fieldReg a = z.fieldReg b then y else n}
  | .jump p => {z with pc := p}
  | .output s => {z with pc := z.pc + 1, out := z.fieldReg s :: z.out}
  | .outputNat s => {z with pc := z.pc + 1, natOut := z.natReg s :: z.natOut}

theorem step_eq {P : Program F} {ns : List ℕ} {xs : List F} {z : MachineState F}
    {ins : Instruction F} (h : P[z.pc]? = some ins) (hh : ins ≠ .halt) :
    step P ns xs z = some (eff ns xs z ins) := by
  cases ins <;> simp_all [step, eff]

inductive reach (P : Program F) (ns : List ℕ) (xs : List F) (B : ℕ) :
    ℕ → MachineState F → MachineState F → Prop
  | zero (w : MachineState F) : reach P ns xs B 0 w w
  | succ {n : ℕ} {w w' : MachineState F} (ins : Instruction F) :
      (∀ i, w.natReg i ≤ B) → P[w.pc]? = some ins → ins ≠ .halt →
      reach P ns xs B n (eff ns xs w ins) w' → reach P ns xs B (n+1) w w'

theorem reach_trans {P : Program F} {ns : List ℕ} {xs : List F} {B a b : ℕ}
    {w₁ w₂ w₃ : MachineState F} (h₁ : reach P ns xs B a w₁ w₂)
    (h₂ : reach P ns xs B b w₂ w₃) : reach P ns xs B (a+b) w₁ w₃ := by
  induction h₁ with
  | zero => simpa using h₂
  | @succ n w w' ins hb hq hh _ ih =>
    rw [show n + 1 + b = (n+b)+1 by omega]
    exact reach.succ ins hb hq hh (ih h₂)

theorem runFrom_of_reach {P : Program F} {ns : List ℕ} {xs : List F} {B n : ℕ}
    {w w' : MachineState F} (h : reach P ns xs B n w w') (t : ℕ) :
    runFrom P ns xs B (n+t) w = runFrom P ns xs B t w' := by
  induction h with
  | zero => simp
  | @succ n w w' ins hb hq hh _ ih =>
    rw [show n + 1 + t = (n+t)+1 by omega]
    simp only [runFrom, hb, implies_true, if_true, hq]
    split
    · rename_i heq; cases heq; exact absurd rfl hh
    · rw [step_eq hq hh]; simpa using ih

theorem runFrom_halt {P : Program F} {ns : List ℕ} {xs : List F} {B : ℕ}
    {w : MachineState F} (hb : ∀ i, w.natReg i ≤ B) (hq : P[w.pc]? = some .halt) :
    runFrom P ns xs B 1 w = some w := by simp [runFrom, hb, hq]

def N (natBase j : ℕ) : ℕ := natBase + 2 + j
def A (fieldBase j : ℕ) : ℕ := fieldBase + j

def pad (l : List (Instruction F)) : List (Instruction F) := l ++ List.replicate (4-l.length) .halt

end SubspaceEvasion312.Explicit.Dev.GMC


