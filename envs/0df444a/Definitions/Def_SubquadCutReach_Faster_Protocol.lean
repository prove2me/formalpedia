-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Protocol
-- name    : SubquadCutReach_Faster_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:57:19.953745+00:00
-- url     : https://prove2.me/theorems/b73c396e-cd2a-4765-9f14-ac0da7fe5766
-- title:
--   Finite charged cut-oracle programs and stopping cost
-- statement:
--   A program is a finite list extending the published real RAM with fair coins, a cut query and halt. All real literals are rational. Three finite macros implement neighbour search, edge tests and imbalance evaluation by actual cut queries; their counters include every constituent query. A restricted program contains no direct cut opcode. Input data and output tables have disjoint finite memory blocks; the hidden graph never enters the input.
--
--   $$Q(\omega)=\inf_{t\ge0}\begin{cases}q_t(\omega)&\text{if halted by }t,\\+\infty&\text{otherwise.}\end{cases}$$
--
--   Zero error requires correctness on every returning tape and almost-sure termination. Expected cost is the nonnegative extended integral. Soft bounds quantify positive constants and fixed logarithmic powers outside all instances, and arbitrary fixed polynomial tails for the same program. This separates query cost from correctness probability.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), §2, pp.3–5 (PDF pp.5–7); Theorem 1.2 p.2 (PDF p.4); §B.2 p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SubquadCutReach_Faster_Graphs

set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory

namespace SubquadCutReach.Faster

/-- A finite oracle program extends the published real RAM. No opcode carries a function.
`cut d b` reads the n membership cells starting at pointer b. Output is the memory
at halt. Rational literals prevent graph-dependent advice in constants. -/
inductive Instr where
  | core (i : SmaleNinth.RAMInstr)
  | coin (dst : ℕ)
  | cut (dst bank : ℕ)
  | neighbour (dst vertex bank : ℕ)
  | edge (dst u v : ℕ)
  | balance (dst vertex rule : ℕ)
  | halt
abbrev Program := List Instr

def Admissible (P : Program) : Prop := ∀ i ∈ P, match i with
  | .core (.const _ x) => ∃ q : ℚ, x = q
  | .core .accept | .core .reject => False
  | _ => True

def Restricted (P : Program) : Prop := ∀ d b, Instr.cut d b ∉ P

def Deterministic (P : Program) : Prop := ∀ d, Instr.coin d ∉ P

structure State where
  core : SmaleNinth.RAMConfig
  cursor : ℕ
  queries : ℕ
  halted : Bool

abbrev Memory := ℤ → ℝ

def init (input : Memory) : State := ⟨⟨0, fun _ => 0, fun _ => 0, input⟩, 0, 0, false⟩

def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with | .core i => i | _ => .const 0 0

noncomputable def readSet (n : ℕ) (m : Memory) (base : ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => m (base + (v.val : ℤ)) ≠ 0

/-- Three genuine cut queries implementing the singleton count (1). -/
def neighbourCount {n : ℕ} (O : Finset (Fin n) → ℕ) (v : Fin n)
    (X : Finset (Fin n)) : ℕ := (O {v} + O X - O (insert v X)) / 2

/-- Binary search, with a finite fuel of n+1 and exact charged query count.
On a legitimate cut oracle, fuel cannot run out before a singleton is reached. -/
def neighbourSearch {n : ℕ} (O : Finset (Fin n) → ℕ) (v : Fin n) :
    ℕ → List (Fin n) → Option (Fin n) × ℕ
  | 0, _ => (none, 0)
  | k+1, xs =>
    if neighbourCount O v xs.toFinset = 0 then (none, 3) else
    match xs with
    | [] => (none, 3)
    | [w] => (some w, 3)
    | _ =>
      let a := xs.take ((xs.length + 1)/2)
      let b := xs.drop ((xs.length + 1)/2)
      let result := neighbourSearch O v k (if neighbourCount O v a.toFinset = 0 then b else a)
      (result.1, result.2 + 6)

noncomputable def memDirects (n : ℕ) (m : Memory) (base : ℤ) (u v : Fin n) : Bool :=
  if u < v then decide (m (base + (u.val*n+v.val : ℕ)) ≠ 0)
  else if v < u then decide (m (base + (v.val*n+u.val : ℕ)) = 0) else false

noncomputable def step {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ)
    (ω : ℕ → Bool) (s : State) : State := by
  classical
  exact if s.halted then s else
  let t := { s with core := { s.core with pc := s.core.pc + 1 } }
  match P[s.core.pc]? with
  | none => s
  | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
  | some (.coin d) => { t with       cursor := s.cursor + 1, core := { t.core with regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
  | some (.cut d bank) => { t with       queries := s.queries + 1, core := { t.core with regs := Function.update s.core.regs d         (O (readSet n s.core.mem (s.core.ptrs bank)) : ℝ) } }
  | some (.neighbour d vi bank) =>
    if hv : 0 ≤ s.core.ptrs vi ∧ (s.core.ptrs vi).toNat < n then
      let v : Fin n := ⟨(s.core.ptrs vi).toNat,hv.2⟩
      let xs := ((readSet n s.core.mem (s.core.ptrs bank)).erase v).toList
      let r := neighbourSearch O v (n+1) xs
      { t with queries := s.queries + r.2, core := { t.core with         regs := Function.update s.core.regs d (match r.1 with | none => 0 | some w => w.val+1) } }
    else t
  | some (.edge d ui vi) =>
    if hu : 0 ≤ s.core.ptrs ui ∧ (s.core.ptrs ui).toNat < n then
    if hv : 0 ≤ s.core.ptrs vi ∧ (s.core.ptrs vi).toNat < n then
      let u : Fin n := ⟨(s.core.ptrs ui).toNat,hu.2⟩
      let v : Fin n := ⟨(s.core.ptrs vi).toNat,hv.2⟩
      if u = v then t else
      { t with queries := s.queries + 3, core := { t.core with         regs := Function.update s.core.regs d (neighbourCount O u {v} : ℝ) } }
    else t else t
  | some (.balance d vi bank) =>
    if hv : 0 ≤ s.core.ptrs vi ∧ (s.core.ptrs vi).toNat < n then
      let v : Fin n := ⟨(s.core.ptrs vi).toNat,hv.2⟩
      let A := Finset.univ.filter fun w => memDirects n s.core.mem (s.core.ptrs bank) v w = true
      let B := Finset.univ.filter fun w => memDirects n s.core.mem (s.core.ptrs bank) w v = true
      { t with queries := s.queries + 6, core := { t.core with         regs := Function.update s.core.regs d ((neighbourCount O v A : ℝ) - neighbourCount O v B) } }
    else t
  | some .halt => { t with halted := true }

noncomputable def run {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ)
    (input : Memory) (ω : ℕ → Bool) (t : ℕ) : State :=
  (step P O ω)^[t] (init input)

noncomputable def coins : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- Nontermination has cost infinity, even if a run enters an infinite local loop.
The infimum in ENNReal is infinity if no finite time has halted. -/
noncomputable def cost {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ)
    (input : Memory) (ω : ℕ → Bool) : ℝ≥0∞ :=
  ⨅ t : ℕ, if (run P O input ω t).halted then (run P O input ω t).queries else ⊤

/-- Correctness on every returning tape and almost sure termination, separately. -/
def ZeroError {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ)
    (input : Memory) (answer : Memory → Prop) : Prop :=
  (∀ ω t, (run P O input ω t).halted = true → answer (run P O input ω t).core.mem) ∧
  ∀ᵐ ω ∂coins, ∃ t, (run P O input ω t).halted = true

noncomputable def expected {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ)
    (input : Memory) : ℝ≥0∞ := ∫⁻ ω, cost P O input ω ∂coins

/-- Uniform coefficients are bound by theorems outside all instances; c is a cost-tail
parameter and does not change P. A bound here never asserts a correctness probability. -/
def Tail {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ) (input : Memory)
    (bound c : ℝ) : Prop :=
  coins {ω | ENNReal.ofReal bound < cost P O input ω} ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))

/-- Read an output table; invalid/redundant ordered cells do not affect a rule. -/
noncomputable def outputRule (n : ℕ) (m : Memory) : Rule n :=
  fun u v => decide (m (u.val * n + v.val : ℕ) ≠ 0)

noncomputable def outputFrac (n : ℕ) (m : Memory) : Fractional n :=
  fun u v => m (u.val * n + v.val : ℕ)

/-- All task inputs use negative addresses. Output occupies nonnegative addresses.
The graph is never included. Cells -1,-2,-3 hold n and two task parameters;
known data are at -4-i in a caller-specified finite block, zero elsewhere. -/
def input (n a b : ℕ) (data : ℕ → ℝ) : Memory := fun j =>
  if j = -1 then n else if j = -2 then a else if j = -3 then b
  else if j ≤ -4 then data (-j - 4).toNat else 0

noncomputable def targetInput {n : ℕ} (b : Fin n → ℤ) (T : ℕ) : Memory :=
  input n T 0 fun i => if h : i < n then b ⟨i,h⟩ else 0

noncomputable def repairInput {n : ℕ} (b : Fin n → ℤ) (D : Rule n) : Memory :=
  input n 0 0 fun i => if h : i < n then b ⟨i,h⟩ else
    if _h : i - n < n*n then
      let j := i-n
      if hu : j/n < n then if hv : j%n < n then
        if D ⟨j/n,hu⟩ ⟨j%n,hv⟩ then 1 else 0 else 0 else 0
    else 0

noncomputable def fracInput {n : ℕ} (z : Fractional n) : Memory :=
  input n 0 0 fun i => if hu : i/n < n then if hv : i%n < n then
    z ⟨i/n,hu⟩ ⟨i%n,hv⟩ else 0 else 0

/-- The class of query costs used repeatedly below. Uniformity is across all inputs
in an explicitly supplied class of instances, not across graphs hidden in constants. -/
def SoftBounds (I : Type) (size : I → ℕ) (queries : I → (ℕ → Bool) → ℝ≥0∞)
    (base : I → ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ i,
    (∫⁻ ω, queries i ω ∂coins) ≤ ENNReal.ofReal (C * base i * L (size i)^p)) ∧
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∃ p N : ℕ, ∀ i, N ≤ size i →
    coins {ω | ENNReal.ofReal (C * base i * L (size i)^p) < queries i ω} ≤
      ENNReal.ofReal ((size i : ℝ)^(-c))

end SubquadCutReach.Faster


