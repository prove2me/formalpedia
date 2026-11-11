-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Program
-- name    : ConstrainedCorrelationRepulsion_Main_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:51.992208+00:00
-- url     : https://prove2.me/theorems/901b8655-4684-4853-be70-d337a5cb2945
-- title:
--   Finite programs and charged operational execution
-- statement:
--   A program is a finite list of register instructions with rational literals, arithmetic, comparisons, indirect memory, pair access, Bernoulli sampling, jumps and halt. Execution is iteration of the given transition kernel, starting with zero memory. No instruction solves an LP, finds a matching, selects an optimum partition, or returns a distribution supplied by a guarantee.
--
--   In the rational mode, arithmetic and memory accesses charge operand, result and address bit lengths; valid randomized instructions in this bit-cost mode use only a fair coin. Bounded rational sampling must therefore be implemented from fair random bits; an exact biased-coin oracle cannot discharge a bit-cost theorem. Exact-real mode charges arithmetic and Bernoulli operations for arbitrary real weighted inputs. Valid runs exclude zero divisors and probabilities outside $[0,1]$. A bounded run requires a bound on every reachable execution and termination within that bound. These semantics make computational clauses substantive proof obligations.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), §§2.1, 5.1, 6.1, 6.3, Appendix B; printed pp.4, 22–24, 30–35, 43–45 (PDF pp.5, 23–25, 31–36, 44–46)

import Mathlib

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

/-- A finite register program, independent of the input size. The syntax has no optimizer,
LP solver, matching oracle, partition oracle, or arbitrary semantic callback. -/
inductive Instruction where
  | natConst (dst value : ℕ)
  | ratConst (dst : ℕ) (value : ℚ)
  | natAdd (dst a b : ℕ)
  | natSub (dst a b : ℕ)
  | natMul (dst a b : ℕ)
  | natDiv (dst a b : ℕ)
  | natMod (dst a b : ℕ)
  | realAdd (dst a b : ℕ)
  | realSub (dst a b : ℕ)
  | realMul (dst a b : ℕ)
  | realDiv (dst a b : ℕ)
  | cast (dst src : ℕ)
  | ceil (dst src : ℕ)
  | natLoad (dst addr : ℕ)
  | natStore (addr src : ℕ)
  | realLoad (dst addr : ℕ)
  | realStore (addr src : ℕ)
  | query (dst bank u v : ℕ)
  | branchNat (a b yes no : ℕ)
  | branchReal (a b yes no : ℕ)
  | jump (pc : ℕ)
  | bernoulli (dst parameter : ℕ)
  | halt

abbrev Program := List Instruction

structure MachineState where
  pc : ℕ := 0
  natReg : ℕ → ℕ := fun _ => 0
  realReg : ℕ → ℝ := fun _ => 0
  natMem : ℕ → ℕ := fun _ => 0
  realMem : ℕ → ℝ := fun _ => 0
  work : ℕ := 0
  halted : Bool := false

/-- Totalized Bernoulli law. Invalid parameters have a specified fallback; a valid run
separately requires all Bernoulli parameters to lie in [0,1]. -/
noncomputable def flip (p : ℝ) : PMF Bool :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    PMF.bernoulli ⟨p, h.1⟩ (by exact_mod_cast h.2)
  else PMF.pure false

def natBits (a : ℕ) : ℕ := Nat.log2 a + 1

def ratBits (a : ℚ) : ℕ := natBits a.num.natAbs + natBits a.den

/-- Bit cost on rational computations; arbitrary real inputs use exact-real mode instead. -/
noncomputable def realBits (a : ℝ) : ℕ :=
  if h : ∃ q : ℚ, (q : ℝ) = a then ratBits (Classical.choose h) else 1

/-- Dispatch, comparisons, memory, arithmetic, sampling and output are all charged.
The exact-real reading charges one arithmetic operation. The rational reading charges
quadratic operand/result bit lengths, and charges addresses and stored words. -/
noncomputable def instructionCharge (bitModel : Bool) (i : Instruction) (s : MachineState) : ℕ :=
  if !bitModel then 1 else
  match i with
  | .realAdd _ a b => (realBits (s.realReg a) + realBits (s.realReg b) +
      realBits (s.realReg a + s.realReg b)) ^ 2 + 1
  | .realSub _ a b => (realBits (s.realReg a) + realBits (s.realReg b) +
      realBits (s.realReg a - s.realReg b)) ^ 2 + 1
  | .realMul _ a b => (realBits (s.realReg a) + realBits (s.realReg b) +
      realBits (s.realReg a * s.realReg b)) ^ 2 + 1
  | .realDiv _ a b => (realBits (s.realReg a) + realBits (s.realReg b) +
      realBits (s.realReg a / s.realReg b)) ^ 2 + 1
  | .natLoad _ a => natBits (s.natReg a) + natBits (s.natMem (s.natReg a)) + 1
  | .natStore a b => natBits (s.natReg a) + natBits (s.natReg b) + 1
  | .realLoad _ a => natBits (s.natReg a) + realBits (s.realMem (s.natReg a)) + 1
  | .realStore a b => natBits (s.natReg a) + realBits (s.realReg b) + 1
  | .bernoulli _ a => realBits (s.realReg a) ^ 2 + 1
  | .natAdd _ a b | .natSub _ a b | .natMul _ a b | .natDiv _ a b | .natMod _ a b =>
      (natBits (s.natReg a) + natBits (s.natReg b) + 1) ^ 2
  | .branchNat a b _ _ => natBits (s.natReg a) + natBits (s.natReg b) + 1
  | .branchReal a b _ _ => realBits (s.realReg a) + realBits (s.realReg b) + 1
  | .ceil _ a => (realBits (s.realReg a) + natBits ⌈s.realReg a⌉₊ + 1) ^ 2
  | .cast _ a => natBits (s.natReg a) + 1
  | .query _ _ a b => natBits (s.natReg a) + natBits (s.natReg b) + 1
  | .natConst _ v => natBits v + 1
  | .ratConst _ q => ratBits q + 1
  | .jump _ | .halt => 1

noncomputable def machineStep (bitModel : Bool) (code : Program)
    (oracle : ℕ → ℕ → ℕ → ℝ) (s : MachineState) : PMF MachineState :=
  if s.halted then PMF.pure s else
  match code[s.pc]? with
  | none => PMF.pure {s with halted := true, work := s.work + 1}
  | some i =>
    let z := {s with pc := s.pc + 1, work := s.work + instructionCharge bitModel i s}
    match i with
    | .natConst d v => PMF.pure {z with natReg := Function.update s.natReg d v}
    | .ratConst d v => PMF.pure {z with realReg := Function.update s.realReg d v}
    | .natAdd d a b => PMF.pure {z with natReg := Function.update s.natReg d (s.natReg a + s.natReg b)}
    | .natSub d a b => PMF.pure {z with natReg := Function.update s.natReg d (s.natReg a - s.natReg b)}
    | .natMul d a b => PMF.pure {z with natReg := Function.update s.natReg d (s.natReg a * s.natReg b)}
    | .natDiv d a b => PMF.pure {z with natReg := Function.update s.natReg d (s.natReg a / s.natReg b)}
    | .natMod d a b => PMF.pure {z with natReg := Function.update s.natReg d (s.natReg a % s.natReg b)}
    | .realAdd d a b => PMF.pure {z with realReg := Function.update s.realReg d (s.realReg a + s.realReg b)}
    | .realSub d a b => PMF.pure {z with realReg := Function.update s.realReg d (s.realReg a - s.realReg b)}
    | .realMul d a b => PMF.pure {z with realReg := Function.update s.realReg d (s.realReg a * s.realReg b)}
    | .realDiv d a b => PMF.pure {z with realReg := Function.update s.realReg d (s.realReg a / s.realReg b)}
    | .cast d a => PMF.pure {z with realReg := Function.update s.realReg d (s.natReg a)}
    | .ceil d a => PMF.pure {z with natReg := Function.update s.natReg d ⌈s.realReg a⌉₊}
    | .natLoad d a => PMF.pure {z with natReg := Function.update s.natReg d (s.natMem (s.natReg a))}
    | .natStore a b => PMF.pure {z with natMem := Function.update s.natMem (s.natReg a) (s.natReg b)}
    | .realLoad d a => PMF.pure {z with realReg := Function.update s.realReg d (s.realMem (s.natReg a))}
    | .realStore a b => PMF.pure {z with realMem := Function.update s.realMem (s.natReg a) (s.realReg b)}
    | .query d bank a b => PMF.pure {z with realReg := Function.update s.realReg d (oracle bank (s.natReg a) (s.natReg b))}
    | .branchNat a b yes no => PMF.pure {z with pc := if s.natReg a ≤ s.natReg b then yes else no}
    | .branchReal a b yes no => PMF.pure {z with pc := if s.realReg a ≤ s.realReg b then yes else no}
    | .jump pc => PMF.pure {z with pc := pc}
    | .bernoulli d a => (flip (s.realReg a)).map fun b =>
        {z with natReg := Function.update s.natReg d (if b then 1 else 0)}
    | .halt => PMF.pure {z with halted := true}

noncomputable def machineRun (bitModel : Bool) (code : Program)
    (oracle : ℕ → ℕ → ℕ → ℝ) (initial : MachineState) : ℕ → PMF MachineState
  | 0 => PMF.pure initial
  | t + 1 => (machineRun bitModel code oracle initial t).bind (machineStep bitModel code oracle)

/-- Validity rules exclude the interpreter's default values from actual arithmetic/sampling.
Bit-cost execution has only fair random bits. Exact-real execution may sample Bernoulli(p).
Thus a bounded bit-cost run cannot use an exact biased coin as a constant-time oracle. -/
def InstructionValid (bitModel : Bool) (code : Program) (s : MachineState) : Prop :=
  s.halted = true ∨ ∃ i, code[s.pc]? = some i ∧
    match i with
    | .realDiv _ _ b => s.realReg b ≠ 0
    | .natDiv _ _ b | .natMod _ _ b => 0 < s.natReg b
    | .bernoulli _ p => 0 ≤ s.realReg p ∧ s.realReg p ≤ 1 ∧
        (bitModel = true → s.realReg p = (1 : ℝ) / 2)
    | _ => True

def BoundedRun (bitModel : Bool) (code : Program) (oracle : ℕ → ℕ → ℕ → ℝ)
    (initial : MachineState) (B : ℕ) : Prop :=
  (∀ t ≤ B, ∀ s ∈ (machineRun bitModel code oracle initial t).support,
    InstructionValid bitModel code s ∧ s.work ≤ B) ∧
  (∀ s ∈ (machineRun bitModel code oracle initial B).support, s.halted = true)

end ConstrainedCorrelationRepulsion.Main


