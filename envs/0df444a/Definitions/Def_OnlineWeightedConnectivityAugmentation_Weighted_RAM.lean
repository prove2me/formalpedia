-- Prove2me | Definitions.Def_OnlineWeightedConnectivityAugmentation_Weighted_RAM
-- name    : OnlineWeightedConnectivityAugmentation_Weighted_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:04.026324+00:00
-- url     : https://prove2.me/theorems/4cce1d4a-c5f0-426c-9075-ab5f97013ec4
-- title:
--   Charged online exact-real programs and rational simulation
-- statement:
--   A uniform program consists of two finite instruction lists: preprocessing and response. It has natural and real registers, indirect memory, rational literals, arithmetic, comparisons, jumps, indexed input reads and individual purchase emissions. An optional fair-bit instruction supports the randomized reduction. There is no optimization, graph, floor, logarithm or exponent-extraction instruction. Division by zero and invalid input/code accesses cause failure.
--
--   Registers start at zero. The response entry receives only the current request's two endpoint indices and persistent memory. There is no horizon or end-of-input instruction. Emitted link indices accumulate irreversibly. Each primitive operation costs one; delivering a request charges its two writes. For rational inputs, a separate conservative charge is the fourth power of the operand/result/address bit-length sum, including normalized numerator and denominator lengths. This charge is a trace measurement and is unavailable to the program.
--
--   Polynomial execution means a positive integer constant and a natural-number exponent bound these actual counters on all admissible input/prefix pairs. Termination and performance are conclusions, never fields of a program. The exact-real and rational numerical conventions make explicit the source's unspecified arithmetic model.
-- source:
--   Mohit Garg, Felix Hommelsheim, Alexander Lindermayr, Optimal Online Weighted Connectivity Augmentation, STOC 2027 submission #337 (October 2026), published citation basis, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/337.pdf, §2 and §3.5, printed pp. 7, 20 (PDF pp. 8, 21); computational-model reading fixed in BRIEF.md

import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace OnlineWeightedConnectivityAugmentation.Weighted

/-- Exact-real RAM instructions. All constants are rational; no optimization, logarithm,
floor of a real number, exponent extraction, set scan, or graph oracle is an instruction.
Indirect memory access uses natural registers. A coin instruction reads the next tape bit. -/
inductive Instr where
  | halt
  | nconst (dst value : ℕ)
  | rconst (dst : ℕ) (value : ℚ)
  | nadd (dst a b : ℕ) | nsub (dst a b : ℕ) | nmul (dst a b : ℕ)
  | ndiv (dst a b : ℕ)
  | radd (dst a b : ℕ) | rsub (dst a b : ℕ) | rmul (dst a b : ℕ)
  | rdiv (dst a b : ℕ)
  | loadN (dst addr : ℕ) | loadR (dst addr : ℕ)
  | storeN (addr src : ℕ) | storeR (addr src : ℕ)
  | inputN (dst addr : ℕ) | inputR (dst addr : ℕ)
  | jump (target : ℕ)
  | nlt (a b yes no : ℕ) | rlt (a b yes no : ℕ)
  | emit (src : ℕ)
  | coin (dst : ℕ)
  deriving DecidableEq

/-- Two fixed finite pieces of code, sharing persistent memory. The second is invoked on
one request at a time. Neither entry point has an EOF or horizon input. -/
structure Program where
  init : List Instr
  respond : List Instr

def Deterministic (P : Program) : Prop :=
  (∀ d, Instr.coin d ∉ P.init) ∧ ∀ d, Instr.coin d ∉ P.respond

structure MachineInput where
  naturals : List ℕ
  reals : List ℝ

def natBits (v : ℕ) : ℕ := Nat.log2 (v + 1) + 1

def ratBits (v : ℚ) : ℕ := natBits v.num.natAbs + natBits v.den + 1

/-- This measures rational representations; the machine cannot call it. Nonrational
operands have size zero here and use the exact-arithmetic cost, not the rational claim. -/
def realBits (v : ℝ) : ℕ :=
  if h : ∃ q : ℚ, (q : ℝ) = v then ratBits (Classical.choose h) else 0

def MachineInput.arithmeticSize (x : MachineInput) : ℕ :=
  1 + x.naturals.length + x.reals.length + (x.naturals.map natBits).sum

def MachineInput.binarySize (x : MachineInput) : ℕ :=
  x.arithmeticSize + (x.reals.map realBits).sum

def MachineInput.Rational (x : MachineInput) : Prop :=
  ∀ a ∈ x.reals, ∃ q : ℚ, (q : ℝ) = a

structure MachineState where
  pc : ℕ := 0
  nmem : ℕ → ℕ := fun _ => 0
  rmem : ℕ → ℝ := fun _ => 0
  purchases : List ℕ := []
  coins : ℕ := 0
  work : ℕ := 0
  bitWork : ℕ := 0
  halted : Bool := false
  failed : Bool := false

def fault (s : MachineState) : MachineState := {s with failed := true, halted := true}

def addresses (i : Instr) (s : MachineState) : Finset ℕ :=
  match i with
  | .halt => ∅
  | .nconst d _ | .rconst d _ | .emit d | .coin d => {d}
  | .nadd d a b | .nsub d a b | .nmul d a b | .ndiv d a b
  | .radd d a b | .rsub d a b | .rmul d a b | .rdiv d a b => {d,a,b}
  | .loadN d a | .loadR d a | .storeN a d | .storeR a d => {d,a,s.nmem a}
  | .inputN d a | .inputR d a => {d,a}
  | .jump _ => ∅
  | .nlt a b _ _ | .rlt a b _ _ => {a,b}

def footprint (i : Instr) (s : MachineState) : ℕ :=
  natBits s.pc + ∑ a ∈ addresses i s,
    (natBits a + natBits (s.nmem a) + realBits (s.rmem a))

def instruction (x : MachineInput) (ω : ℕ → Bool) (i : Instr)
    (s : MachineState) : MachineState :=
  let t := {s with pc := s.pc + 1}
  match i with
  | .halt => {t with halted := true}
  | .nconst d v => {t with nmem := Function.update s.nmem d v}
  | .rconst d v => {t with rmem := Function.update s.rmem d (v : ℝ)}
  | .nadd d a b => {t with nmem := Function.update s.nmem d (s.nmem a + s.nmem b)}
  | .nsub d a b => {t with nmem := Function.update s.nmem d (s.nmem a - s.nmem b)}
  | .nmul d a b => {t with nmem := Function.update s.nmem d (s.nmem a * s.nmem b)}
  | .ndiv d a b => if s.nmem b = 0 then fault t else
      {t with nmem := Function.update s.nmem d (s.nmem a / s.nmem b)}
  | .radd d a b => {t with rmem := Function.update s.rmem d (s.rmem a + s.rmem b)}
  | .rsub d a b => {t with rmem := Function.update s.rmem d (s.rmem a - s.rmem b)}
  | .rmul d a b => {t with rmem := Function.update s.rmem d (s.rmem a * s.rmem b)}
  | .rdiv d a b => if s.rmem b = 0 then fault t else
      {t with rmem := Function.update s.rmem d (s.rmem a / s.rmem b)}
  | .loadN d a => {t with nmem := Function.update s.nmem d (s.nmem (s.nmem a))}
  | .loadR d a => {t with rmem := Function.update s.rmem d (s.rmem (s.nmem a))}
  | .storeN a d => {t with nmem := Function.update s.nmem (s.nmem a) (s.nmem d)}
  | .storeR a d => {t with rmem := Function.update s.rmem (s.nmem a) (s.rmem d)}
  | .inputN d a => match x.naturals[s.nmem a]? with
      | none => fault t
      | some v => {t with nmem := Function.update s.nmem d v}
  | .inputR d a => match x.reals[s.nmem a]? with
      | none => fault t
      | some v => {t with rmem := Function.update s.rmem d v}
  | .jump a => {t with pc := a}
  | .nlt a b yes no => {t with pc := if s.nmem a < s.nmem b then yes else no}
  | .rlt a b yes no => {t with pc := if s.rmem a < s.rmem b then yes else no}
  | .emit a => {t with purchases := s.nmem a :: s.purchases}
  | .coin d => {t with
      nmem := Function.update s.nmem d (if ω s.coins then 1 else 0)
      coins := s.coins + 1}

/-- Every primitive operation, memory access, comparison, and purchase emission costs one.
For rational inputs a conservative polynomial simulation charge includes operand/result
bit lengths, addresses and instruction position. Neither charge is a free supplied counter. -/
def machineStep (code : List Instr) (x : MachineInput) (ω : ℕ → Bool)
    (s : MachineState) : MachineState :=
  if s.halted then s else
  match code[s.pc]? with
  | none => { (fault s) with work := s.work + 1, bitWork := s.bitWork + 1}
  | some i =>
      let t := instruction x ω i s
      {t with
        work := s.work + 1
        bitWork := s.bitWork + (1 + footprint i s + footprint i t)^4}

def Executes (code : List Instr) (x : MachineInput) (ω : ℕ → Bool)
    (s t : MachineState) : Prop :=
  ∃ fuel : ℕ, (machineStep code x ω)^[fuel] s = t ∧
    t.halted = true ∧ t.failed = false

def feed (s : MachineState) (q : ℕ × ℕ) : MachineState :=
  {s with
    pc := 0
    halted := false
    nmem := Function.update (Function.update s.nmem 0 q.1) 1 q.2
    work := s.work + 2
    bitWork := s.bitWork + (1 + natBits q.1 + natBits q.2)^4}

/-- Requests are supplied only after the previous response has halted. The initial state
is fixed, all memory starts at zero, and purchased indices persist through every response. -/
inductive Transcript (P : Program) (x : MachineInput) (ω : ℕ → Bool) :
    List (ℕ × ℕ) → MachineState → Prop where
  | init {s} : Executes P.init x ω {} s → Transcript P x ω [] s
  | next {qs s t q} : Transcript P x ω qs s →
      Executes P.respond x ω (feed s q) t → Transcript P x ω (qs ++ [q]) t

def Stops (P : Program) (x : MachineInput) (qs : List (ℕ × ℕ)) (ω : ℕ → Bool) : Prop :=
  ∃ s, Transcript P x ω qs s

def finalState (P : Program) (x : MachineInput) (qs : List (ℕ × ℕ))
    (ω : ℕ → Bool) : MachineState :=
  if h : Stops P x qs ω then Classical.choose h else {failed := true}

def selected (m : ℕ) (s : MachineState) : Finset (Fin m) :=
  Finset.univ.filter (fun a => a.val ∈ s.purchases)

def ValidOutput (m : ℕ) (s : MachineState) : Prop := ∀ a ∈ s.purchases, a < m

def PolyOn (P : Program) (domain : MachineInput → List (ℕ × ℕ) → Prop) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ x qs, domain x qs → ∀ ω,
    ∃ s, Transcript P x ω qs s ∧
      s.work ≤ C * (x.arithmeticSize + qs.length + 1)^d ∧
      (x.Rational → s.bitWork ≤ C *
        (x.binarySize + qs.length + (qs.map (fun q => natBits q.1 + natBits q.2)).sum + 1)^d)

end OnlineWeightedConnectivityAugmentation.Weighted


