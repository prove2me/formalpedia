-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Supplement_StreamingMemory
-- name    : PrivateContinualCounting_Kraft_Supplement_StreamingMemory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:28:54.305603+00:00
-- url     : https://prove2.me/theorems/905e952e-e1f9-43a9-be8d-da082809c1af
-- title:
--   Finite register programs and counted streaming implementations
-- statement:
--   A streaming implementation is a finite register program with finite arrays of real and natural registers, an instruction pointer, a fresh-normal draw pointer and one output slot. Instructions perform arithmetic, copy, branching, allocation, arrival-input reading and independent standard normal sampling. Exact logarithm and square root are scalar primitives for the source's deterministic budget and coefficient initialization. This is an exact real-arithmetic space model, not a finite-precision or running-time assertion. No instruction can inspect an input history or apply an arbitrary measurable encoder.
--
--   The transition semantics are explicit. At tick $t$ the only input available is $x_{t+1}$ and the only fresh randomness is the next unused coordinate of that tick's Gaussian tape. A tick runs to its first emitted output; totality is a separate obligation for all streams and seeds. The state after each tick is recursively computed by these transitions. The product seed defines the probability experiment; it is not stored as an infinite runtime object.
--
--   For a machine $A$, let $W_A(s)$ count all allocated real and natural registers, its stored instruction operands and real constants, initial arrays, input/output, clock, program counter, random-draw position and constant-size arithmetic scratch. The implementation predicate requires totality, measurable joint transcripts, equality of the entire transcript law to the A/B/C mechanism for one inner family, and
--   $$W_A(s_{t,k})\le C_{\rm mem}(\ln(t+1))^2\quad(t+1\ge3)$$
--   for every intermediate state $k$ before that tick emits, every stream and every seed. In particular any retained data, matrices, coefficients, buffers or sampled randomness occupy counted registers. The memory constant is fixed before time. BLT family existence and a program meeting these obligations are part of Theorem 1.4, never assumptions of that theorem.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), pp. 23–24, PDF pp. 25–26, Appendix E.3

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Hypertree

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- A finite real-register program. Natural registers contain addresses and the clock.
All operands are addresses in natural registers. Exact log and sqrt permit the source's
coefficient/budget initialization; no bit precision or running-time claim is made.
There is no primitive accepting a history or an arbitrary measurable function. -/
inductive RAMInstruction where
  | realConst (address : ℕ) (value : ℝ)
  | natConst (address value : ℕ)
  | natAdd (dst lhs rhs : ℕ)
  | natSub (dst lhs rhs : ℕ)
  | natDiv (dst lhs rhs : ℕ)
  | clock (dst : ℕ)
  | copy (dst src : ℕ)
  | add (dst lhs rhs : ℕ)
  | sub (dst lhs rhs : ℕ)
  | mul (dst lhs rhs : ℕ)
  | div (dst lhs rhs : ℕ)
  | sqrt (dst src : ℕ)
  | log (dst src : ℕ)
  | natToReal (dst src : ℕ)
  | input (dst : ℕ)
  | normal (dst : ℕ)
  | resizeReal (sizeRegister : ℕ)
  | resizeNat (sizeRegister : ℕ)
  | jump (pc : ℕ)
  | natBranch (lhs rhs pc : ℕ)
  | realBranch (lhs rhs pc : ℕ)
  | emit (src : ℕ)

structure RAMState where
  reals : List ℝ
  naturals : List ℕ
  pc : ℕ
  draws : ℕ
  output : Option ℝ

structure StreamingRAM where
  code : List RAMInstruction
  initialReals : List ℝ
  initialNaturals : List ℕ

/-- All live values are in these finite arrays. Registers outside the allocation read
as zero and out-of-range writes have no effect, making the operational semantics total. -/
def RAMState.nat (s : RAMState) (i : ℕ) : ℕ := s.naturals[i]?.getD 0
def RAMState.real (s : RAMState) (i : ℕ) : ℝ := s.reals[s.nat i]?.getD 0

def RAMState.writeReal (s : RAMState) (i : ℕ) (v : ℝ) : RAMState :=
  {s with reals := s.reals.set (s.nat i) v}
def RAMState.writeNat (s : RAMState) (i v : ℕ) : RAMState :=
  {s with naturals := s.naturals.set i v}

noncomputable def StreamingRAM.step (A : StreamingRAM) (t : ℕ) (x : ℝ)
    (ω : ℕ × ℕ → ℝ) (s : RAMState) : RAMState :=
  if s.output.isSome then s else
  let next := {s with pc := s.pc+1}
  match A.code[s.pc]? with
  | none => s
  | some (.realConst dst v) => next.writeReal dst v
  | some (.natConst dst v) => next.writeNat dst v
  | some (.natAdd dst p q) => next.writeNat dst (s.nat p + s.nat q)
  | some (.natSub dst p q) => next.writeNat dst (s.nat p - s.nat q)
  | some (.natDiv dst p q) => next.writeNat dst (s.nat p / s.nat q)
  | some (.clock dst) => next.writeNat dst (t+1)
  | some (.copy dst src) => next.writeReal dst (s.real src)
  | some (.add dst p q) => next.writeReal dst (s.real p + s.real q)
  | some (.sub dst p q) => next.writeReal dst (s.real p - s.real q)
  | some (.mul dst p q) => next.writeReal dst (s.real p * s.real q)
  | some (.div dst p q) => next.writeReal dst (s.real p / s.real q)
  | some (.sqrt dst src) => next.writeReal dst (Real.sqrt (s.real src))
  | some (.log dst src) => next.writeReal dst (Real.log (s.real src))
  | some (.natToReal dst src) => next.writeReal dst (s.nat src : ℝ)
  | some (.input dst) => next.writeReal dst x
  | some (.normal dst) => {(next.writeReal dst (ω (t,s.draws))) with draws := s.draws+1}
  | some (.resizeReal i) => {next with reals := ((s.reals.take (s.nat i)).append (List.replicate (s.nat i - s.reals.length) 0))}
  | some (.resizeNat i) => {next with naturals := ((s.naturals.take (s.nat i)).append (List.replicate (s.nat i - s.naturals.length) 0))}
  | some (.jump pc) => {next with pc := pc}
  | some (.natBranch p q pc) => if s.nat p ≤ s.nat q then {next with pc := pc} else next
  | some (.realBranch p q pc) => if s.real p ≤ s.real q then {next with pc := pc} else next
  | some (.emit src) => {next with output := some (s.real src)}

/-- Fresh Gaussian coordinates are read once during each tick, then discarded unless
copied to a counted register. No infinite random seed is retained in the state. -/
def StreamingRAM.start (s : RAMState) : RAMState := {s with output := none, draws := 0}

noncomputable def StreamingRAM.micro (A : StreamingRAM) (t : ℕ) (x : ℝ)
    (ω : ℕ × ℕ → ℝ) (s : RAMState) (k : ℕ) : RAMState :=
  (A.step t x ω)^[k] (StreamingRAM.start s)

noncomputable def StreamingRAM.duration (A : StreamingRAM) (t : ℕ) (x : ℝ)
    (ω : ℕ × ℕ → ℝ) (s : RAMState) : ℕ := by
  classical
  exact if h : ∃ k, (A.micro t x ω s k).output.isSome = true then Nat.find h else 0

noncomputable def StreamingRAM.state (A : StreamingRAM) (x : Stream)
    (ω : ℕ × ℕ → ℝ) : ℕ → RAMState
  | 0 => ⟨A.initialReals, A.initialNaturals, 0, 0, none⟩
  | t+1 => let s := A.state x ω t
           A.micro t (x t) ω s (A.duration t (x t) ω s)

/-- Code and its embedded coefficients, initial arrays, all registers, the program
counter, clock, RNG position, input/output and constant-size arithmetic scratch count.
The fixed factor 8 bounds the operands stored by each instruction. -/
def StreamingRAM.words (A : StreamingRAM) (s : RAMState) : ℕ :=
  8*A.code.length + A.initialReals.length + A.initialNaturals.length +
  s.reals.length + s.naturals.length + 16

def StreamingRAM.Total (A : StreamingRAM) : Prop :=
  ∀ (x : Stream) (ω : ℕ × ℕ → ℝ) (t : ℕ),
    ∃ k, (A.micro t (x t) ω (A.state x ω t) k).output.isSome = true

noncomputable def StreamingRAM.law (A : StreamingRAM) (x : Stream) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  (gaussianSeed (ℕ × ℕ)).map (fun ω k => (A.state x ω (k.val+1)).output.getD 0)

/-- Correctness includes measurability and equality of the entire joint transcript,
not only each marginal. Peak space includes all intermediate states during a tick. -/
def Implements (A : StreamingRAM) (F : InnerFamily) (a ξ : ℝ) (M : ℝ) : Prop :=
  A.Total ∧
  (∀ (x : Stream) (n : ℕ), Measurable
    (fun ω k : Fin n => (A.state x ω (k.val+1)).output.getD 0)) ∧
  (∀ (x : Stream) (n : ℕ), A.law x n = treeLaw F a ξ x n) ∧
  ∀ (x : Stream) (ω : ℕ × ℕ → ℝ) (t : ℕ), 3 ≤ t+1 →
    ∀ k : ℕ, k ≤ A.duration t (x t) ω (A.state x ω t) →
      (A.words (A.micro t (x t) ω (A.state x ω t) k) : ℝ) ≤
        M * (Real.log ((t+1:ℕ):ℝ))^2

end PrivateContinualCounting.Kraft.Supplement


