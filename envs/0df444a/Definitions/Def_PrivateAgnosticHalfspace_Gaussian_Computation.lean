-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Computation
-- name    : PrivateAgnosticHalfspace_Gaussian_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:22:54.320416+00:00
-- url     : https://prove2.me/theorems/7cb30b66-9bdb-48c1-95e6-175075a0573e
-- title:
--   Costed real arithmetic programs and operational output laws
-- statement:
--   The learner uses the referenced sampling real RAM: a single finite admissible program with rational literals, integer pointer registers, exact real arithmetic, square root, exponential, logarithm, comparisons, memory operations and independent Gaussian and exponential draws. Uniform draws are derived from exponential draws. Every executed instruction adds to the machine work counter. A separate oracle-cost dialect for Lemma B.4 charges scalar expressions and individual subgradient and projection calls; addresses there must be nonnegative integers, without a real-to-integer computational primitive.
--
--   For a public input array $a$, independent random tape $\omega$, initial zero registers and fuel $F$, execution is a partial deterministic function. Oracle instructions also count individual subgradient and projection calls. The published learner machine has no such oracle instructions: the corresponding computations must be performed with its scalar instructions. The real arithmetic interpretation charges the same types of operations used by the source's feature construction, optimization, validation and sampling account.
--   $$
--   \operatorname{Implements}(\mathcal A,F,B,a,\nu)
--   \quad\Longrightarrow\quad
--   \text{every tape halts with cost at most }B,\qquad
--   \mathcal L(\operatorname{output}(\mathcal A,a,\omega))=\nu.
--   $$
--   The predicate also requires a measurable execution output, a unit-ball coefficient output and a valid integer threshold index on every tape. Output coordinates use an explicitly defined lexicographic multi-index rank, independent of any choice of a finite equivalence. Both learner and optimizer input arrays contain only public parameters and the labeled sample.
--
--   This operational interface lets the goal assert efficiency of a single uniform sample-only program. A probability measure together with an arbitrary assigned cost does not satisfy it. Subgradient and projection oracles serve the separate oracle complexity statement of Lemma B.4.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 5, 21, 27, Algorithm 1, Lemma B.4 and arithmetic-operation cost account; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Model
import Definitions.Def_PolySampIso_Machine

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

/-- Real arithmetic expressions. Addresses are computed, so a single finite program handles
all dimensions and sample sizes. No operation can read a population law or an optimum. -/
inductive Expr where
  | constant : ℝ → Expr
  | load : Expr → Expr
  | input : Expr → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
  | inv : Expr → Expr
  | sqrt : Expr → Expr
  | exp : Expr → Expr
  | log : Expr → Expr

noncomputable def address (x : ℝ) : ℕ := ⌊x⌋₊
noncomputable def Expr.eval (r a : ℕ → ℝ) : Expr → ℝ
  | .constant x => x
  | .load e => r (address (e.eval r a))
  | .input e => a (address (e.eval r a))
  | .add e f => e.eval r a + f.eval r a
  | .mul e f => e.eval r a * f.eval r a
  | .neg e => -(e.eval r a)
  | .inv e => (e.eval r a)⁻¹
  | .sqrt e => Real.sqrt (e.eval r a)
  | .exp e => Real.exp (e.eval r a)
  | .log e => Real.log (e.eval r a)

def Expr.cost : Expr → ℕ
  | .constant _ => 1
  | .load e | .input e | .neg e | .inv e | .sqrt e | .exp e | .log e => e.cost + 1
  | .add e f | .mul e f => e.cost + f.cost + 1

/-- Memory addresses must be nonnegative integers. Real-to-integer rounding is not a
unit-cost computational primitive. -/
def Expr.WellAddressed (r a : ℕ → ℝ) : Expr → Prop
  | .constant _ => True
  | .load e | .input e => e.WellAddressed r a ∧ ∃ n : ℕ, e.eval r a = n
  | .add e f | .mul e f => e.WellAddressed r a ∧ f.WellAddressed r a
  | .neg e | .inv e | .sqrt e | .exp e | .log e => e.WellAddressed r a

/-- Unit-cost independent uniform and normal draws, as in the source's real arithmetic model.
The oracle instructions are used only for the oracle accounting in B.4; the headline
implementation is required to contain neither instruction. -/
inductive Instruction where
  | assign : Expr → Expr → Instruction
  | uniform : Expr → Instruction
  | normal : Expr → Instruction
  | branch : Expr → ℕ → ℕ → Instruction
  | gradient : Expr → Expr → Expr → Instruction
  | project : Expr → Expr → Instruction
  | halt : Instruction

def Expr.IsAddress (r a : ℕ → ℝ) (e : Expr) : Prop :=
  e.WellAddressed r a ∧ ∃ n : ℕ, e.eval r a = n

def Instruction.WellAddressed (r a : ℕ → ℝ) : Instruction → Prop
  | .assign dst e => dst.IsAddress r a ∧ e.WellAddressed r a
  | .uniform dst | .normal dst => dst.IsAddress r a
  | .branch e _ _ => e.WellAddressed r a
  | .gradient idx src dst => idx.IsAddress r a ∧ src.IsAddress r a ∧ dst.IsAddress r a
  | .project src dst => src.IsAddress r a ∧ dst.IsAddress r a
  | .halt => True

abbrev Program := List Instruction
abbrev Tape := ℕ → ℝ × ℝ
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ =>
    ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)).prod (gaussianReal 0 1))

structure MachineState where
  pc : ℕ := 0
  registers : ℕ → ℝ := fun _ => 0
  cursor : ℕ := 0
  operations : ℕ := 0
  gradients : ℕ := 0
  projections : ℕ := 0

structure Oracle (D : ℕ) where
  gradient : ℕ → Vec D → Vec D
  project : Vec D → Vec D

noncomputable def readVector (D : ℕ) (r : ℕ → ℝ) (base : ℕ) : Vec D :=
  WithLp.toLp 2 (fun i => r (base + i.val))
noncomputable def writeVector {D : ℕ} (r : ℕ → ℝ) (base : ℕ) (v : Vec D) : ℕ → ℝ :=
  fun i => if h : base ≤ i ∧ i - base < D then v ⟨i - base, h.2⟩ else r i

/-- One operational step, with every arithmetic expression and oracle call charged. -/
noncomputable def step {D : ℕ} (o : Oracle D) (a : ℕ → ℝ) (ω : Tape)
    (s : MachineState) : Instruction → MachineState
  | .assign dst e =>
      { s with
        pc := s.pc + 1
        registers := Function.update s.registers (address (dst.eval s.registers a)) (e.eval s.registers a)
        operations := s.operations + dst.cost + e.cost + 1}
  | .uniform dst =>
      { s with
        pc := s.pc + 1
        cursor := s.cursor + 1
        registers := Function.update s.registers (address (dst.eval s.registers a)) ((ω s.cursor).1)
        operations := s.operations + dst.cost + 1}
  | .normal dst =>
      { s with
        pc := s.pc + 1
        cursor := s.cursor + 1
        registers := Function.update s.registers (address (dst.eval s.registers a)) ((ω s.cursor).2)
        operations := s.operations + dst.cost + 1}
  | .branch e yes no =>
      { s with
        pc := if 0 ≤ e.eval s.registers a then yes else no
        operations := s.operations + e.cost + 1}
  | .gradient idx src dst =>
      { s with
        pc := s.pc + 1
        gradients := s.gradients + 1
        registers := writeVector s.registers (address (dst.eval s.registers a))
          (o.gradient (address (idx.eval s.registers a))
            (readVector D s.registers (address (src.eval s.registers a))))
        operations := s.operations + idx.cost + src.cost + dst.cost + 2 * D + 1}
  | .project src dst =>
      { s with
        pc := s.pc + 1
        projections := s.projections + 1
        registers := writeVector s.registers (address (dst.eval s.registers a))
          (o.project (readVector D s.registers (address (src.eval s.registers a))))
        operations := s.operations + src.cost + dst.cost + 2 * D + 1}
  | .halt => s

/-- A fuel bound is a termination certificate, not an assigned cost. Cost comes from `step`. -/
noncomputable def execute {D : ℕ} (code : Program) (o : Oracle D) (a : ℕ → ℝ) (ω : Tape) :
    ℕ → MachineState → Option MachineState
  | 0, _ => none
  | fuel + 1, s => by
      classical
      exact match code[s.pc]? with
      | none => none
      | some .halt => some s
      | some i => if i.WellAddressed s.registers a then
          execute code o a ω fuel (step o a ω s i) else none

def oracleFree (code : Program) : Prop :=
  ∀ i ∈ code, (∀ x y z, i ≠ Instruction.gradient x y z) ∧
    (∀ x y, i ≠ Instruction.project x y)
noncomputable def noOracle : Oracle 0 := ⟨fun _ _ => 0, fun _ => 0⟩

/-- Fixed public input layout followed by the ordered labeled sample. The first eleven cells
are d,p,k,M,n0,m,epsilon,delta,alpha,beta,n; the sample starts at cell 11. -/
noncomputable def learnerInput (d p k M n₀ m : ℕ) (ε δ α β : ℝ)
    (S : Fin (k * n₀ + m) → Example d) (i : ℕ) : ℝ :=
  if hi : i < 11 then
    (![ (d : ℝ), p, k, M, n₀, m, ε, δ, α, β, k * n₀ + m ] : Fin 11 → ℝ) ⟨i, hi⟩
  else
    let row := (i - 11) / (d + 1)
    let col := (i - 11) % (d + 1)
    if h : row < k * n₀ + m then
      if hc : col < d then (S ⟨row, h⟩).1 ⟨col, hc⟩ else label (S ⟨row, h⟩).2
    else 0

/-- Explicit lexicographic enumeration by a base-(p+1) code. No choice of a finite equivalence. -/
def indexCode {d p : ℕ} (κ : Index d p) : ℕ :=
  ∑ i, (κ.val i).val * (p + 1) ^ i.val
def indexRank {d p : ℕ} (κ : Index d p) : ℕ :=
  (Finset.univ.filter (fun ξ : Index d p => indexCode ξ < indexCode κ)).card

/-- Output coefficients occupy registers indexed by the public lexicographic enumeration;
the threshold index follows them. -/
noncomputable def readCoefficients (d p : ℕ) (r : ℕ → ℝ) : Coeff d p :=
  WithLp.toLp 2 (fun i => r (indexRank i))
noncomputable def rawOutput (d p : ℕ) (r : ℕ → ℝ) : Coeff d p × ℕ :=
  (readCoefficients d p r, address (r (Fintype.card (Index d p))))

/-- The published generic real-RAM program, with no optimization oracle. -/
abbrev LearnerProgram := PolySampIso.Program

/-- Public integer dimensions and the input table are the only initial data. Negative
memory cells are reserved for outputs. There is no population-dependent initialization. -/
noncomputable def initialState (d p M : ℕ) (input : ℕ → ℝ) : PolySampIso.State :=
  ⟨⟨0, fun _ => 0,
      fun q => if q = 0 then (d : ℤ) else if q = 1 then (p : ℤ) else if q = 2 then (M : ℤ) else 0,
      fun z => if 0 ≤ z then input z.toNat else 0⟩, 0, 0, false, 0⟩
noncomputable def outputMemory (s : PolySampIso.State) (i : ℕ) : ℝ :=
  s.core.mem (-1 - (i : ℤ))

/-- Operational realization on the published sampling real RAM: one admissible finite
program, actual charged work, successful termination and well-formed output on every tape,
and equality of measurable output laws. No correctness or efficiency is assumed in a type. -/
noncomputable def Implements (code : LearnerProgram) (fuel cost : ℕ)
    (d p M : ℕ) (input : ℕ → ℝ) (ν : Measure (Output d p M)) : Prop :=
  PolySampIso.Admissible code ∧
  (∀ ω, let s := PolySampIso.run code (initialState d p M input) ω fuel
    s.halted = true ∧ s.work ≤ cost ∧ ‖(rawOutput d p (outputMemory s)).1‖ ≤ 1 ∧
    (rawOutput d p (outputMemory s)).2 < M ∧
    outputMemory s (Fintype.card (Index d p)) = ((rawOutput d p (outputMemory s)).2 : ℝ)) ∧
  let out := fun ω => rawOutput d p
    (outputMemory (PolySampIso.run code (initialState d p M input) ω fuel))
  Measurable out ∧ PolySampIso.tape.map out = ν.map (fun v => (v.1.val, v.2.val))

end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian

/-- The training subroutine's public input layout is the learner layout with a single block. -/
noncomputable def optimizerInput (d p n : ℕ) (ε δ : ℝ)
    (S : Fin n → Example d) (i : ℕ) : ℝ :=
  if hi : i < 11 then
    (![ (d : ℝ), p, 1, 1, n, 0, ε, δ, 0, 0, n ] : Fin 11 → ℝ) ⟨i, hi⟩
  else
    let row := (i - 11) / (d + 1)
    let col := (i - 11) % (d + 1)
    if h : row < n then
      if hc : col < d then (S ⟨row, h⟩).1 ⟨col, hc⟩ else label (S ⟨row, h⟩).2
    else 0

end PrivateAgnosticHalfspace.Gaussian


