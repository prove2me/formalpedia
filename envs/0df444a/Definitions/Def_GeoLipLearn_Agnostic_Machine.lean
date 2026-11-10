-- Prove2me | Definitions.Def_GeoLipLearn_Agnostic_Machine
-- name    : GeoLipLearn_Agnostic_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:09.173199+00:00
-- url     : https://prove2.me/theorems/0d742646-62f1-454d-90e8-54a7904e0de7
-- title:
--   The Gaussian and labelled-example sampling real RAM
-- statement:
--   A program is a finite list of instructions extending the published real-RAM core. It has real registers, integer pointers, real memory, a program counter, sample and normal-stream positions, a work counter, a halt flag and a real output. Admissible programs have rational real literals and contain neither core accept nor core reject. The added instructions cast a pointer to a real, compute square root, exponential, logarithm or standard Gaussian inverse CDF, read the next scalar Gaussian, read the next labelled example, or halt with a register value.
--
--   Each instruction costs one unit, except reading an example costs $d+1$ and writes its $d$ coordinates and label to consecutive addresses. Random inputs are independent streams with law $D^{\mathbb N}\otimes N(0,1)^{\mathbb N}$. Only the sample instruction accesses $D$. Programs marked deterministic contain neither sampling instruction; programs marked NoExamples may draw Gaussians but cannot request examples. Invalid program counters remain stuck and continue costing work; halted states stutter without further cost.
--
--   Input memory starts at address zero; pointer 0 contains $d$, pointer 3 an optional discrete input, and other initial registers are zero. Pointer 1 specifies the length of the output block, and pointer 2 its base address. The block is read as a finite list of reals. This fixes the operational reading of arithmetic costs, with no floor, no real-to-integer conversion and no instruction carrying a function.
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p.25, representation convention and Algorithm 2; p.34, Algorithm 4; pp.48–49, Theorems C.1–C.2; machine model is an explicit reading

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_Cohen2019_Robust_Phi

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

/-- Only the core has literal constants, restricted to rationals by Admissible. -/
inductive Instr where
  | core (i : SmaleNinth.RAMInstr)
  | pointerReal (dst src : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | phiInv (dst src : ℕ)
  | gauss (dst : ℕ)
  | sample (addr : ℕ)
  | halt (src : ℕ)
abbrev Program := List Instr
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject
def Deterministic (P : Program) : Prop :=
  (∀ i ∈ P, ∀ dst, i ≠ .gauss dst ∧ i ≠ .sample dst)
def NoExamples (P : Program) : Prop := ∀ i ∈ P, ∀ dst, i ≠ .sample dst
structure State where
  cfg : SmaleNinth.RAMConfig
  examples : ℕ
  normals : ℕ
  work : ℕ
  halted : Bool
  output : ℝ
abbrev Streams (d : ℕ) := (ℕ → Space d × ℝ) × (ℕ → ℝ)
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept
def State.next (S : State) (regs : ℕ → ℝ) : State :=
  { S with cfg := { S.cfg with pc := S.cfg.pc+1, regs := regs }, work := S.work+1 }
noncomputable def step (P : Program) (d : ℕ) (ω : Streams d) (S : State) : State :=
  if S.halted then S else
  let r := S.cfg.regs
  match P[S.cfg.pc]? with
  | none => { S with work := S.work+1 }
  | some (.core _) =>
      { S with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) S.cfg, work := S.work+1 }
  | some (.pointerReal dst src) => S.next (Function.update r dst (S.cfg.ptrs src : ℝ))
  | some (.sqrt dst src) => S.next (Function.update r dst (Real.sqrt (r src)))
  | some (.exp dst src) => S.next (Function.update r dst (Real.exp (r src)))
  | some (.log dst src) => S.next (Function.update r dst (Real.log (r src)))
  | some (.phiInv dst src) => S.next (Function.update r dst (Cohen2019.Robust.PhiInvReal (r src)))
  | some (.gauss dst) =>
      { S.next (Function.update r dst (ω.2 S.normals)) with normals := S.normals+1 }
  | some (.sample addr) =>
      let b := S.cfg.ptrs addr
      let e := ω.1 S.examples
      let mem := fun j =>
        if h : b ≤ j ∧ j < b+(d : ℤ) then e.1 ⟨(j-b).toNat, by omega⟩
        else if j = b+(d : ℤ) then e.2 else S.cfg.mem j
      { S with
        cfg := { S.cfg with pc := S.cfg.pc+1, mem := mem }
        examples := S.examples+1
        work := S.work+d+1 }
  | some (.halt src) => { S with halted := true, output := r src, work := S.work+1 }
/-- Pointer 0: dimension; pointer 3: an optional discrete parameter. Input reals start at 0. -/
noncomputable def initial (d discrete : ℕ) (input : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun j => if j=0 then (d : ℤ) else if j=3 then (discrete : ℤ) else 0,
    fun j => if 0 ≤ j then input[j.toNat]! else 0⟩, 0, 0, 0, false, 0⟩
noncomputable def run (P : Program) (d : ℕ) (ω : Streams d) (S : State) (t : ℕ) : State :=
  (step P d ω)^[t] S
/-- Output block: pointer 1 is its length, pointer 2 its base. -/
noncomputable def representation (S : State) : List ℝ :=
  (List.range (S.cfg.ptrs 1).toNat).map fun j => S.cfg.mem (S.cfg.ptrs 2 + (j : ℤ))
noncomputable def streamLaw {d : ℕ} (D : Measure (Space d × ℝ)) : Measure (Streams d) :=
  (Measure.infinitePi fun _ : ℕ => D).prod
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
noncomputable def gaussianStreamLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

end GeoLipLearn.Agnostic


