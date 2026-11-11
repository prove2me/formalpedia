-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Machine
-- name    : KramersHubbard_PartitionFunction_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:08.125253+00:00
-- url     : https://prove2.me/theorems/2b17f581-cb19-4863-b5dd-d1d4456686e9
-- title:
--   Uniform scalar arithmetic programs and charged execution
-- statement:
--   The theorem's algorithm is read as one finite randomized arithmetic program, using the published real-RAM pointer core. It has real registers, integer pointers, scalar indirect loads/stores, exact field arithmetic, comparisons, rational code literals, pointer-to-real conversion, scalar exponential and square-root instructions, independent uniform $[0,1]$ draws, and halt. Each executed instruction costs one unit; array and matrix operations require individual scalar accesses. Invalid counters remain stuck and charged. Halted states stutter at zero cost.
--
--   $$T=\left\lceil C(1+N+r+\beta+\Lambda+\varepsilon^{-1})^d\right\rceil.$$
--
--   The input memory contains only $N,r,\beta,\varepsilon,h,T,v_i,U_i$, where $T$ in the input list denotes the matrix of the antiunitary; it is distinct from the runtime bound. Matrices are row-major pairs of reals. The program must compute partners, Green matrices, transitions, estimates and bounded restarts using its instructions. No instruction computes a matrix exponential, determinant, target partition function or target-distribution sample. The output is register zero after charged execution. Success is a measurable event under the product of uniform-draw measures. This is an explicit reading of the paper's unspecified arbitrary-real input model, rather than a bit-complexity claim.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Theorem 2, p.4; computation in Section 4.4, pp.17-18; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_KramersHubbard_PartitionFunction_Model

noncomputable section
open MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Scalar arithmetic/exponential RAM, extending the published pointer core.
    No instruction accepts a mathematical function, matrix operation, or sampler. -/
inductive Instruction where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | uniform (dst : ℕ)
  | halt
abbrev Program := List Instruction

/-- Rational constants restrict code, never the real/complex inputs. -/
def AdmissibleProgram (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ c) => ∃ q : ℚ, c = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with | .core i => i | _ => .const 0 0

structure MachineState where
  core : SmaleNinth.RAMConfig
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- Every executed scalar instruction costs 1; no whole-array operations exist.
    Invalid counters remain stuck and charged. Halted states stutter at zero cost. -/
def machineStep (P : Program) (omega : ℕ → ℝ) (s : MachineState) : MachineState :=
  if s.halted then s else
    let t : MachineState := { s with work := s.work+1, core := {s.core with pc := s.core.pc+1} }
    let setReg (d : ℕ) (x : ℝ) : MachineState :=
      { t with core := {t.core with regs := Function.update s.core.regs d x} }
    match P[s.core.pc]? with
    | none => {s with work := s.work+1}
    | some (.core _) => {t with core := SmaleNinth.RAMStep (coreProgram P) s.core}
    | some (.pointerReal d q) => setReg d (s.core.ptrs q : ℝ)
    | some (.sqrt d a) => setReg d (Real.sqrt (s.core.regs a))
    | some (.exp d a) => setReg d (Real.exp (s.core.regs a))
    | some (.uniform d) => {setReg d (omega s.cursor) with cursor := s.cursor+1}
    | some .halt => {t with halted := true}

def machineRun (P : Program) (s : MachineState) (omega : ℕ → ℝ) (t : ℕ) : MachineState :=
  (machineStep P omega)^[t] s

/-- Independent uniform draws in [0,1]. -/
def uniformTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))

def complexCells (z : ℂ) : List ℝ := [z.re, z.im]

/-- Explicit finite input: N,r,beta,epsilon, then h and theta row-major, each v_i, then U_i.
    Partners must be computed by charged scalar instructions. No Fock-space matrix, Z, Lambda, G or sample oracle. -/
def inputCells {N r} (D : Data N r) (β eps : ℝ) : List ℝ :=
  [(N : ℝ), (r : ℝ), β, eps] ++
  ((List.finRange (2*N)).flatMap fun j =>
    (List.finRange (2*N)).flatMap fun k => complexCells (D.h j k)) ++
  ((List.finRange (2*N)).flatMap fun j =>
    (List.finRange (2*N)).flatMap fun k => complexCells (D.theta j k)) ++
  ((List.finRange r).flatMap fun i =>
    ((List.finRange (2*N)).flatMap fun j => complexCells (D.v i j))) ++
  (List.finRange r).map D.U

def initialState {N r} (D : Data N r) (β eps : ℝ) : MachineState :=
  ⟨⟨0, fun _ => 0, (fun q => if q = 0 then (N : ℤ) else if q = 1 then (r : ℤ) else 0),
    fun a => if 0 ≤ a then (inputCells D β eps).getD a.toNat 0 else 0⟩, 0, false, 0⟩

/-- One uniform polynomial majorant in the five source parameters. -/
def timeBound {N r} (D : Data N r) (β eps C : ℝ) (d : ℕ) : ℕ :=
  Nat.ceil (C * (1 + N + r + β + sizeParameter D + eps⁻¹)^d)

/-- Output register 0 is the actual estimate computed by the program. -/
def output (s : MachineState) : ℝ := s.core.regs 0

def successEvent {N r} (P : Program) (D : Data N r) (β eps C : ℝ) (d : ℕ)
    (Z : ℝ) : Set (ℕ → ℝ) :=
  {omega | let s := machineRun P (initialState D β eps) omega (timeBound D β eps C d)
    s.halted = true ∧ (1-eps)*Z ≤ output s ∧ output s ≤ (1+eps)*Z}

end KramersHubbard.PartitionFunction


