-- Prove2me | Definitions.Def_BasicPackArb_Main_Supplement_RankMachine
-- name    : BasicPackArb_Main_Supplement_RankMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:56:37.439489+00:00
-- url     : https://prove2.me/theorems/04c32134-4b3d-4610-b2e3-691c03410628
-- title:
--   Uniform scalar programs with charged rank queries and an executable interpreter
-- statement:
--   A program is a finite list of scalar instructions. Natural registers support literals, arithmetic, comparison, branching, indirect memory and read-only input access. Scalar registers support rational literals, exact field arithmetic, comparison, indirect memory and cost input. One rank instruction reads an explicit length-$t$ bit vector from ordinary memory and returns the rank of the indicated subset of $\{0,\ldots,t-1\}$. Output is an explicitly emitted stream of naturals. All work registers start at zero; no input cell contains a packing, a minimizer or a full rank table.
--
--   The finite-fuel interpreter charges every instruction, all operand/result binary lengths for natural operations, queried bit addresses and values, rank replies and emitted output. Scalar weight is one for exact real arithmetic and binary encoding length for exact rational arithmetic. A fixed fourth-power overhead in these lengths is a polynomial simulation allowance, not an asserted algorithm exponent. The runtime relation requires
--
--   $$\operatorname{execute}(P,O,I,c,B)=\operatorname{some}(s),\qquad \operatorname{work}(s)+\operatorname{outputLength}(s)\le B,$$
--
--   and exact equality with the emitted output. Insufficient fuel and out-of-code execution fail. The only oracle instruction is rank; no connectivity, packing or submodular-minimization oracle is present. The rational specialization is executable. This separate general machine interface makes uniform polynomial-time conclusions substantive.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, pp. 6–7, §4 rank-oracle convention

import Mathlib

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Finite scalar programs. Numeric arguments are register indices, except the literal and jump
labels. Indirect loads/stores support unbounded input sizes. The only oracle is matroid rank.
The scalar field is instantiated by exact reals or exact rationals, not by arbitrary functions. -/
inductive Instruction where
  | literal (dst value : ℕ)
  | copy (dst src : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | div (dst left right : ℕ)
  | load (dst ptr : ℕ)
  | store (ptr src : ℕ)
  | input (dst ptr : ℕ)
  | branch (left right yes no : ℕ)
  | jump (label : ℕ)
  | scalarLiteral (dst : ℕ) (q : ℚ)
  | scalarCopy (dst src : ℕ)
  | scalarAdd (dst left right : ℕ)
  | scalarSub (dst left right : ℕ)
  | scalarMul (dst left right : ℕ)
  | scalarDiv (dst left right : ℕ)
  | scalarLoad (dst ptr : ℕ)
  | scalarStore (ptr src : ℕ)
  | scalarInput (dst ptr : ℕ)
  | scalarBranch (left right yes no : ℕ)
  | rankQuery (dst ptr : ℕ)
  | emit (src : ℕ)
  | halt
  deriving DecidableEq

abbrev Program := List Instruction

structure MachineState (K : Type) where
  pc : ℕ := 0
  natMem : ℕ → ℕ := fun _ => 0
  scalarMem : ℕ → K
  outputRev : List ℕ := []
  work : ℕ := 0
  halted : Bool := false

/-- Binary length with one overhead bit, including zero. -/
def bitSize (n : ℕ) : ℕ := n.bits.length + 1

def rationalSize (q : ℚ) : ℕ := bitSize q.num.natAbs + bitSize q.den + 1

namespace Machine

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def initial : MachineState K := ⟨0, fun _ => 0, fun _ => 0, [], 0, false⟩

/-- The query is an explicit length-t bit vector already constructed in ordinary memory. -/
def querySet {t : ℕ} (s : MachineState K) (ptr : ℕ) : Finset (Fin t) :=
  Finset.univ.filter (fun i => s.natMem (s.natMem ptr + i.val) = 1)

/-- One ordinary scalar/natural operation. No instruction computes a packing or a minimum. -/
def effect {t : ℕ} (oracle : Finset (Fin t) → ℕ)
    (input : List ℕ) (costs : List K) (s : MachineState K) : Instruction → MachineState K
  | .literal d v => {s with pc := s.pc + 1, natMem := Function.update s.natMem d v}
  | .copy d a => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (s.natMem a)}
  | .add d a b => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (s.natMem a + s.natMem b)}
  | .sub d a b => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (s.natMem a - s.natMem b)}
  | .mul d a b => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (s.natMem a * s.natMem b)}
  | .div d a b => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (s.natMem a / s.natMem b)}
  | .load d p => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (s.natMem (s.natMem p))}
  | .store p a => {s with pc := s.pc + 1, natMem := Function.update s.natMem (s.natMem p) (s.natMem a)}
  | .input d p => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (input[s.natMem p]?.getD 0)}
  | .branch a b yes no => {s with pc := if s.natMem a ≤ s.natMem b then yes else no}
  | .jump l => {s with pc := l}
  | .scalarLiteral d q => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (q : K)}
  | .scalarCopy d a => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (s.scalarMem a)}
  | .scalarAdd d a b => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (s.scalarMem a + s.scalarMem b)}
  | .scalarSub d a b => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (s.scalarMem a - s.scalarMem b)}
  | .scalarMul d a b => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (s.scalarMem a * s.scalarMem b)}
  | .scalarDiv d a b => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (s.scalarMem a / s.scalarMem b)}
  | .scalarLoad d p => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (s.scalarMem (s.natMem p))}
  | .scalarStore p a => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem (s.natMem p) (s.scalarMem a)}
  | .scalarInput d p => {s with pc := s.pc + 1, scalarMem := Function.update s.scalarMem d (costs[s.natMem p]?.getD 0)}
  | .scalarBranch a b yes no => {s with pc := if s.scalarMem a ≤ s.scalarMem b then yes else no}
  | .rankQuery d p => {s with pc := s.pc + 1, natMem := Function.update s.natMem d (oracle (querySet s p))}
  | .emit a => {s with pc := s.pc + 1, outputRev := s.natMem a :: s.outputRev}
  | .halt => {s with halted := true}

/-- Register addresses and every scalar read/written are charged. Natural arithmetic is charged
by a schoolbook polynomial in operand/result binary lengths. The scalar weight is 1 on R and
rational bit length on Q. Query scan costs include all t addresses and bits, and the rank reply.
No whole set or vector is constructed by an uncharged instruction. -/
def charge {t : ℕ} (weight : K → ℕ) (oracle : Finset (Fin t) → ℕ)
    (input : List ℕ) (costs : List K) (s : MachineState K) (i : Instruction) : ℕ := by
  let next := effect oracle input costs s i
  let ns := fun a => bitSize a + bitSize (s.natMem a) + bitSize (next.natMem a)
  let ks := fun a => bitSize a + weight (s.scalarMem a) + weight (next.scalarMem a)
  let basic := match i with
    | .literal d v => ns d + bitSize v
    | .copy d a => ns d + ns a
    | .add d a b | .sub d a b | .mul d a b | .div d a b => ns d + ns a + ns b
    | .load d p => ns d + ns p + ns (s.natMem p)
    | .store p a => ns p + ns a + ns (s.natMem p)
    | .input d p => ns d + ns p
    | .branch a b y n => ns a + ns b + bitSize y + bitSize n
    | .jump l => bitSize l
    | .scalarLiteral d q => ks d + rationalSize q
    | .scalarCopy d a => ks d + ks a
    | .scalarAdd d a b | .scalarSub d a b | .scalarMul d a b | .scalarDiv d a b => ks d + ks a + ks b
    | .scalarLoad d p => ks d + ns p + ks (s.natMem p)
    | .scalarStore p a => ns p + ks a + ks (s.natMem p)
    | .scalarInput d p => ks d + ns p
    | .scalarBranch a b y n => ks a + ks b + bitSize y + bitSize n
    | .rankQuery d p => ns d + ns p + t +
        ∑ j : Fin t, (bitSize (s.natMem p + j.val) + bitSize (s.natMem (s.natMem p + j.val)))
    | .emit a => ns a
    | .halt => 1
  exact (1 + bitSize s.pc + basic) ^ 4

/-- Finite-fuel interpreter. Out-of-code execution fails; it never silently halts. -/
def execute {t : ℕ} (code : Program) (weight : K → ℕ)
    (oracle : Finset (Fin t) → ℕ) (input : List ℕ) (costs : List K) :
    ℕ → MachineState K → Option (MachineState K)
  | 0, s => if s.halted then some s else none
  | fuel + 1, s =>
      if s.halted then some s else
      match code[s.pc]? with
      | none => none
      | some i =>
          let next := effect oracle input costs s i
          execute code weight oracle input costs fuel
            {next with work := s.work + charge weight oracle input costs s i}

/-- Both actual accumulated work and the interpreter's instruction count are bounded.
Reversing/reading the emitted output is charged by its binary size as well. -/
def ComputesWithin {t : ℕ} (code : Program) (weight : K → ℕ)
    (oracle : Finset (Fin t) → ℕ) (input : List ℕ) (costs : List K)
    (bound : ℕ) (output : List ℕ) : Prop :=
  ∃ s, execute code weight oracle input costs bound initial = some s ∧
    s.work + (output.map bitSize).sum ≤ bound ∧ s.outputRev.reverse = output

end Machine
end BasicPackArb.Main.Supplement


