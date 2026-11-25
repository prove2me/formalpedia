-- Prove2me | Definitions.Def_StableMSR_BoundaryDigitScan
-- name    : StableMSR_BoundaryDigitScan
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T13:33:49.618451+00:00
-- url     : https://prove2.me/theorems/1601f28d-430f-51fd-bbf5-952179335d0c
-- title:
--   The compiler’s boundary-digit scan
-- statement:
--   The radix-power and boundary-decoding blocks in the regional entry writer, with the current quotient, accumulated validity and partial slot array. Digits are read in reverse boundary order.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_DecodedEntry

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.EntryWriter
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.TightLanguage CutTraversal
set_option autoImplicit false

/-- The source prefix that copies the ordinal, initializes validity, and decodes
every separator vertex in right-to-left order. -/
def decodeProgram : Program :=
  let loopCmd := ((listOf entryProgram)[5]?).getD .skip
  let ordinal := match ((listOf loopCmd)[3]? : Option Program) with
    | some (Program.loop _ _ b) => ((listOf b)[0]?).getD .skip
    | _ => .skip
  chain ((listOf ordinal).take 4)

/-- The entry program first computes the radix raised to the separator length. -/
def powerProgram : Program := chain ((listOf entryProgram).take 3)

/-- Digits already decoded, their accumulated validity, and the remaining quotient. -/
structure Trace where
  quotient : ℕ
  digits : List (ℕ × ℕ)
  valid : Bool

def startTrace (q : ℕ) : Trace := ⟨q,[],true⟩
def nextDigit (B : ℕ) (keep : ℕ → ℕ → Bool) (t : Trace) (p : ℕ) : Trace :=
  ⟨t.quotient/B,(p,t.quotient%B)::t.digits,t.valid && keep p (t.quotient%B)⟩
def atDigit (B : ℕ) (keep : ℕ → ℕ → Bool) (cut : List ℕ) (q i : ℕ) :=
  (cut.reverse.take i).foldl (nextDigit B keep) (startTrace q)

/-- The actual scratch row and two live registers after decoding a prefix. -/
structure DigitImage (n vals : ℕ) (cut : List ℕ) (tr : Trace) (s t : State) : Prop where
  quotient : t.reg 252=(tr.quotient:ℤ)
  flag : t.reg 253=if tr.valid then 1 else 0
  lowHeap : ∀j<vals,t.heap j=s.heap j
  cells : ∀p j,(p,j)∈tr.digits → t.heap (vals+p)=(j:ℤ)
  unused : ∀p<n,p∉cut → t.heap (vals+p)=0
  output : t.output=s.output
  closed : t.closed=s.closed


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.EntryWriter


