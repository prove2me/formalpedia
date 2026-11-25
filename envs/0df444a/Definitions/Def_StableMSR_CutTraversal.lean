-- Prove2me | Definitions.Def_StableMSR_CutTraversal
-- name    : StableMSR_CutTraversal
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T12:23:46.364949+00:00
-- url     : https://prove2.me/theorems/bd2f3c9f-f770-4541-8949-b75bcbb0bc0f
-- title:
--   The cut visitor and the depth-first separator stack
-- statement:
--   A separator has both an ordered list and a membership row. A visit appends the instructions for its components and preserves the allocated prefix of memory. The controller begins with an empty separator and resumes at the largest numbered vertex.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_SeparatorLevel

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit
open SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- Instructions associated with a single separator, in component order. -/
def cutTape (d : Instance) (k : ℕ) (cut : List ℕ) :=
  (keysFor d (vertices d) cut).flatMap (visitTape Naming.name d k cut)

/-- The visit routine receives the separator both as a membership bitmap and as an ordered vector. -/
structure CutInput (n level : ℕ) (cut : List ℕ) (s : State) : Prop where
  levelReg : s.reg 240=(level:ℤ)
  lengthReg : s.reg 243=(cut.length:ℤ)
  rows : ∃ b v : ℕ, s.reg 241=(b:ℤ) ∧ s.reg 242=(v:ℤ) ∧
    b+n ≤ (s.reg 8).toNat ∧ v+n ≤ (s.reg 8).toNat ∧
    (∀p<n,s.heap (b+p)=if p∈cut then 1 else 0) ∧ (∀i (h:i<cut.length),s.heap (v+i)=(cut[i]:ℤ))

/-- A visit may allocate scratch and append output. All previously allocated words survive the call. -/
def Visits (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut, Between z a → cut∈cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    ∃t k, Executes d.n m src_visit a t k ∧ k ≤ V ∧ Between a t ∧ t.output=a.output++cutTape d level cut

/-- The persistent data read by the depth-first controller. -/
structure TraversalData (d : Instance) (w : ℕ) (s : State) : Prop where
  one : s.reg 6=1
  zero : s.reg 7=0
  size : s.reg 64=(d.n:ℤ)
  width : s.reg 67=(w:ℤ)
  nonnegative : 0 ≤ s.reg 8
  active : ∃b:ℕ,s.reg 71=(b:ℤ) ∧ ∀p<d.n,b+p<(s.reg 8).toNat ∧
    s.heap (b+p)=if d.active p then 1 else 0

/-- The actual while-loop after the initial visit to the empty separator. -/
def remainingProgram := ((listOf src_all_cuts)[23]?).getD .skip

/-- At the root the next candidate is n-1, the separator is empty, and all three
stack arrays lie below the cursor available to subsequent calls. -/
structure RootStack (n level base : ℕ) (s : State) : Prop where
  levelReg : s.reg 259=(level:ℤ)
  bitmap : s.reg 260=(base:ℤ)
  vector : s.reg 261=((base+n:ℕ):ℤ)
  stack : s.reg 262=((base+n+n:ℕ):ℤ)
  depth : s.reg 263=0
  doneFlag : s.reg 264=0
  running : s.reg 1166=1
  reserved : ((base+n+n+(n+1):ℕ):ℤ) ≤ s.reg 8
  empty : ∀ p<n,s.heap (base+p)=0
  next : s.heap (base+n+n)=(n:ℤ)-1

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


