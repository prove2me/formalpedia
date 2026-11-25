-- Prove2me | Definitions.Def_StableMSR_CutStackMoves
-- name    : StableMSR_CutStackMoves
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T12:33:06.269439+00:00
-- url     : https://prove2.me/theorems/9a22015f-df91-45cb-9b51-42f06e6c6ee2
-- title:
--   Single-step semantics of the depth-first separator stack
-- statement:
--   The stack records the chosen vertices, the resume index of each ancestor and the membership row of the current separator. The four possible transitions skip an inactive vertex, visit a child, return to a parent or halt at the root.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_CutTraversal

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

def loopBody : Program := match remainingProgram with
  | .loop _ _ body => body
  | _ => .skip

def lower (cut : List ℕ) := (cut.getLast?.map (·+1)).getD 0
def canExtend (w : ℕ) (cut : List ℕ) (next : ℤ) :=
  cut.length < w ∧ (lower cut:ℤ) ≤ next

/-- The entries below the live depth describe precisely the pending continuations. Each
ancestor resumes one index below the child it chose. The active frame keeps its own
next signed index so that exhaustion at vertex zero is represented by minus one. -/
structure StackAt (n level base : ℕ) (z : State) (cut : List ℕ) (next : ℤ) (a : State) : Prop where
  between : Between z a
  levelReg : a.reg 259=(level:ℤ)
  bitmap : a.reg 260=(base:ℤ)
  vector : a.reg 261=((base+n:ℕ):ℤ)
  stack : a.reg 262=((base+n+n:ℕ):ℤ)
  depth : a.reg 263=(cut.length:ℤ)
  doneFlag : a.reg 264=0
  running : a.reg 1166=1
  reserved : ((base+n+n+(n+1):ℕ):ℤ) ≤ a.reg 8
  bits : ∀p<n,a.heap (base+p)=if p∈cut then 1 else 0
  ancestors : ∀i (h:i<cut.length), a.heap (base+n+i)=(cut[i]:ℤ) ∧ a.heap (base+n+n+i)=(cut[i]:ℤ)-1
  pending : a.heap (base+n+n+cut.length)=next

/-- A single controller iteration either skips an inactive candidate, pushes a vertex
and visits its separator, pops a completed child, or terminates at the root. -/
structure Moves (d : Instance) (w level base : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop where
  skipVertex : ∀ c q s, q<d.n → canExtend w c (q:ℤ) → d.active q=false →
    StackAt d.n level base z c q s →
    ∃t k, Executes d.n m loopBody s t k ∧ k ≤ 850+V ∧
      StackAt d.n level base z c ((q:ℤ)-1) t ∧ t.output=s.output
  pushVertex : ∀ c q s, q<d.n → canExtend w c (q:ℤ) → d.active q=true →
    c++[q]∈cuts (vertices d) (min w d.n) → c.length ≤ lower c → (∀p∈c,p<lower c) →
    StackAt d.n level base z c q s →
    ∃t k, Executes d.n m loopBody s t k ∧ k ≤ 850+V ∧
      StackAt d.n level base z (c++[q]) ((d.n:ℤ)-1) t ∧ t.output=s.output++cutTape d level (c++[q])
  popVertex : ∀ c q next s, q<d.n → c.length < d.n → q∉c →
    ¬canExtend w (c++[q]) next → StackAt d.n level base z (c++[q]) next s →
    ∃t k, Executes d.n m loopBody s t k ∧ k ≤ 850+V ∧
      StackAt d.n level base z c ((q:ℤ)-1) t ∧ t.output=s.output
  stopRoot : ∀ next s, ¬canExtend w [] next → StackAt d.n level base z [] next s →
    ∃t k, Executes d.n m loopBody s t k ∧ k ≤ 850+V ∧ t.reg 6>t.reg 1166 ∧ Between z t ∧ t.output=s.output

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


