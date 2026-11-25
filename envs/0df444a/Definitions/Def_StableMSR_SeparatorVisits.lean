-- Prove2me | Definitions.Def_StableMSR_SeparatorVisits
-- name    : StableMSR_SeparatorVisits
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T12:31:07.337009+00:00
-- url     : https://prove2.me/theorems/053f559d-328a-4174-86cd-3cba4ed7d987
-- title:
--   Component representatives in a single separator visit
-- statement:
--   At a separator the allowed vertices are the active vertices outside the cut. A component row is presented to the entry writer precisely when its seed is its least vertex. The row and the ordered separator are available throughout this call.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_CutTraversal

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

def allowed (d : Instance) (cut : List ℕ) := (vertices d).filter fun p=> !cut.contains p

private def command (p : Program) (i : ℕ) := ((listOf p)[i]?).getD .skip
private def yesBranch (p : Program) (i : ℕ) := match command p i with
  | .cond _ _ yes _ => yes
  | _ => .skip
private def forBody (p : Program) := match command p 3 with
  | .loop _ _ body => command body 0
  | _ => .skip

/-- Actual source block executed for an allowed seed which is the least vertex of its component. -/
def representativeWork := yesBranch (yesBranch (forBody (command src_visit 3)) 1) 9

/-- Membership row, already filled by the connected-component routine. -/
structure ComponentArg (n : ℕ) (c : List ℕ) (s : State) : Prop where
  row : ∃b : ℕ, s.reg 247=(b:ℤ) ∧ b+n ≤ (s.reg 8).toNat ∧
    ∀q<n,s.heap (b+q)=if q∈c then 1 else 0

/-- Work on the unique representative of a component, including its size and boundary checks. -/
def Representatives (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop :=
  ∀a cut seed, Between z a → cut∈cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed∈allowed d cut → a.reg 246=(seed:ℤ) →
    let c:=pieceAt d (allowed d cut) seed
    c.head?=some seed → ComponentArg d.n c a →
      ∃t k, Executes d.n m representativeWork a t k ∧ k ≤ V ∧ Between a t ∧
        t.output=a.output++visitTape Naming.name d level cut c

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


