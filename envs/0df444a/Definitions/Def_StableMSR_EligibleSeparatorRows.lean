-- Prove2me | Definitions.Def_StableMSR_EligibleSeparatorRows
-- name    : StableMSR_EligibleSeparatorRows
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T12:39:07.973039+00:00
-- url     : https://prove2.me/theorems/d276e32a-ca36-4abb-b297-f00d35862509
-- title:
--   Assignment entries for a verified component and boundary
-- statement:
--   The assignment block receives a component with the specified cardinality and exact external boundary. It emits the trials and closing instruction for each admissible assignment in reference order.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_SeparatorVisits

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- This is the assignment-enumeration branch of the representative's program,
entered after checking the component size and comparing the boundary bitmap. -/
def entryProgram : Program := match (((listOf representativeWork)[8]?) : Option Program) with
  | some (Program.cond _ _ yes _) => yes
  | _ => .skip

/-- The entry block ranges over boundary assignments and writes all trials and the
closing seal for each assignment. Both the component and its exact boundary have
already been identified. -/
def Entries (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop :=
  ∀a cut seed, Between z a → cut∈cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed∈allowed d cut → a.reg 246=(seed:ℤ) →
    let c:=pieceAt d (allowed d cut) seed
    c.head?=some seed → ComponentArg d.n c a → c.length=level+1 → rimOf d c=cut →
      ∃t k, Executes d.n m entryProgram a t k ∧ k ≤ V ∧ Between a t ∧
        t.output=a.output++(assignments d cut).flatMap (entry Naming.name d c)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


