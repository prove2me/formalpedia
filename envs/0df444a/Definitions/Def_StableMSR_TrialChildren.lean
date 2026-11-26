-- Prove2me | Definitions.Def_StableMSR_TrialChildren
-- name    : StableMSR_TrialChildren
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-26T03:43:39.783239+00:00
-- url     : https://prove2.me/theorems/df2419a3-bea7-4a2f-b71d-ec61f8a6322b
-- title:
--   Trial suffix after installing the selected vertex label and deleting the vertex
-- statement:
--   Execution contract for the remaining child-key requests, local-consistency record, and frame preservation after the trial materializes its vertex-deletion bitmap.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_OneVertexTrial

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- The suffix of one vertex trial. The selected label and the bitmap after deleting
the selected vertex are already in memory. Emit the ordered child-key requests and
the local compatibility result, then restore the enclosing separator frame. -/
def ChildTrials (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed ∈ allowed d cut → a.reg 246=(seed:ℤ) →
    let c := pieceAt d (allowed d cut) seed
    c.head?=some seed → ComponentArg d.n c a → c.length=level+1 → rimOf d c=cut →
    ∀ q < (a.reg 70).toNat^cut.length, ∀ row : Assignment, ordinalAssignment a cut q=some row →
    ∀ v ∈ c, ∀ j < (a.reg 70).toNat, 1 ≤ a.heap ((a.reg 81).toNat+(v*(a.reg 70).toNat+j)) →
    ∀ t : State, TrialFrame d.n cut q a t →
      t.reg 223=t.reg 247 → t.reg 224=t.reg 241 → t.reg 225=t.reg 250 →
      t.reg 226=(v:ℤ) → t.reg 227=(j:ℤ) →
      ∀ dst : ℕ, t.reg 230=(dst:ℤ) → dst+d.n ≤ (t.reg 8).toNat →
      (∀p<d.n,t.heap (dst+p)=if p∈c ∧ p≠v then 1 else 0) →
      t.heap ((a.reg 8).toNat+v)=(j:ℤ) →
      ∃ y k, Executes d.n m (chain ((listOf src_trial).drop 9)) t y k ∧ k≤V ∧ TrialFrame d.n cut q a y ∧
        let ext := (v,(a.heap ((a.reg 76).toNat+j)).toNat)::row
        y.output=t.output++((children d c v ext).map (fun k=>Instr.need (Naming.name k))++[.close (localOK d ext)])

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


