-- Prove2me | Definitions.Def_StableMSR_TrialLocalTest
-- name    : StableMSR_TrialLocalTest
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-26T03:52:41.195214+00:00
-- url     : https://prove2.me/theorems/8d6653a9-8afc-4fea-bb9e-9a74b303a7ba
-- title:
--   The final local consistency check of a vertex trial
-- statement:
--   Execution of the source suffix that checks the extended assignment and emits the close record with the correct Boolean.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_TrialChildren

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- Execute the final local-consistency check of a vertex trial with its extended
assignment already installed. Return the exact close record and the separator frame. -/
def LocalTrials (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed ∈ allowed d cut → a.reg 246=(seed:ℤ) →
    let c := pieceAt d (allowed d cut) seed
    c.head?=some seed → ComponentArg d.n c a → c.length=level+1 → rimOf d c=cut →
    ∀ q < (a.reg 70).toNat^cut.length, ∀ row : Assignment, ordinalAssignment a cut q=some row →
    ∀ v ∈ c, ∀ j < (a.reg 70).toNat, 1 ≤ a.heap ((a.reg 81).toNat+(v*(a.reg 70).toNat+j)) →
    ∀ t : State, TrialFrame d.n cut q a t →
      t.reg 223=t.reg 247 → t.reg 224=t.reg 241 → t.reg 225=t.reg 250 →
      t.reg 226=(v:ℤ) → t.reg 227=(j:ℤ) →
      t.heap ((a.reg 8).toNat+v)=(j:ℤ) →
      ∃ y k, Executes d.n m (chain ((listOf src_trial).drop 10)) t y k ∧ k≤V ∧ TrialFrame d.n cut q a y ∧
        let ext := (v,(a.heap ((a.reg 76).toNat+j)).toNat)::row
        y.output=t.output++[.close (localOK d ext)]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


