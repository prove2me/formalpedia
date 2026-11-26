-- Prove2me | Definitions.Def_StableMSR_FeasibleEntryEmission
-- name    : StableMSR_FeasibleEntryEmission
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-26T00:57:41.51477+00:00
-- url     : https://prove2.me/theorems/2ad8367b-57ef-47fa-a21e-b3caa9e2629f
-- title:
--   Trial and seal emission for an already decoded boundary assignment
-- statement:
--   The actual successful branch of the separator writer receives a feasible assignment and its word indices in a reserved scratch vector. It emits the vertex trials and the closing seal while preserving the represented inputs and outer-loop counters.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation of the regional separator dynamic program.

import Definitions.Def_StableMSR_SeparatorOrdinals

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- The successful branch after all boundary digits have been decoded and checked. -/
def emitFeasible : Program :=
  match ((listOf ordinalBody)[4]? : Option Program) with
  | some (Program.cond _ _ yes _) => yes
  | _ => .skip

/-- The scratch slot for the ith digit from the right contains its word-table index. -/
def reverseVertex (cut : List ℕ) (i : ℕ) := cut.reverse[i]?.getD 0

/-- The trial and seal instructions for one already decoded, feasible assignment. -/
def FeasibleEmissions (d : Instance) (w level : ℕ) (m : ℤ → ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed ∈ allowed d cut → a.reg 246 = (seed:ℤ) →
    let c := pieceAt d (allowed d cut) seed
    c.head? = some seed → ComponentArg d.n c a → c.length = level+1 → rimOf d c = cut →
    ∀ q < (a.reg 70).toNat ^ cut.length, ∀ row : Assignment, ordinalAssignment a cut q = some row →
    ∀ t : State, OrdinalFrame d.n a t → t.reg 251 = (q:ℤ) →
      (∀ i < cut.length, t.heap ((a.reg 8).toNat + reverseVertex cut i) =
        (((q / (a.reg 70).toNat^i) % (a.reg 70).toNat:ℕ):ℤ)) →
      ∃ y k, Executes d.n m emitFeasible t y k ∧ k ≤ V ∧ OrdinalFrame d.n a y ∧
        y.reg 251=t.reg 251 ∧ y.reg 1085=t.reg 1085 ∧ y.output=t.output++entry Naming.name d c row

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


