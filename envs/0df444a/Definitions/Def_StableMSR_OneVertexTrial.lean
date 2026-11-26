-- Prove2me | Definitions.Def_StableMSR_OneVertexTrial
-- name    : StableMSR_OneVertexTrial
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-26T03:02:56.821953+00:00
-- url     : https://prove2.me/theorems/86cf2330-8d64-4e4b-801a-30324136e7f7
-- title:
--   Input and output contract for one permitted vertex trial
-- statement:
--   The trial subroutine receives a component vertex and a feasible word slot, with the boundary already decoded. The procedure must emit its literals, child requests and closing compatibility flag, while preserving the boundary values and input tables.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation lemma for the boundary assignment loop.

import Definitions.Def_StableMSR_FeasibleEntryEmission

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- The immutable separator input and the live boundary digits at a trial call. -/
structure TrialFrame (n : ℕ) (cut : List ℕ) (q : ℕ) (a t : State) : Prop extends OrdinalFrame n a t where
  digits : ∀ i < cut.length, t.heap ((a.reg 8).toNat + reverseVertex cut i) =
    (((q / (a.reg 70).toNat^i) % (a.reg 70).toNat:ℕ):ℤ)

/-- The trial procedure receives one component vertex and one permissible word slot.
The caller has already selected both. On return the represented inputs and
boundary digits must be available to the next trial or the closing key writer. -/
def VertexTrials (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed ∈ allowed d cut → a.reg 246=(seed:ℤ) →
    let c := pieceAt d (allowed d cut) seed
    c.head?=some seed → ComponentArg d.n c a → c.length=level+1 → rimOf d c=cut →
    ∀ q < (a.reg 70).toNat^cut.length, ∀ row : Assignment, ordinalAssignment a cut q=some row →
    ∀ v ∈ c, ∀ j < (a.reg 70).toNat, 1 ≤ a.heap ((a.reg 81).toNat+(v*(a.reg 70).toNat+j)) →
    ∀ t : State, TrialFrame d.n cut q a t →
      t.reg 223=t.reg 247 → t.reg 224=t.reg 241 → t.reg 225=t.reg 250 →
      t.reg 226=(v:ℤ) → t.reg 227=(j:ℤ) →
      ∃ y k, Executes d.n m src_trial t y k ∧ k≤V ∧ TrialFrame d.n cut q a y ∧
        y.output=t.output++trial Naming.name d c row v ((a.heap ((a.reg 76).toNat+j)).toNat)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


