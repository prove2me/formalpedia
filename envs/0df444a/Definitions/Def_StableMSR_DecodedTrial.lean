-- Prove2me | Definitions.Def_StableMSR_DecodedTrial
-- name    : StableMSR_DecodedTrial
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T13:40:27.797658+00:00
-- url     : https://prove2.me/theorems/cb90e963-bd31-42ce-beb1-38cc14d361e5
-- title:
--   An individual decoded regional trial and its entry seal
-- statement:
--   One candidate trial runs on a pivot, a feasible slot and the existing boundary labels. Its contract records the owned blocks, references to smaller components, the compatibility bit and preservation of the caller’s memory.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_DecodedEntry

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.EntryWriter
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit TightLanguage CutTraversal SeparatorLevels
set_option autoImplicit false

/-- After visiting all pivots and all feasible slots, the source names and seals the entry. -/
def sealProgram : Program := chain ((listOf assignmentBlock).drop 1)

/-- Run one trial with its pivot, candidate slot, component mask and decoded
boundary assignment. Its output is the local literals, child references and closing flag. -/
def TrialCalls (d : Instance) (w level : ℕ) (m : ℤ → ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) →
    seed ∈ allowed d cut → let c := pieceAt d (allowed d cut) seed
    c.head?=some seed → c.length=level+1 → rimOf d c=cut →
    ∀ slot : ℕ → ℕ, Rows d.n c cut slot z a →
      (∀ j ∈ cut, slot j < (a.reg 70).toNat ∧ permitted a j (slot j)=true) →
      ∀ p ∈ c, ∀ i < (a.reg 70).toNat, permitted a p i=true →
      a.reg 223=a.reg 247 → a.reg 224=a.reg 241 → a.reg 225=a.reg 250 →
      a.reg 226=(p:ℤ) → a.reg 227=(i:ℤ) →
      ∃ t k, Executes d.n m src_trial a t k ∧ k ≤ V ∧ Between a t ∧
        t.output=a.output++trial Naming.name d c (row a cut slot) p (word a i)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.EntryWriter


