-- Prove2me | Definitions.Def_StableMSR_DecodedEntry
-- name    : StableMSR_DecodedEntry
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T13:29:22.924024+00:00
-- url     : https://prove2.me/theorems/02fe5406-cfa3-51ec-aa09-b59467afc6f9
-- title:
--   One decoded boundary assignment and its source tables
-- statement:
--   The compiler stores one candidate slot per separator vertex. The entry block enumerates all vertex trials for an admissible assignment and writes its seal. Both masks precede the mutable slot array.
-- source:
--   Ravichandran and Reyzin, arXiv:2611.03547, Appendix A.6. Operational interface for the regional separator implementation.

import Definitions.Def_StableMSR_EligibleSeparatorRows

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.EntryWriter
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit TightLanguage CutTraversal SeparatorLevels
set_option autoImplicit false

private def atCommand (p : Program) (i : ℕ) := ((listOf p)[i]?).getD .skip
private def countedBody (p : Program) : Program := match atCommand p 3 with
  | .loop _ _ b => atCommand b 0
  | _ => .skip

/-- The source block reached when every boundary vertex accepts its decoded slot. -/
def assignmentBlock : Program := match atCommand (countedBody (atCommand entryProgram 5)) 4 with
  | .cond _ _ yes _ => yes
  | _ => .skip

/-- The geometry and both masks precede the table of decoded slots. Outside the
boundary this working table is zero, so a trial can temporarily use its pivot cell. -/
structure Rows (n : ℕ) (c cut : List ℕ) (slot : ℕ → ℕ) (z a : State) : Prop where
  layout : ∃ points boundary vals : ℕ,
    a.reg 247=(points:ℤ) ∧ a.reg 241=(boundary:ℤ) ∧ a.reg 250=(vals:ℤ) ∧
    (z.reg 8).toNat ≤ vals ∧ points+n ≤ vals ∧ boundary+n ≤ vals ∧ vals+n ≤ (a.reg 8).toNat ∧
    (∀ j < n, a.heap (points+j) = if j ∈ c then 1 else 0) ∧
    (∀ j < n, a.heap (boundary+j) = if j ∈ cut then 1 else 0) ∧
    (∀ j < n, a.heap (vals+j) = if j ∈ cut then (slot j:ℤ) else 0)

def word (a : State) (i : ℕ) := (a.heap ((a.reg 76).toNat+i)).toNat
def permitted (a : State) (p i : ℕ) := decide (1 ≤ a.heap ((a.reg 81).toNat+(p*(a.reg 70).toNat+i)))
def row (a : State) (cut : List ℕ) (slot : ℕ → ℕ) : Assignment :=
  cut.map (fun v => (v,word a (slot v)))

/-- The work for one decoded admissible assignment, with all masks and slots in
place. Its source loops run the candidate trials and then write the entry's seal. -/
def AssignmentCalls (d : Instance) (w level : ℕ) (m : ℤ → ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) →
    seed ∈ allowed d cut → let c := pieceAt d (allowed d cut) seed
    c.head?=some seed → c.length=level+1 → rimOf d c=cut →
    ∀ slot : ℕ → ℕ, Rows d.n c cut slot z a →
      (∀ j ∈ cut, slot j < (a.reg 70).toNat ∧ permitted a j (slot j)=true) →
      ∃ t k, Executes d.n m assignmentBlock a t k ∧ k ≤ V ∧ Between a t ∧
        t.output=a.output++entry Naming.name d c (row a cut slot)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.EntryWriter


