-- Prove2me | Definitions.Def_StableMSR_VertexBlockRows
-- name    : StableMSR_VertexBlockRows
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T04:44:39.58962+00:00
-- url     : https://prove2.me/theorems/daf380e1-c62f-5d60-a485-a190089f8b1a
-- title:
--   Block membership rows and their representatives in the regional menu program
-- statement:
--   In the per-vertex procedure, a window point seeds one membership row. The source loop fills this row, then compares it with earlier marked rows. For a family of point sets indexed by seeds, the representative set consists of the least window index yielding each distinct set. These definitions specify the code and the index convention used by the window-partition test.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
open StableMSR.Recovery
open scoped Classical
set_option autoImplicit false

/-- Select one instruction of a chain in the source program. -/
def instruction (p : Program) (i : ℕ) : Program := (listOf p)[i]?.getD .skip

/-- Extract the user body of a counted source loop, before the counter increment. -/
def countedBody (p : Program) : Program := match instruction p 3 with
  | .loop _ _ body => instruction body 0
  | _ => .skip

def insideBranch : Program → Program
  | .cond _ _ body _ => body
  | _ => .skip

/-- The source sweep over the possible seeds of a block. -/
def seedLoop : Program := instruction src_data_for_vertex 20

/-- Instructions executed for a seed belonging to the current window. -/
def seedWork : Program := insideBranch (instruction (countedBody seedLoop) 1)

/-- Fill the membership row for the current seed. -/
def fillBlock : Program := instruction seedWork 4

/-- Initialize the representative flag and scan earlier selected rows for a duplicate. -/
def checkRepresentative : Program := chain (((listOf seedWork).drop 5).take 3)

/-- Candidate block at a numerical seed index. -/
def rowBlock {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h c j : ℕ) : Cluster n :=
  Bits.lookup (Bits.block m W h c) j ∅

/-- Exactly the least window index producing each distinct row. -/
noncomputable def representatives {n : ℕ} (W : Cluster n) (C : ℕ → Cluster n) : Finset ℕ :=
  (W.image Fin.val).filter fun i => ∀ q ∈ W, q.val < i → C q.val ≠ C i

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows


