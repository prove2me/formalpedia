-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
-- name    : QMAPerfectCompleteness_Proof_BlockTaggedActions
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:46.499753+00:00
-- url     : https://prove2.me/theorems/cbc9a553-7845-4435-8a53-e2e8c55ffa2b
-- title:
--   Logical flag and clock actions with range tags
-- statement:
--   For a verifier and certificate $(z,a,b)$, specifies the logical flag updates controlled by the cached index-range predicates, the final-clock test and equality with $z$. The post-call map then advances the clock cyclically exactly on the active range, leaving the remaining data registers fixed.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockTaggedActions.lean, lines 47–106.

/- Generated from Solutions.BlockTaggedActions by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates



/-! Deterministic block SELECT operations on the indexed predicate-tagged workspace fiber. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockStateCoordinates BlockClockCoordinates
variable (V : Verifier gatesG2)











/-- The logical middle operation, including the index-range control. -/
noncomputable def midLogical (a b : ℕ) (p : Logical V) : Logical V :=
  (p.1,p.2.1,p.2.2.1,xor p.2.2.2
    ((Layout.rangeTruth a b p.1.val 3 && decide (p.2.1.val < ell V.proofQubits)) && p.2.2.1 V.output))







/-- The logical closing/identity flag updates before the controlled clock shift. -/
noncomputable def postFlagLogical (z : V.Proof) (a b : ℕ) (p : Logical V) : Logical V :=
  (p.1,p.2.1,p.2.2.1,
    xor (xor p.2.2.2 (Layout.rangeTruth a b p.1.val 0))
      (Layout.rangeTruth a b p.1.val 4 &&
        (decide (p.2.1.val = ell V.proofQubits) && decide (V.proofPart p.2.2.1 = z))))





/-- The logical post-call permutation, before range erasure and final Hadamards. -/
noncomputable def postLogical (z : V.Proof) (a b : ℕ) (p : Logical V) : Logical V :=
  let q := postFlagLogical V z a b p
  (q.1,q.2.1+Fin.ofNat (ell V.proofQubits+1) ((Layout.rangeTruth a b q.1.val 5).toNat),q.2.2)



end QMAPerfectCompleteness.Main.BlockImplements


