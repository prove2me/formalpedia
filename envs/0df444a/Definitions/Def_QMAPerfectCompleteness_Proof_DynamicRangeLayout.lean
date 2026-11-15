-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
-- name    : QMAPerfectCompleteness_Proof_DynamicRangeLayout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:07:09.80048+00:00
-- url     : https://prove2.me/theorems/b95f480d-c5a9-4f00-8707-33bf33716da8
-- title:
--   Disjoint registers for dynamic comparisons
-- statement:
--   Constructs the source, output-tag and scratch embeddings needed by the dynamic range comparator. The layout records the disjointness required to reuse one comparison workspace without changing the input words.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DynamicRangeLayout.lean, retained declaration span lines 9–98.

/- Generated from Solutions.DynamicRangeLayout by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates



/-! Disjoint source/scratch register constructors for the dynamic range comparator scaffold. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open VariableComparison

def appendEmbedding {a b n : ℕ} (f : Fin a ↪ Fin n) (g : Fin b ↪ Fin n)
    (hfg : ∀ i j, f i ≠ g j) : Fin (a+b) ↪ Fin n :=
  ⟨Fin.append f g,by
    intro i j h
    revert h
    refine Fin.addCases (fun x => ?_) (fun x => ?_) i
    · refine Fin.addCases (fun y h => ?_) (fun y h => ?_) j
      · exact congrArg (Fin.castAdd b) (f.injective ((Fin.append_left f g x).symm.trans
          (h.trans (Fin.append_left f g y))))
      · exact (hfg x y (((Fin.append_left f g x).symm.trans h).trans (Fin.append_right f g y))).elim
    · refine Fin.addCases (fun y h => ?_) (fun y h => ?_) j
      · exact (hfg y x (((Fin.append_left f g y).symm.trans h.symm).trans (Fin.append_right f g x))).elim
      · exact congrArg (Fin.natAdd a) (g.injective ((Fin.append_right f g x).symm.trans
          (h.trans (Fin.append_right f g y))))⟩

/-- Index and three threshold registers, plus shared clean borrow storage. -/
structure RangeWires (n r : ℕ) where
  tags : Fin 6 ↪ Fin n
  index : Fin r ↪ Fin n
  thresholds : Fin 3 → (Fin r ↪ Fin n)
  scratch : Fin (r+2) ↪ Fin n
  index_threshold : ∀ t i j, index i ≠ thresholds t j
  index_scratch : ∀ i j, index i ≠ scratch j
  threshold_scratch : ∀ t i j, thresholds t i ≠ scratch j
  tag_index : ∀ t i, tags t ≠ index i
  tag_threshold : ∀ t q i, tags t ≠ thresholds q i
  tag_scratch : ∀ t i, tags t ≠ scratch i

namespace RangeWires
variable {n r : ℕ} (W : RangeWires n r)

noncomputable def comparator (t : Fin 3) : Fin (3*r+2) ↪ Fin n :=
  (finCongr (by omega : 3*r+2 = (r+r)+(r+2))).toEmbedding.trans
    (appendEmbedding (appendEmbedding W.index (W.thresholds t) (W.index_threshold t)) W.scratch
      (by
        intro i j
        refine Fin.addCases (fun a => ?_) (fun a => ?_) i
        · change Fin.append W.index (W.thresholds t) (Fin.castAdd r a) ≠ W.scratch j
          rw [Fin.append_left]
          exact W.index_scratch a j
        · change Fin.append W.index (W.thresholds t) (Fin.natAdd r a) ≠ W.scratch j
          rw [Fin.append_right]
          exact W.threshold_scratch t a j))









noncomputable def toLayout : RangeLayout n r where
  tags := W.tags
  comparators := W.comparator
  disjoint t q i := by
    change W.tags t ≠ Fin.append (Fin.append W.index (W.thresholds q)) W.scratch
      (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) i)
    generalize hj : Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) i = j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) a
      · rw [Fin.append_left,Fin.append_left]
        exact W.tag_index t b
      · rw [Fin.append_left,Fin.append_right]
        exact W.tag_threshold t q b
    · rw [Fin.append_right]
      exact W.tag_scratch t a





end RangeWires
end QMAPerfectCompleteness.Main.DynamicBlockCompiler


