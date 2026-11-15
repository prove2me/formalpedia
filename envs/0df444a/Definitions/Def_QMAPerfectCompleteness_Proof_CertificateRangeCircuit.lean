-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
-- name    : QMAPerfectCompleteness_Proof_CertificateRangeCircuit
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:09:42.492578+00:00
-- url     : https://prove2.me/theorems/d38bb1e8-25f6-4f8b-b711-a5325d54eead
-- title:
--   Dynamic range comparisons on the master register
-- statement:
--   Instantiates the three padded comparisons of the index with $a$, $3a$ and $3a+b$ on the actual master-layout words. The comparisons share preparation carry and temporary storage, while six disjoint persistent tags record the branch predicates used by coherent SELECT.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateRangeCircuit.lean, lines 11–112.

/- Generated from Solutions.CertificateRangeCircuit by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! The dynamic range scaffold instantiated on the master coherent-certificate wire layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QMAPerfectCompleteness.Main.CertificateRangeCircuit
open CertificateMasterLayout DynamicBlockCompiler BlockCompiler
variable (V : Verifier gatesG2)

def wordEmbedding (d : Fin 6) : Fin (r V) ↪ Fin (total V) :=
  ⟨prepWord V d,by
    intro i j h
    have hp := finProdFinEquiv.injective ((prepWordBank V).injective h)
    exact congrArg Prod.snd hp⟩

def scratch : Fin (r V+2) ↪ Fin (total V) :=
  bank V (oldWork V+6*r V) (r V+2) (by dsimp [work,prepWork,r,k]; omega)

def tags : Fin 6 ↪ Fin (total V) :=
  ⟨fun i => oldEmbedding V ((layoutOf V).tagWire ⟨i.val,by have := i.isLt; omega⟩),by
    intro i j h
    have hp := (layoutOf V).tagWire_injective ((oldEmbedding V).injective h)
    exact Fin.ext (congrArg (fun z : Fin 11 => z.val) hp)⟩

lemma word_bounds (d : Fin 6) (j : Fin (r V)) :
    BlockCircuit.bodyWires V+oldWork V ≤ (prepWord V d j).val ∧
      (prepWord V d j).val < BlockCircuit.bodyWires V+oldWork V+6*r V := by
  have hp := (finProdFinEquiv (d,j)).isLt
  change _ ≤ BlockCircuit.bodyWires V+oldWork V+(finProdFinEquiv (d,j)).val ∧ _
  change _ ∧ BlockCircuit.bodyWires V+oldWork V+(finProdFinEquiv (d,j)).val < _
  omega

lemma scratch_bounds (j : Fin (r V+2)) :
    BlockCircuit.bodyWires V+oldWork V+6*r V ≤ (scratch V j).val ∧
      (scratch V j).val < BlockCircuit.bodyWires V+oldWork V+prepWork V := by
  have hj := j.isLt
  change _ ≤ BlockCircuit.bodyWires V+(oldWork V+6*r V)+j.val ∧ _
  change _ ∧ BlockCircuit.bodyWires V+(oldWork V+6*r V)+j.val < _
  dsimp [prepWork,r,k] at *
  omega

lemma tag_bounds (i : Fin 6) :
    BlockCircuit.bodyWires V ≤ (tags V i).val ∧ (tags V i).val < BlockCircuit.bodyWires V+oldWork V := by
  have hi := i.isLt
  change _ ≤ BlockCircuit.bodyWires V+i.val ∧ BlockCircuit.bodyWires V+i.val < _
  dsimp [oldWork,Layout.work]
  omega

lemma index_outside_prep (i : Fin (r V)) (w : Fin (total V))
    (hlo : BlockCircuit.bodyWires V+oldWork V ≤ w.val)
    (hhi : w.val < BlockCircuit.bodyWires V+oldWork V+prepWork V) : paddedIndex V i ≠ w := by
  intro h
  have hv := congrArg Fin.val h
  change (if i.val<k V then i.val else
    BlockCircuit.bodyWires V+oldWork V+prepWork V+(i.val-k V)) = w.val at hv
  split_ifs at hv with hi
  · change i.val = w.val at hv
    have hbody : k V ≤ BlockCircuit.bodyWires V := by dsimp [k,BlockCircuit.bodyWires]; omega
    omega
  · omega

lemma tag_ne_index (t : Fin 6) (i : Fin (r V)) : tags V t ≠ paddedIndex V i := by
  intro h
  have ht := tag_bounds V t
  have hv := congrArg Fin.val h
  change (tags V t).val = (if i.val<k V then i.val else
    BlockCircuit.bodyWires V+oldWork V+prepWork V+(i.val-k V)) at hv
  split_ifs at hv with hi
  · change (tags V t).val = i.val at hv
    have hbody : k V ≤ BlockCircuit.bodyWires V := by dsimp [k,BlockCircuit.bodyWires]; omega
    omega
  · omega

/-- All three comparisons reuse the preparation carry chain and temporary. -/
def wires : RangeWires (total V) (r V) where
  tags := tags V
  index := paddedIndex V
  thresholds t := wordEmbedding V (![0,4,5] t)
  scratch := scratch V
  index_threshold t i j := by
    change paddedIndex V i ≠ prepWord V (![0,4,5] t) j
    exact index_outside_prep V i _ (word_bounds V _ j).1 (by
      have hw := (word_bounds V (![0,4,5] t) j).2
      have hspan : 6*r V ≤ prepWork V := by dsimp only [prepWork,r]; omega
      omega)
  index_scratch i j := index_outside_prep V i _ (by
    have hs := (scratch_bounds V j).1; omega) (scratch_bounds V j).2
  threshold_scratch t i j := by
    intro h
    have hw := (word_bounds V (![0,4,5] t) i).2
    have hs := (scratch_bounds V j).1
    have hv := congrArg Fin.val h
    change (prepWord V (![0,4,5] t) i).val = (scratch V j).val at hv
    omega
  tag_index := tag_ne_index V
  tag_threshold t q i := by
    intro h
    have ht := (tag_bounds V t).2
    have hw := (word_bounds V (![0,4,5] q) i).1
    have hv := congrArg Fin.val h
    change (tags V t).val = (prepWord V (![0,4,5] q) i).val at hv
    omega
  tag_scratch t i := by
    intro h
    have ht := (tag_bounds V t).2
    have hs := (scratch_bounds V i).1
    have hv := congrArg Fin.val h
    omega

noncomputable def layout : RangeLayout (total V) (r V) := (wires V).toLayout
noncomputable def gates : List (Instr gatesG2 (total V)) := (layout V).gates



end QMAPerfectCompleteness.Main.CertificateRangeCircuit


