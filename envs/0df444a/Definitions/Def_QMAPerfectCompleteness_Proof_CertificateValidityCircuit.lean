-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
-- name    : QMAPerfectCompleteness_Proof_CertificateValidityCircuit
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:10:48.579945+00:00
-- url     : https://prove2.me/theorems/22af9de8-3765-44e2-8b60-deef05259a61
-- title:
--   Certificate-validity computation on physical wires
-- statement:
--   Instantiates the validity tests on the master arithmetic words and the six validity wires. The variable comparison reads $a$ and the prepared doubled word $2b$ through the shared carry bank, while the criterion tags and final validity output satisfy the disjointness conditions needed by the literal circuit.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateValidityCircuit.lean, lines 11–114.

/- Generated from Solutions.CertificateValidityCircuit by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
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



/-! Literal certificate-validity circuit on the coherent verifier's master registers. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CertificateValidityCircuit
open CertificateMasterLayout CertificateRangeCircuit DynamicBlockCompiler BlockCompiler ControlCircuits
variable (V : Verifier gatesG2)

lemma word_ne_word (a b : Fin 6) (hab : a ≠ b) (i j : Fin (r V)) :
    prepWord V a i ≠ prepWord V b j := by
  intro h
  have he := finProdFinEquiv.injective ((prepWordBank V).injective h)
  exact hab (congrArg Prod.fst he)

lemma validity_bounds (i : Fin 6) :
    BlockCircuit.bodyWires V+oldWork V+prepWork V+2 ≤ (validity V i).val := by
  change _ ≤ BlockCircuit.bodyWires V+(oldWork V+prepWork V+2)+i.val
  omega

lemma validity_ne_word (t d : Fin 6) (j : Fin (r V)) : validity V t ≠ prepWord V d j := by
  intro h
  have ht := validity_bounds V t
  have hw := (word_bounds V d j).2
  have hv := congrArg Fin.val h
  have hspan : 6*r V ≤ prepWork V := by dsimp only [prepWork,r]; omega
  omega

lemma validity_ne_scratch (t : Fin 6) (j : Fin (r V+2)) :
    validity V t ≠ CertificateRangeCircuit.scratch V j := by
  intro h
  have ht := validity_bounds V t
  have hs := (scratch_bounds V j).2
  have hv := congrArg Fin.val h
  omega

/-- The validity A<2B comparator shares the same carry/temp storage as the range comparators. -/
def comparatorWires : RangeWires (total V) (r V) where
  tags := validity V
  index := wordEmbedding V 0
  thresholds _ := wordEmbedding V 3
  scratch := CertificateRangeCircuit.scratch V
  index_threshold _ i j := word_ne_word V 0 3 (by decide) i j
  index_scratch i j := by
    intro h
    have hw := (word_bounds V 0 i).2
    have hs := (scratch_bounds V j).1
    have hv := congrArg Fin.val h
    change (prepWord V 0 i).val = (CertificateRangeCircuit.scratch V j).val at hv
    omega
  threshold_scratch _ i j := by
    intro h
    have hw := (word_bounds V 3 i).2
    have hs := (scratch_bounds V j).1
    have hv := congrArg Fin.val h
    change (prepWord V 3 i).val = (CertificateRangeCircuit.scratch V j).val at hv
    omega
  tag_index t i := validity_ne_word V t 0 i
  tag_threshold t _ i := validity_ne_word V t 3 i
  tag_scratch := validity_ne_scratch V

def criterionTags : Fin 5 ↪ Fin (total V) :=
  (⟨fun j => ⟨j.val,by have := j.isLt; omega⟩,by
    intro i j h; exact Fin.ext (congrArg (fun z : Fin 6 => z.val) h)⟩ : Fin 5 ↪ Fin 6).trans (validity V)

def constLayout (d : Fin 6) : AndLayout (r V) (total V) where
  controls := wordEmbedding V d
  flags := prepCarry V
  disjoint i j := by
    intro h
    have hw := (word_bounds V d i).2
    have hv := congrArg Fin.val h
    change (prepWord V d i).val = BlockCircuit.bodyWires V+(oldWork V+6*r V)+j.val at hv
    omega

lemma validity_ne_carry (t : Fin 6) (j : Fin (k V+3)) : validity V t ≠ prepCarry V j := by
  intro h
  have ht := validity_bounds V t
  have hv := congrArg Fin.val h
  change (validity V t).val = BlockCircuit.bodyWires V+(oldWork V+6*r V)+j.val at hv
  have hj := j.isLt
  dsimp [prepWork,r,k] at *
  omega

noncomputable def layout : CertificateValidity.Layout (k V) (total V) where
  a := constLayout V 0
  b := constLayout V 2
  cmp := (comparatorWires V).comparator 0
  tags := criterionTags V
  tag_a t i := validity_ne_word V ⟨t.val,by have := t.isLt; omega⟩ 0 i
  tag_b t i := validity_ne_word V ⟨t.val,by have := t.isLt; omega⟩ 2 i
  tag_af t i := validity_ne_carry V ⟨t.val,by have := t.isLt; omega⟩ i
  tag_bf t i := validity_ne_carry V ⟨t.val,by have := t.isLt; omega⟩ i
  tag_cmp t i := (comparatorWires V).toLayout.disjoint ⟨t.val,by have := t.isLt; omega⟩ 0 i

lemma index_width : 3 ≤ k V := by
  dsimp only [k,indexQubits]
  omega

lemma output_ne_tags (t : Fin 5) : validity V 5 ≠ (layout V).tags t := by
  intro h
  have he := (validity V).injective h
  have hv := congrArg Fin.val he
  have ht := t.isLt
  change (5 : ℕ) = t.val at hv
  omega

noncomputable def program : CleanProgram (total V) (layout V).Clean :=
  (layout V).validProgram (index_width V) (validity V 5) (output_ne_tags V)
    (validity_ne_carry V 5) (validity_ne_carry V 5)
    ((comparatorWires V).toLayout.disjoint 5 0)

noncomputable def gates : List (Instr gatesG2 (total V)) := (program V).gates



end QMAPerfectCompleteness.Main.CertificateValidityCircuit


