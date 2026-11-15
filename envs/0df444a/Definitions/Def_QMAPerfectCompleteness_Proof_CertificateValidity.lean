-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
-- name    : QMAPerfectCompleteness_Proof_CertificateValidity
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:08:49.123053+00:00
-- url     : https://prove2.me/theorems/dd76fbf7-9830-4f5f-b257-d27c1cdec4f2
-- title:
--   Reversible numerical certificate-validity tests
-- statement:
--   For a width $k$ of at least three, defines the five tests $a>0$, $b>0$, $2^{k-3} ≤ a$, $a ≤ 2^{k-2}$ and $2b ≤ a$, with the binary source bounds supplied by the register widths. Constant and variable comparisons compute criterion tags, and their five-way conjunction controls a separate validity bit using reusable clean carry storage.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateValidity.lean, lines 11–217.

/- Generated from Solutions.CertificateValidity by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
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
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
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



/-! Exact polynomial-size certificate validity predicates for the coherent verifier. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateValidity
open BlockCompiler ReversibleGadgets ControlCircuits ComparisonCircuits VariableComparison

instance validDecidable (V : Verifier gatesG2) (a b : ℕ) : Decidable (IsValidCertificate V a b) := by
  unfold IsValidCertificate
  infer_instance

/-- Positivity, lower/upper A bounds, and 2B≤A. The k-bit source bound is structural. -/
def checks (k a b : ℕ) : Fin 5 → Bool :=
  ![!decide (a<1),!decide (b<1),!decide (a<2^(k-3)),
    decide (a<2^(k-2)+1),!decide (a<2*b)]





/-- Source/borrow layouts and five criterion bits for the concrete validity computation. -/
structure Layout (k n : ℕ) where
  a : AndLayout (k+2) n
  b : AndLayout (k+2) n
  cmp : Fin (3*(k+2)+2) ↪ Fin n
  tags : Fin 5 ↪ Fin n
  tag_a : ∀ t i, tags t ≠ a.controls i
  tag_b : ∀ t i, tags t ≠ b.controls i
  tag_af : ∀ t i, tags t ≠ a.flags i
  tag_bf : ∀ t i, tags t ≠ b.flags i
  tag_cmp : ∀ t i, tags t ≠ cmp i

namespace Layout
variable {k n : ℕ} (L : Layout k n)

def Clean (x : Basis n) : Prop :=
  (∀ j, x (L.a.flags j) = false) ∧ (∀ j, x (L.b.flags j) = false) ∧ VariableEquality.Clean L.cmp x

lemma clean_update (x : Basis n) (hx : L.Clean x) (t : Fin 5) (v : Bool) :
    L.Clean (Function.update x (L.tags t) v) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    rw [Function.update_of_ne (L.tag_af t j).symm]
    exact hx.1 j
  · intro j
    rw [Function.update_of_ne (L.tag_bf t j).symm]
    exact hx.2.1 j
  · intro j
    rw [Function.update_of_ne (show carryWire L.cmp j ≠ L.tags t from (L.tag_cmp t _).symm)]
    exact hx.2.2.1 j
  · rw [Function.update_of_ne (show tempWire L.cmp ≠ L.tags t from (L.tag_cmp t _).symm)]
    exact hx.2.2.2

abbrev aValue (x : Basis n) : ℕ := BlockCircuit.bitsValue x L.a.controls
abbrev bValue (x : Basis n) : ℕ := BlockCircuit.bitsValue x L.b.controls





def constAction (useB : Bool) (threshold : ℕ) (t : Fin 5) (x : Basis n) : Basis n :=
  Function.update x (L.tags t) (xor (x (L.tags t))
    (decide ((if useB then L.bValue x else L.aValue x) < threshold)))

noncomputable def constProgram (useB : Bool) (threshold : ℕ) (t : Fin 5) : CleanProgram n L.Clean where
  gates := if useB then compareNatGates L.b threshold (L.tags t) (fun i => L.tag_bf t i)
    else compareNatGates L.a threshold (L.tags t) (fun i => L.tag_af t i)
  action := L.constAction useB threshold t
  sound y x hx := by
    cases useB
    · exact compareNatGates_matrix_bitsValue L.a threshold (L.tags t) (L.tag_a t) (L.tag_af t) y x hx.1
    · exact compareNatGates_matrix_bitsValue L.b threshold (L.tags t) (L.tag_b t) (L.tag_bf t) y x hx.2.1
  preserves x hx := L.clean_update x hx t _

noncomputable def flipProgram (t : Fin 5) : CleanProgram n L.Clean where
  gates := [xAt (L.tags t)]
  action := xAction (L.tags t)
  sound y x _ := by simp only [circuitMatrix,Matrix.one_mul,xAt_matrix]; rfl
  preserves x hx := L.clean_update x hx t _

noncomputable def varProgram : CleanProgram n L.Clean where
  gates := comparatorGates L.cmp (L.tags 4) (L.tag_cmp 4)
  action x := Function.update x (L.tags 4) (xor (x (L.tags 4)) (VariableEquality.comparisonBit L.cmp x))
  sound y x hx := comparatorGates_matrix _ _ _ y x hx.2.2.1 hx.2.2.2
  preserves x hx := L.clean_update x hx 4 _

/-- Five actual comparisons and the four required Boolean negations. -/
noncomputable def program : CleanProgram n L.Clean :=
  (((((((((L.constProgram false 1 0).append (L.flipProgram 0)).append
    (L.constProgram true 1 1)).append (L.flipProgram 1)).append
    (L.constProgram false (2^(k-3)) 2)).append (L.flipProgram 2)).append
    (L.constProgram false (2^(k-2)+1) 3)).append L.varProgram).append (L.flipProgram 4))

noncomputable abbrev action : Basis n → Basis n := L.program.action
noncomputable def gates : List (Instr gatesG2 n) := L.program.gates

def truth (x : Basis n) : Fin 5 → Bool :=
  ![!decide (L.aValue x<1),!decide (L.bValue x<1),!decide (L.aValue x<2^(k-3)),
    decide (L.aValue x<2^(k-2)+1),!VariableEquality.comparisonBit L.cmp x]











/-- Six flags from the existing A-comparison borrow bank implement a five-way conjunction. -/
def conjunctionLayout (hk : 3≤k) : AndLayout 5 n where
  controls := L.tags
  flags := ⟨fun j => L.a.flags ⟨j.val,by have := j.isLt; omega⟩,by
    intro i j h
    have he := L.a.flags.injective h
    exact Fin.ext (congrArg (fun z : Fin (k+3) => z.val) he)⟩
  disjoint i j := L.tag_af i _

noncomputable def outputProgram (hk : 3≤k) (out : Fin n)
    (hot : ∀ t, out ≠ L.tags t) (hoa : ∀ j, out ≠ L.a.flags j)
    (hob : ∀ j, out ≠ L.b.flags j) (hoc : ∀ j, out ≠ L.cmp j) : CleanProgram n L.Clean where
  gates := multiControlledX (L.conjunctionLayout hk) out (fun j => hoa _)
  action x := Function.update x out (xor (x out) (prefixAnd (L.conjunctionLayout hk) x 5 le_rfl))
  sound y x hx := multiControlledX_matrix (L.conjunctionLayout hk) out hot
    (fun j => hoa _) y x (fun j => hx.1 _)
  preserves x hx := by
    refine ⟨?_,?_,?_,?_⟩
    · intro j
      rw [Function.update_of_ne (hoa j).symm]
      exact hx.1 j
    · intro j
      rw [Function.update_of_ne (hob j).symm]
      exact hx.2.1 j
    · intro j
      rw [Function.update_of_ne (show carryWire L.cmp j ≠ out from (hoc _).symm)]
      exact hx.2.2.1 j
    · rw [Function.update_of_ne (show tempWire L.cmp ≠ out from (hoc _).symm)]
      exact hx.2.2.2

/-- Compute five criterion tags and XOR their conjunction into the validity output bit. -/
noncomputable def validProgram (hk : 3≤k) (out : Fin n)
    (hot : ∀ t, out ≠ L.tags t) (hoa : ∀ j, out ≠ L.a.flags j)
    (hob : ∀ j, out ≠ L.b.flags j) (hoc : ∀ j, out ≠ L.cmp j) : CleanProgram n L.Clean :=
  L.program.append (L.outputProgram hk out hot hoa hob hoc)







end Layout
end QMAPerfectCompleteness.Main.CertificateValidity


