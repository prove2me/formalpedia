-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
-- name    : QMAPerfectCompleteness_Proof_BlockCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:55:51.724511+00:00
-- url     : https://prove2.me/theorems/e4e8ef66-1bc5-44a0-88cc-368fdde715d6
-- title:
--   Logical coordinates of the physical block register
-- statement:
--   For a verifier and a scratch width, constructs an equivalence between physical bit strings and the logical index, clock, verifier-wire and flag registers together with scratch bits. The clock conversion uses its exact power-of-two cardinality, and the logical component agrees with the published block-register decoding.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockCoordinates.lean, lines 9–107.

/- Generated from Solutions.BlockCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Exact basis coordinates for the published block register, including clean workspace. -/
open Matrix
namespace QMAPerfectCompleteness.Main.BlockCoordinates
open BlockCircuit IndexHadamards

lemma clock_card (m : ℕ) : ell m + 1 = 2 ^ clockQubits m := by
  have hp : 0 < 2 ^ clockQubits m := pow_pos (by omega) _
  unfold ell
  omega

abbrev RawReg (V : Verifier gatesG2) (w : ℕ) :=
  Basis (indexQubits V) × Basis (clockWires V) × V.Wire × Bool × Basis w

def unpack (V : Verifier gatesG2) (w : ℕ) (x : Basis (bodyWires V+w)) : RawReg V w :=
  (x ∘ indexWire,x ∘ clockWire,x ∘ verifierWire,x flagWire,x ∘ workspaceWire)

def pack (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w) : Basis (bodyWires V+w) :=
  Fin.append (Fin.append (Fin.append (Fin.append p.1 p.2.1) p.2.2.1)
    (fun _ : Fin 1 => p.2.2.2.1)) p.2.2.2.2

@[simp] lemma pack_index (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w)
    (i : Fin (indexQubits V)) : pack V w p (indexWire i) = p.1 i := by
  change (Fin.append (Fin.append (Fin.append (Fin.append p.1 p.2.1) p.2.2.1)
    (fun _ : Fin 1 => p.2.2.2.1)) p.2.2.2.2)
      (Fin.castAdd w (Fin.castAdd 1 (Fin.castAdd _ (Fin.castAdd _ i)))) = _
  simp only [Fin.append_left]

@[simp] lemma pack_clock (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w)
    (i : Fin (clockWires V)) : pack V w p (clockWire i) = p.2.1 i := by
  change (Fin.append (Fin.append (Fin.append (Fin.append p.1 p.2.1) p.2.2.1)
    (fun _ : Fin 1 => p.2.2.2.1)) p.2.2.2.2)
      (Fin.castAdd w (Fin.castAdd 1 (Fin.castAdd _ (Fin.natAdd _ i)))) = _
  simp only [Fin.append_left,Fin.append_right]

@[simp] lemma pack_verifier (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w)
    (i : Fin (V.proofQubits+V.ancillaQubits)) : pack V w p (verifierWire i) = p.2.2.1 i := by
  change (Fin.append (Fin.append (Fin.append (Fin.append p.1 p.2.1) p.2.2.1)
    (fun _ : Fin 1 => p.2.2.2.1)) p.2.2.2.2)
      (Fin.castAdd w (Fin.castAdd 1 (Fin.natAdd _ i))) = _
  simp only [Fin.append_left,Fin.append_right]

@[simp] lemma pack_flag (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w) :
    pack V w p flagWire = p.2.2.2.1 := by
  have hw : (flagWire : Fin (bodyWires V+w)) =
      Fin.castAdd w (Fin.natAdd (indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits)) (0 : Fin 1)) := by
    apply Fin.ext
    simp [flagWire]
  rw [hw]
  exact (Fin.append_left _ _ _).trans (Fin.append_right _ _ _)

@[simp] lemma pack_workspace (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w)
    (i : Fin w) : pack V w p (workspaceWire i) = p.2.2.2.2 i := Fin.append_right _ _ _

@[simp] theorem unpack_pack (V : Verifier gatesG2) (w : ℕ) (p : RawReg V w) :
    unpack V w (pack V w p) = p := by
  apply Prod.ext
  · funext i; exact pack_index V w p i
  · apply Prod.ext
    · funext i; exact pack_clock V w p i
    · apply Prod.ext
      · funext i; exact pack_verifier V w p i
      · exact Prod.ext (pack_flag V w p) (funext (pack_workspace V w p))

lemma unpack_injective (V : Verifier gatesG2) (w : ℕ) : Function.Injective (unpack V w) := by
  intro x y h
  funext j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · refine Fin.addCases (fun a => ?_) (fun a => ?_) a
      · refine Fin.addCases (fun a => ?_) (fun a => ?_) a
        · exact congrFun (congrArg Prod.fst h) a
        · exact congrFun (congrArg (fun p : RawReg V w => p.2.1) h) a
      · exact congrFun (congrArg (fun p : RawReg V w => p.2.2.1) h) a
    · have ha : a = 0 := Subsingleton.elim _ _
      subst a
      have hw : Fin.castAdd w
          (Fin.natAdd (indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits)) (0 : Fin 1)) =
          (flagWire : Fin (bodyWires V+w)) := by
        apply Fin.ext
        simp [flagWire]
      rw [hw]
      exact congrArg (fun p : RawReg V w => p.2.2.2.1) h
  · exact congrFun (congrArg (fun p : RawReg V w => p.2.2.2.2) h) a

def rawEquiv (V : Verifier gatesG2) (w : ℕ) : Basis (bodyWires V+w) ≃ RawReg V w where
  toFun := unpack V w
  invFun := pack V w
  left_inv x := unpack_injective V w (unpack_pack V w (unpack V w x))
  right_inv := unpack_pack V w

/-- Bits-to-integer conversion uses the exact power-of-two size of the published clock. -/
def clockEquiv (V : Verifier gatesG2) : Basis (clockWires V) ≃ Clock V.proofQubits :=
  (bitsEquiv (clockWires V)).trans (finCongr (clock_card V.proofQubits).symm)

def logicalEquiv (V : Verifier gatesG2) (w : ℕ) : RawReg V w ≃ V.BlockReg (indexQubits V) × Basis w where
  toFun p := ((bitsEquiv _ p.1,clockEquiv V p.2.1,p.2.2.1,p.2.2.2.1),p.2.2.2.2)
  invFun p := ((bitsEquiv _).symm p.1.1,(clockEquiv V).symm p.1.2.1,p.1.2.2.1,p.1.2.2.2,p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Genuine wire-layout equivalence, with the body exactly in the published decode coordinates. -/
def coordinates (V : Verifier gatesG2) (w : ℕ) :
    Basis (bodyWires V+w) ≃ V.BlockReg (indexQubits V) × Basis w :=
  (rawEquiv V w).trans (logicalEquiv V w)





















end QMAPerfectCompleteness.Main.BlockCoordinates


