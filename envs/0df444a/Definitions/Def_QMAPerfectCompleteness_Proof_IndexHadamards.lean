-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
-- name    : QMAPerfectCompleteness_Proof_IndexHadamards
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:54:16.414816+00:00
-- url     : https://prove2.me/theorems/81c1840d-c8fe-4eb2-bb80-071677b81260
-- title:
--   Paired Hadamards and index-bit coordinates
-- statement:
--   Defines the disjoint adjacent-pair Hadamard bank and the bit-value equivalence used to express it as the paper index-register Hadamard operator. Product and reindexing constructions connect physical bit assignments with matrix coordinates.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Sections 3.2–3.3, the binary clock and index-register operations. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/IndexHadamards.lean, retained declaration span lines 10–209.

/- Generated from Solutions.IndexHadamards by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Paired physical Hadamards and the little-endian index Hadamard matrix. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace QMAPerfectCompleteness.Main.IndexHadamards
open ReversibleGadgets ComparisonCircuits ClockCircuits

noncomputable abbrev piMatrix {J α : Type*} [Fintype J] (M : J → Matrix α α ℂ) :
    Matrix (J → α) (J → α) ℂ := fun y x => ∏ j, M j (y j) (x j)







/-- A family of copy matrices, with all flag wires untouched. -/

def pairEmbedding (r : ℕ) (j : Fin r) : Fin 2 ↪ Fin (r*2) :=
  ⟨fun i => finProdFinEquiv (j,i), fun i l h => (Prod.mk.inj (finProdFinEquiv.injective h)).2⟩

@[simp] lemma pairEmbedding_decode (r : ℕ) (j : Fin r) (i : Fin 2) :
    finProdFinEquiv.symm (pairEmbedding r j i) = (j,i) := by
  exact finProdFinEquiv.symm_apply_apply (j,i)

@[simp] lemma pairEmbedding_divNat (r : ℕ) (j : Fin r) (i : Fin 2) :
    (pairEmbedding r j i).divNat = j := congrArg Prod.fst (pairEmbedding_decode r j i)

@[simp] lemma pairEmbedding_modNat (r : ℕ) (j : Fin r) (i : Fin 2) :
    (pairEmbedding r j i).modNat = i := congrArg Prod.snd (pairEmbedding_decode r j i)

@[simp] lemma pairEmbedding_divModNat (r : ℕ) (w : Fin (r*2)) :
    pairEmbedding r w.divNat w.modNat = w := finProdFinEquiv.apply_symm_apply w

def pairEquiv (r : ℕ) : Basis (r*2) ≃ (Fin r → Basis 2) where
  toFun x j i := x (pairEmbedding r j i)
  invFun x w := x w.divNat w.modNat
  left_inv x := by funext w; simp
  right_inv x := by funext j i; simp

noncomputable def pairMatrix (r : ℕ) (M : Fin r → Matrix (Basis 2) (Basis 2) ℂ) :
    Matrix (Basis (r*2)) (Basis (r*2)) ℂ :=
  (piMatrix M).submatrix (pairEquiv r) (pairEquiv r)









noncomputable def pairProduct {r : ℕ} (js : List (Fin r)) (k : Fin r) :
    Matrix (Basis 2) (Basis 2) ℂ :=
  (js.reverse.map fun j => if k = j then hadamardTwoMatrix else 1).prod








def bitsEquiv (k : ℕ) : Basis k ≃ Fin (2^k) where
  toFun x := ⟨littleValue x,littleValue_lt_two_pow x⟩
  invFun j i := j.val.testBit i.val
  left_inv x := by funext i; exact littleValue_decode x i
  right_inv j := by
    apply Fin.ext
    exact (littleValue_testBit j.val k).trans (Nat.mod_eq_of_lt j.isLt)

noncomputable def bitFactor (y x : Bool) : ℂ :=
  (-1) ^ (if y && x then 1 else 0 : ℕ) / ((Real.sqrt 2 : ℝ) : ℂ)








/-- Physical targets of one pair of adjacent index bits. -/
def pairTargets {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin (k/2)) : Fin 2 ↪ Fin n :=
  (⟨fun i => ⟨2*j.val+i.val,by have := j.isLt; have := i.isLt; omega⟩,
    by intro a b h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; omega⟩ : Fin 2 ↪ Fin k).trans e

/-- One G₂ HH gate on each adjacent pair of the selected register. -/
noncomputable def pairedHadamards {k n : ℕ} (e : Fin k ↪ Fin n) : List (Instr gatesG2 n) :=
  (List.finRange (k/2)).map fun j => hhAt (pairTargets e j)

















end QMAPerfectCompleteness.Main.IndexHadamards


