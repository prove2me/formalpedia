-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
-- name    : QMAPerfectCompleteness_Proof_BlockProgramPlacement
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:35.927089+00:00
-- url     : https://prove2.me/theorems/77ee3ef4-d4f4-474e-bcb3-5dd301407764
-- title:
--   Placement of clean programs in larger registers
-- statement:
--   Places a clean classical program on any injective selection of physical wires. The selected wires undergo the original deterministic basis action, complementary wires remain spectators, and the cleanliness invariant is pulled back along the wire injection without changing the literal gate count.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockProgramPlacement.lean, lines 8–38.

/- Generated from Solutions.BlockProgramPlacement by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
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



/-! Clean basis-action programs lift to larger physical registers without changing gate counts. -/
open Matrix
namespace QMAPerfectCompleteness.Main.BlockCompiler.CleanProgram
open ReversibleGadgets

lemma placePermutation_selected {r n : ℕ} (e : Fin r ↪ Fin n) (f : Basis r → Basis r)
    (x : Basis n) : (placePermutation e f x) ∘ e = f (x ∘ e) := by
  exact congrArg Prod.fst ((CircuitProof.splitTargets e).apply_symm_apply
    (f (x ∘ e),(CircuitProof.splitTargets e x).2))

lemma placePermutation_eq_iff {r n : ℕ} (e : Fin r ↪ Fin n) (f : Basis r → Basis r)
    (y x : Basis n) :
    y = placePermutation e f x ↔ y ∘ e = f (x ∘ e) ∧
      (∀ w, (∀ i, e i ≠ w) → y w = x w) := by
  rw [← (CircuitProof.splitTargets e).apply_eq_iff_eq]
  simp only [placePermutation,Equiv.apply_symm_apply,Prod.ext_iff,CircuitProof.splitTargets_fst]
  rw [CircuitProof.unaffected_iff e x y]

/-- Address every literal instruction through e; all complementary physical wires are spectators. -/
noncomputable def mapWires {r n : ℕ} {Clean : Basis r → Prop}
    (P : CleanProgram r Clean) (e : Fin r ↪ Fin n) :
    CleanProgram n (fun x => Clean (x ∘ e)) where
  gates := P.gates.map (Instr.mapWires e)
  action := placePermutation e P.action
  sound y x hx := by
    classical
    rw [circuitMatrix_mapWires,placeMatrix_apply,P.sound _ _ hx]
    have he := placePermutation_eq_iff e P.action y x
    by_cases ho : ∀ w, (∀ i, e i ≠ w) → y w = x w
    · by_cases hs : y ∘ e = P.action (x ∘ e)
      · rw [if_pos ho,if_pos hs,if_pos (he.mpr ⟨hs,ho⟩)]
      · rw [if_pos ho,if_neg hs,if_neg (fun h => hs (he.mp h).1)]
    · rw [if_neg ho,if_neg (fun h => ho (he.mp h).2)]
  preserves x hx := by
    rw [placePermutation_selected]
    exact P.preserves _ hx



end QMAPerfectCompleteness.Main.BlockCompiler.CleanProgram


