-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:00.116554+00:00
-- url     : https://prove2.me/theorems/b6d7b9ab-f12b-48d0-af05-143ab706013b
-- title:
--   Uni Mat Block Triangular
-- statement:
--   Definitions and structural lemmas for Uni Mat Block Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UniMatBlockTriangular.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
namespace GlobalTheory.FlagPts
def AffPts (k J : Type) : Type := J → k
instance instTopAffPts (k J : Type) [Field k] : TopologicalSpace (AffPts k J) :=
  .generateFrom {s | ∃ p : MvPolynomial J k, s = {x | MvPolynomial.eval x p ≠ 0}}
instance (k J : Type) [Field k] : Zero (AffPts k J) := ⟨fun _ => 0⟩
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def CellIdx : Type := Σ i : ι, {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1}
instance [Fintype ι] : Fintype (CellIdx k V) := by
  unfold CellIdx
  infer_instance
variable {k V}
def uniMat (u : AffPts k (CellIdx k V)) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun a c => if a = c then 1 else if h : c < a then u ⟨i, (a, c), h⟩ else 0
theorem uniMat_apply_self (u : AffPts k (CellIdx k V)) (i : ι) (a : Fin (finrank k (V i))) : uniMat u i a a = 1 := by
  simp [uniMat]
theorem uniMat_apply_of_gt (u : AffPts k (CellIdx k V)) (i : ι) {a c : Fin (finrank k (V i))} (h : a < c) :
    uniMat u i a c = 0 := by
  simp [uniMat, h.ne, not_lt.2 h.le]
theorem uniMat_blockTriangular (u : AffPts k (CellIdx k V)) (i : ι) : (uniMat u i).BlockTriangular OrderDual.toDual :=
  fun a c h => uniMat_apply_of_gt u i (by simpa using h)
theorem det_uniMat (u : AffPts k (CellIdx k V)) (i : ι) : (uniMat u i).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (uniMat_blockTriangular u i)]
  simp [uniMat_apply_self]
def cellFrame (b : Frames k V) (u : AffPts k (CellIdx k V)) : Frames k V := fun i =>
  (b i).map (Matrix.toLinearEquiv (b i) (uniMat u i) (by rw [det_uniMat]; exact isUnit_one))
def cellMap (b : Frames k V) (u : AffPts k (CellIdx k V)) : Flags k V := (cellFrame b u).flags
end GlobalTheory.FlagPts


