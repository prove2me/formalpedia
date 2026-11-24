-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:47.934313+00:00
-- url     : https://prove2.me/theorems/6ff70767-6c1c-42c4-898a-27032b8e96d7
-- title:
--   To Matrix Mul Vec
-- statement:
--   Definitions and structural lemmas for To Matrix Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier
attribute [local simp] GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul


set_option autoImplicit false
noncomputable section
open Matrix
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ}
abbrev Wd (e : Matrix (Fin N) (Fin N) k) : Submodule k (Fin N → k) := LinearMap.range e.mulVecLin
lemma W_stable {e a : Matrix (Fin N) (Fin N) k} (hc : a * e = e * a) {w : Fin N → k} (hw : w ∈ Wd e) :
    a *ᵥ w ∈ Wd e := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨a *ᵥ v, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hc]⟩
variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
def rho (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) : A →ₐ[k] Module.End k (Wd e) where
  toFun a := (a.1.mulVecLin).restrict (fun w hw => W_stable (hA _ a.2 _ he) hw)
  map_one' := by ext w; simp
  map_mul' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 * b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (b.1 *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec]
  map_zero' := by ext w; simp
  map_add' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 + b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (w : Fin N → k) + b.1 *ᵥ (w : Fin N → k)
    rw [Matrix.add_mulVec]
  commutes' r := by ext w; simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
abbrev Pe (e : Matrix (Fin N) (Fin N) k) : (Fin N → k) →ₗ[k] Wd e := LinearMap.rangeRestrict e.mulVecLin
end PositivityTheory.RgUd.TP.Desc.Piece.PDich


