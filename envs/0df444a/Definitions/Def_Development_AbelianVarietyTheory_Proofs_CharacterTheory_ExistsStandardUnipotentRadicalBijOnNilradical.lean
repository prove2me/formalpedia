-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradical
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:35.066143+00:00
-- url     : https://prove2.me/theorems/6354df34-ffee-4574-b1d8-d5cb1f247191
-- title:
--   Exists Standard Unipotent Radical Bij On Nilradical
-- statement:
--   Definitions and structural lemmas for Exists Standard Unipotent Radical Bij On Nilradical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsStandardUnipotentRadicalBijOnNilradical.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL.UnipNilRad
variable {F : Type} [Field F]
def lowSub (F : Type) [Field F] (d a : ℕ) : Submodule F (Fin d → F) :=
  LinearMap.ker (LinearMap.funLeft F F (Subtype.val : {i : Fin d // a ≤ i.val} → Fin d))
def unip {d : ℕ} (A : Submodule F (Fin d → F)) : Subgroup (GL (Fin d) F) where
  carrier := {u | Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈ nilRad A}
  one_mem' := by
    refine ⟨fun x => ?_, fun x _ => ?_⟩ <;> simp
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := A.add_mem (hu1 (Matrix.toLin' (v : Matrix (Fin d) (Fin d) F) x)) (hv1 x)
      simpa [Matrix.toLin'_mul] using this
    · have h1 := hu2 x hx
      have h2 := hv2 x hx
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1 h2 ⊢
      rw [Units.val_mul, Matrix.toLin'_mul, LinearMap.comp_apply, h2, h1]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have e1 : ∀ x, Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)
        (Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) x) = x := fun x => by
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    have e2 : ∀ x, Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) x) = x := fun x => by
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := A.neg_mem (hu1 (Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) x))
      rw [LinearMap.sub_apply, e1, neg_sub] at this
      exact this
    · have h1 := hu2 x hx
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1 ⊢
      conv_lhs => rw [← h1]
      exact e2 x
end GlobalTheory.CuspGL.UnipNilRad


