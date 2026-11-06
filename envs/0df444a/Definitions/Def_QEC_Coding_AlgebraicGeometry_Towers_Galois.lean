-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
-- name    : QEC_Coding_AlgebraicGeometry_Towers_Galois
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:51:29.170894+00:00
-- url     : https://prove2.me/theorems/e1b7f7a7-21ee-4c8a-99e9-341f9d5b84f6
-- title:
--   Galois
-- statement:
--   Definitions and structural lemmas for Galois, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Galois.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Translation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Mathlib.FieldTheory.Galois.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepField_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepTranslation_apply_auxiliaryCoordinate

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem stepTranslation_injective
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Function.Injective (stepTranslation P x hx) := by
  intro c d hcd
  have haux := congrArg
    (fun e : StepField P x hx ≃ₐ[K] StepField P x hx =>
      e (stepAuxiliaryCoordinate P x hx)) hcd
  change stepTranslation P x hx c (stepAuxiliaryCoordinate P x hx) =
    stepTranslation P x hx d (stepAuxiliaryCoordinate P x hx) at haux
  rw [stepTranslation_apply_auxiliaryCoordinate,
    stepTranslation_apply_auxiliaryCoordinate] at haux
  have hconstants :
      algebraMap F256 (StepField P x hx) (c : F256) =
        algebraMap F256 (StepField P x hx) (d : F256) :=
    add_left_cancel haux
  apply Subtype.ext
  exact (algebraMap F256 (StepField P x hx)).injective hconstants
theorem stepField_algEquiv_card
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Nat.card (StepField P x hx ≃ₐ[K] StepField P x hx) = 16 := by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (StepField P x hx ≃ₐ[K] StepField P x hx) ≤
          Module.finrank K (StepField P x hx) := AlgEquiv.card_le
      _ = 16 := stepField_finrank P x hx
  · calc
      16 = Nat.card (LinearMap.ker f256ArtinSchreier) := by
        rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
      _ ≤ Nat.card (StepField P x hx ≃ₐ[K] StepField P x hx) :=
        Nat.card_le_card_of_injective (stepTranslation P x hx)
          (stepTranslation_injective P x hx)
noncomputable instance stepField_isGalois
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsGalois K (StepField P x hx) := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [stepField_algEquiv_card, stepField_finrank]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


