-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:12:48.466725+00:00
-- url     : https://prove2.me/theorems/1804c49f-f0e5-465c-9cf2-a854f9cb1b0f
-- title:
--   USt
-- statement:
--   Definitions and structural lemmas for USt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/USt.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory TensorProduct GlobalTheory.CatCoh
namespace GlobalTheory.CompanionTheory.Axis
def USt {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] (z : ∀ T : C, M ⊗[R] F.obj T),
    (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
    ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T)
def evZ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T T' : C} (φ : T ⟶ T') :
    Z1 F →ₗ[R] F.obj T' where
  toFun f := f.1 T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end GlobalTheory.CompanionTheory.Axis


