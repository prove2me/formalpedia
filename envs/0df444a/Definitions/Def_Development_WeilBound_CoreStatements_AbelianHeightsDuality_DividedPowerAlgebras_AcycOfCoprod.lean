-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
-- name    : Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:24.569809+00:00
-- url     : https://prove2.me/theorems/63e32d59-6fa6-4339-91e6-bcc757206914
-- title:
--   Acyc Of Coprod
-- statement:
--   Definitions and structural lemmas for Acyc Of Coprod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DividedPowerAlgebras/AcycOfCoprod.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
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
open CategoryTheory GlobalTheory.CatCoh
namespace FubiniStudyChowHeightFormula₂.Adr
universe v u v' u'
def Acyc (R : Type) [CommRing R] (D : Type u) [Category.{v} D] : Prop :=
  Nonempty D ∧ ∀ M : CommAlgCat.{0} R, (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a b, g a = g b) ∧
    (∀ c : H1 ((Functor.const D).obj M), c = 0) ∧ ∀ c : H2 ((Functor.const D).obj M), c = 0
section Contract
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]
def cm (M : CommAlgCat.{0} R) (G : D ⥤ D) :
    CoefMap (RingHom.id R) ((Functor.const D).obj M) ((Functor.const D).obj M) where
  G := G
  α _ := RingHom.id M
  naturality _ _ := rfl
  smul _ _ _ := rfl
end Contract
section Comma
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {G : C' ⥤ C} {T : C}
end Comma
section QA
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
end QA
end FubiniStudyChowHeightFormula₂.Adr


