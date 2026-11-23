-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:51.518163+00:00
-- url     : https://prove2.me/theorems/a704938d-34b2-4dc4-8424-7e43cc6fdeaf
-- title:
--   Base Ideal Ideal
-- statement:
--   Definitions and structural lemmas for Base Ideal Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BaseIdealIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AbLaw
namespace GlobalTheory.FormalAlg
variable {R : Type} [CommRing R] {W : Scheme.{0}}
def baseIdeal (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) : W.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (cst f ⊤))
def IsSystem (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (t : ℕ → W.IdealSheafData) : Prop :=
  ∀ e, t e = t (e + 1) ⊔ baseIdeal f (I ^ (e + 1))
def Reduces (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (T : W.IdealSheafData)
    (t : ℕ → W.IdealSheafData) : Prop :=
  ∀ e, T ⊔ baseIdeal f (I ^ (e + 1)) = t e
def Alg (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Prop :=
  ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T t
end GlobalTheory.FormalAlg


