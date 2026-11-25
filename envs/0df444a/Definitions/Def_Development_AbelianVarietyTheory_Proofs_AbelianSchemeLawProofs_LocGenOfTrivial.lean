-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:14.532854+00:00
-- url     : https://prove2.me/theorems/90c655bd-5025-4320-8b1b-d6d4879e4b7e
-- title:
--   Loc Gen Of Trivial
-- statement:
--   Definitions and structural lemmas for Loc Gen Of Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KerPow
section General
variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
def HasGen (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen
theorem HasGen.pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : HasGen L φ ε) (h : Y' ⟶ Y) {φ' : K → (Y' ⟶ X)}
    (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.pullGen_isGen L φ ε t ht h⟩
def LocGen (L : LB X) (π : Y ⟶ B) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ HasGen L (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε
end General
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
end GlobalTheory.KerPow
namespace GlobalTheory
end GlobalTheory


