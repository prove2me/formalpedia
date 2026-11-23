-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:45.398786+00:00
-- url     : https://prove2.me/theorems/1fd02a8b-7019-4d9a-a236-c27b302c5766
-- title:
--   Phi Rel Transport
-- statement:
--   Definitions and structural lemmas for Phi Rel Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
section Alg
variable {A B U : Type} [CommGroup A] [CommGroup B] [CommGroup U] {θ : B → B → B → U} {θ' : A → A → A → U}
  (β : A →* B) (Ω : A → U)
  (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a *
      Ω b * Ω c * (Ω 1)⁻¹ * θ' a b c)
include h
end Alg
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (hD : IsPullDeg φ D D') (hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (hΘ₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (hΘ₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
def liftB (ρ : T' ⟶ DegPre.BF D' F) : Over.mk (T'.hom ≫ spMap φ) ⟶ DegPre.BF D F :=
  Over.homMk (ρ.left ≫ Θ) (by
    show (ρ.left ≫ Θ) ≫ (DegPre.BF D F).hom = T'.hom ≫ spMap φ
    rw [← Over.w (fst (TF (R := R) F) D.P.A), Category.assoc, ← Category.assoc Θ, hΘ₁, ← hT, ← Over.w ρ,
      ← Over.w (fst (TF (R := R') F) D'.P.A)]
    simp only [Category.assoc])
end Pull
end PhiPull
end GlobalTheory


