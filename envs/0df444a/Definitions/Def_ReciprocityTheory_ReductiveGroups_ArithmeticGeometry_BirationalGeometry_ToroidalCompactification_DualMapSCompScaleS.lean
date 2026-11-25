-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:52:55.19723+00:00
-- url     : https://prove2.me/theorems/1a7fe537-106b-4ce0-923e-68a7f1501202
-- title:
--   Dual Map SComp Scale S
-- statement:
--   Definitions and structural lemmas for Dual Map SComp Scale S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
section Wrap
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
end Wrap
section Scale
variable {S : Type} [CommRing S]
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
end Scale
section Over
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
abbrev Qv (s t : S) : Type := Localization.Away (algebraMap S (Localization.Away s) t)
abbrev qL (s t : S) : Localization.Away s →ₐ[S] Qv s t := IsScalarTower.toAlgHom S _ _
theorem isUnit_qv (s t : S) : IsUnit (algebraMap S (Qv s t) t) := by
  rw [IsScalarTower.algebraMap_apply S (Localization.Away s) (Qv s t)]
  exact IsLocalization.Away.algebraMap_isUnit _
def qR (s t : S) : Localization.Away t →ₐ[S] Qv s t :=
  { IsLocalization.Away.lift t (isUnit_qv s t) with
    commutes' := fun r => IsLocalization.Away.lift_eq t (isUnit_qv s t) r }
end Over
end ReciprocityTheory.ChartRestriction.G.Chart


