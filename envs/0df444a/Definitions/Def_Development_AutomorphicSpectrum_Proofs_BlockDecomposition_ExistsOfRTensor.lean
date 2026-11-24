-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:22.797829+00:00
-- url     : https://prove2.me/theorems/584401de-eda0-4934-8237-770bb17e5d1c
-- title:
--   Exists Of RTensor
-- statement:
--   Definitions and structural lemmas for Exists Of RTensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
namespace GlobalTheory.CompanionTheory.HodgeAlt
section Basic
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
end Basic
section Lin
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']
def alt (l l' : V →ₗ[R] R) : ⋀[R]^2 V →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![l, l']))
end Lin
section Wedge
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
def wd : V →ₗ[R] V →ₗ[R] ⋀[R]^2 V :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
end Wedge
section Main
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
end Main
section Final
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
end Final
end GlobalTheory.CompanionTheory.HodgeAlt


