-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:12:15.985667+00:00
-- url     : https://prove2.me/theorems/2247e56c-df1d-4057-a275-8c8367efab77
-- title:
--   Exterior Pairing Iota Two
-- statement:
--   Definitions and structural lemmas for Exterior Pairing Iota Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean

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
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
section Lin
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
abbrev i2 (a b : V) : ⋀[R]^2 V := exteriorPower.ιMulti R 2 ![a, b]
theorem up0 (a b c : V) : Function.update ![a, b] 0 c = ![c, b] := by
  ext i; fin_cases i <;> rfl
theorem up1 (a b c : V) : Function.update ![a, b] 1 c = ![a, c] := by
  ext i; fin_cases i <;> rfl
def b2 : V →ₗ[R] V →ₗ[R] ⋀[R]^2 V :=
  LinearMap.mk₂ R i2
    (fun a a' b ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_add ![a, b] 0 a a'
      rwa [up0, up0, up0] at this)
    (fun c a b ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_smul ![a, b] 0 c a
      rwa [up0, up0] at this)
    (fun a b b' ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_add ![a, b] 1 b b'
      rwa [up1, up1, up1] at this)
    (fun c a b ↦ by
      have := (exteriorPower.ιMulti R 2 (M := V)).map_update_smul ![a, b] 1 c b
      rwa [up1, up1] at this)
def pair2 (l u : V →ₗ[R] R) : ⋀[R]^2 V →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![l, u]))
end Lin
section Frame
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
def evT : C0 F ⊗[R] Glob1 F →ₗ[R] A0 F :=
  TensorProduct.lift (LinearMap.mk₂ R (fun g ω T ↦ g T • ω.1 T)
    (fun a b ω ↦ funext fun T ↦ by simp [add_smul])
    (fun r a ω ↦ funext fun T ↦ by simp)
    (fun a ω ω' ↦ funext fun T ↦ by simp)
    (fun r a ω ↦ funext fun T ↦ by simp [smul_comm r]))
end Frame
end GlobalTheory.CompanionTheory.Hodge.LiftO


