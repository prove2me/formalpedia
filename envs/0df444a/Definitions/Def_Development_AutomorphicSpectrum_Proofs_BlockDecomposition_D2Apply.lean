-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:06.635426+00:00
-- url     : https://prove2.me/theorems/0fe1fce4-064b-4796-b54b-4e9512b6f887
-- title:
--   D2 Apply
-- statement:
--   Definitions and structural lemmas for D2 Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.PerfExt
section Gen
variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
def Ext {N Q : Type} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R' Q] (c : N → Q) : Prop :=
  ∃ e : R' ⊗[R] N ≃ₗ[R'] Q, ∀ b, e (1 ⊗ₜ b) = c b
variable {R R'}
variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]
variable (M) in

def tw (E : R' ⊗[R] N ≃ₗ[R'] Q) : M ⊗[R] N ≃+ M ⊗[R'] Q :=
  ((AlgebraTensorModule.cancelBaseChange R R' R' M N).symm.trans (LinearEquiv.lTensor M E)).toAddEquiv
end Gen
section Main
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]
end Main
end GlobalTheory.CompanionTheory.PerfExt


