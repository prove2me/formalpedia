-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
-- name    : Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:08.774127+00:00
-- url     : https://prove2.me/theorems/be9dac5f-63c5-4a09-becd-7a192d245e39
-- title:
--   Qi Pts A
-- statement:
--   Definitions and structural lemmas for Qi Pts A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiPtsA.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
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
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR
namespace PositivityTheory.PrwZar.QiP
variable {R : Type} [CommRing R] {F : Type} [CommRing F] [Algebra R F]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}
def mulPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) : F →ₐ[R] S :=
  (hs.mul S φ φ').choose
def onePt (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : F →ₐ[R] S :=
  (hs.one S).choose
def powPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) : ℕ → (F →ₐ[R] S)
  | 0 => onePt hs S
  | n + 1 => mulPt hs (powPt hs φ n) φ
variable {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
end PositivityTheory.PrwZar.QiP


