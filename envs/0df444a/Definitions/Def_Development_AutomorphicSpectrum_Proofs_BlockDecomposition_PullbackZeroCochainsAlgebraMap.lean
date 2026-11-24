-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:00.267282+00:00
-- url     : https://prove2.me/theorems/aefcbe47-cace-4624-80dd-541d8af897b4
-- title:
--   Pullback Zero Cochains Algebra Map
-- statement:
--   Definitions and structural lemmas for Pullback Zero Cochains Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul

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
namespace GlobalTheory.CompanionTheory.HodgeLow
section
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}
def pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') : C0 F →ₗ[R] C0 F' where
  toFun g T := m.α T (g (m.G.obj T))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ m.smul _ _ _
def pullbackOneCochains (m : CoefMap (RingHom.id R) F F') : C1 F →ₗ[R] C1 F' where
  toFun f T T' φ := m.α T' (f _ _ (m.G.map φ))
  map_add' _ _ := by funext T T' φ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' φ; exact m.smul _ _ _
def pullbackTwoCochains (m : CoefMap (RingHom.id R) F F') : C2 F →ₗ[R] C2 F' where
  toFun z T T' T'' φ ψ := m.α T'' (z _ _ _ (m.G.map φ) (m.G.map ψ))
  map_add' _ _ := by funext T T' T'' φ ψ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' T'' φ ψ; exact m.smul _ _ _
end
end GlobalTheory.CompanionTheory.HodgeLow


