-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:04.038862+00:00
-- url     : https://prove2.me/theorems/11d0600a-51c7-4fea-8b7c-49d1d58a14dc
-- title:
--   Is Raw Chart Base Change Jet Points
-- statement:
--   Definitions and structural lemmas for Is Raw Chart Base Change Jet Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl
theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
section Maps
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]
    first | done | rfl)
def dualPtMap : overAt (spMap ψ ≫ x0) (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_alg])
end Maps
end GlobalTheory.RawChartBC


