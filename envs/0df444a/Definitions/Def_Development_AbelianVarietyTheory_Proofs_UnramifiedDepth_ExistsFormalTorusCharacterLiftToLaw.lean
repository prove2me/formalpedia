-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalTorusCharacterLiftToLaw
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalTorusCharacterLiftToLaw
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:11.306315+00:00
-- url     : https://prove2.me/theorems/b7f33d8a-7c36-426e-9b5a-2b92407261fa
-- title:
--   Exists Formal Torus Character Lift To Law
-- statement:
--   Definitions and structural lemmas for Exists Formal Torus Character Lift To Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalTorusCharacterLiftToLaw.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalSeriesJacobianChainRuleLinearPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIsChOfTorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MultiplicativeFormalGroupLawPowerPTorsionFiniteFStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GmLawCharsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsAddUnitOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsAddCommMonoidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupSeriesSeparatedByTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubSurjectiveOfLinLeftInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF.Lift
section Subst
variable {R : Type} [CommRing R] {m n d e : ℕ}
theorem hasSub (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)
noncomputable def subA (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS R m d →ₐ[R] PS R n e :=
  MvPowerSeries.substAlgHom (hasSub a ha)
theorem const_one (φ : Fin d → PS R n e) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → Fin d → PS R n e) i j) = 0 := by
  intro i j
  fin_cases i
  exact hφ j
end Subst
end GlobalTheory.ChF.Lift


