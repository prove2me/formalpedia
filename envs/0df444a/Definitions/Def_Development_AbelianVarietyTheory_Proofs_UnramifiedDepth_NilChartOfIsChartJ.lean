-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilChartOfIsChartJ
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilChartOfIsChartJ
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T18:01:38.088673+00:00
-- url     : https://prove2.me/theorems/f29bf1bc-88b1-557d-b0ff-047b5c6dc04b
-- title:
--   Nil Chart Of Is Chart J
-- statement:
--   Definitions and structural lemmas for Nil Chart Of Is Chart J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NilChartOfIsChartJ.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
section Jets
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.ChartBaseChange GlobalTheory.ChartUniv
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} {κ : Type}
variable [GrpObj G]
variable [IsLocalRing R] [Smooth G.hom] {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
  (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
  (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
    ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
  {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (q : A →ₐ[R] B)
  (hJ : (RingHom.ker q) ^ (m + 1) = ⊥)
end Jets
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
end GlobalTheory.ChF


