-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsAbelianTorusGeneratorsAtPlace
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsAbelianTorusGeneratorsAtPlace
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:42.372744+00:00
-- url     : https://prove2.me/theorems/5ef6d356-07ac-401d-b904-aa7856d1ed4b
-- title:
--   Exists Abelian Torus Generators At Place
-- statement:
--   Definitions and structural lemmas for Exists Abelian Torus Generators At Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsAbelianTorusGeneratorsAtPlace.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenspaceDimAddSplitExactTransposeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EmbeddingsLiftIntegersIdempotentsConjugationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenbasisRestrictionSurjectiveEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateModuleEigenspaceDimEqLieAlgebraSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicPlaceBasisOfIdempotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFreeGeneratorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicIntAlgebraOfIsAdicCompleteMatrixUniqueStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF.GenAtPlace
noncomputable def extM (p : ℕ) [Fact p.Prime] {O OE κ : Type} [CommRing O] [Algebra ℤ_[p] O] [CommRing OE]
    [Fintype κ] [DecidableEq κ] (ρ : OE →+* Matrix κ κ O) : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] _) ρ.toIntAlgHom (fun c _ => Algebra.commutes c _)
def trR {O OE κ : Type} [CommRing O] [CommRing OE]
    [Fintype κ] [DecidableEq κ] (ρ : OE →+* Matrix κ κ O) : OE →+* Matrix κ κ O where
  toFun a := (ρ a)ᵀ
  map_one' := by simp
  map_mul' a b := by rw [mul_comm a b, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp [Matrix.transpose_add]
end GlobalTheory.ChF.GenAtPlace


