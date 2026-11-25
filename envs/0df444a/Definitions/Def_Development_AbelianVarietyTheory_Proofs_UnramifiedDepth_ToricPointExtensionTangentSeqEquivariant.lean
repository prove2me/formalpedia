-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionTangentSeqEquivariant
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionTangentSeqEquivariant
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:54.752901+00:00
-- url     : https://prove2.me/theorems/feef4ec1-7be7-4ee1-81c1-90716dca382d
-- title:
--   Toric Point Extension Tangent Seq Equivariant
-- statement:
--   Definitions and structural lemmas for Toric Point Extension Tangent Seq Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ToricPointExtensionTangentSeqEquivariant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
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
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
def tv {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (e : S) {n : ℕ} (v : Fin n → R) :
    Fin n → S := fun i => algebraMap R S (v i) * e
def chi {R S X : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup X] {e : S}
    (he : e * e = 0) (L : X →+ R) : Multiplicative X →* Sˣ :=
  MonoidHom.toHomUnits
    { toFun := fun y => 1 + algebraMap R S (L y.toAdd) * e
      map_one' := by simp
      map_mul' := fun y z => by
        simp only [toAdd_mul, map_add]
        linear_combination (-(algebraMap R S (L y.toAdd) * algebraMap R S (L z.toAdd))) * he }
end GlobalTheory.ChF


