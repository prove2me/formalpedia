-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentChartBaseChangeFormalGroup
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentChartBaseChangeFormalGroup
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:47.018526+00:00
-- url     : https://prove2.me/theorems/5153095a-d5aa-4437-8601-842331275726
-- title:
--   Nilpotent Chart Base Change Formal Group
-- statement:
--   Definitions and structural lemmas for Nilpotent Chart Base Change Formal Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NilpotentChartBaseChangeFormalGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
abbrev resAlg {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') (S : Type) [CommRing S]
    [Algebra R' S] : Algebra R S := ((algebraMap R' S).comp β).toAlgebra
def resHom {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') {S S' : Type} [CommRing S]
    [Algebra R' S] [CommRing S'] [Algebra R' S'] (φ : S →ₐ[R'] S') :
    @AlgHom R S S' _ _ _ (resAlg β S) (resAlg β S') :=
  letI := resAlg β S
  letI := resAlg β S'
  { φ.toRingHom with commutes' := fun r => φ.commutes (β r) }
end GlobalTheory.ChF


