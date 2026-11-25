-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionCurvatureSumWedgeSemilinearPullback
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionCurvatureSumWedgeSemilinearPullback
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:41:31.5131+00:00
-- url     : https://prove2.me/theorems/b85c6db1-4666-4641-b0dd-5189ea53c935
-- title:
--   Connection Curvature Sum Wedge Semilinear Pullback
-- statement:
--   Definitions and structural lemmas for Connection Curvature Sum Wedge Semilinear Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionCurvatureSumWedgeSemilinearPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh
section Helpers
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type} [Category.{0} C] [Category.{0} C']
end Helpers
end GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


