-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:12.723607+00:00
-- url     : https://prove2.me/theorems/1be2cedd-febe-4cf7-98e9-6c7dbec33a73
-- title:
--   Exists Gen T
-- statement:
--   Definitions and structural lemmas for Exists Gen T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.UU.IntGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
def basePts (T : Over (Spec (CommRingCat.of R))) (α mu : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(cP D T α * cP D T mu).left, (cP D T α).left, (cP D T mu).left, (1 : T ⟶ D.P.A).left]
def baseExp (k : ℕ) : Fin 4 → ℤ := ![-1, 1, 1 - k, k - 1]
def multK (k : ℕ) (mu α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
    (GeneratorPullback.powGen D.P.L _ _ D.rigK k)
end GlobalTheory.UU.IntGen


