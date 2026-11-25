-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:40.721748+00:00
-- url     : https://prove2.me/theorems/3f24a0f3-0bfd-43f4-8419-2e5388be8339
-- title:
--   Exists Descend Through
-- statement:
--   Definitions and structural lemmas for Exists Descend Through, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.PackageDescent
section Descent
variable {X X' Y Y' Z : Scheme.{0}} {K : Type} [Fintype K]
end Descent
section Action
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}
end Action
section Package
variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]
variable [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] [IsMonHom q] [QuasiCompact q.left]
def isoV {L : LB G.left} {M : LB B.left} (w : LB.Iso L (M.pull q.left)) {T : Over S} (z : T.left)
    (I : (T.left ⟶ B.left) → M.ι) (J : (T.left ⟶ G.left) → L.ι) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  gw w x.left z (I (x.left ≫ q.left)) (J x.left)
def diff₃ {A U : Type} [CommGroup A] [CommGroup U] (W : A → U) (a b d : A) : U :=
  W (a * b * d) * (W (a * b))⁻¹ * (W (a * d))⁻¹ * (W (b * d))⁻¹ * W a * W b * W d * (W 1)⁻¹
end Package
end GlobalTheory.UU.PackageDescent
namespace GlobalTheory.UU
open PackageDescent
end GlobalTheory.UU
end


