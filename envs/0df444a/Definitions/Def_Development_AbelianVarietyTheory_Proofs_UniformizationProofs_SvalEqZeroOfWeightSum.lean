-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:55:16.506671+00:00
-- url     : https://prove2.me/theorems/683f113f-df67-4131-abe6-5c796646c92c
-- title:
--   Sval Eq Zero Of Weight Sum
-- statement:
--   Definitions and structural lemmas for Sval Eq Zero Of Weight Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfWeightSum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat

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
noncomputable section
namespace GlobalTheory.ExpUniq
section Values
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
def diffSec {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]
end Values
section Level
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {Y : Scheme.{0}} (p : Y ⟶ D.P.A.left) {K : Type} [Fintype K] {ε : K → ℤ}
end Level
section Expansion
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {σ σ' : U.SecGT T k} {f f' : ∀ α, SecBT D T k α}
end Expansion
end GlobalTheory.ExpUniq
namespace GlobalTheory
end GlobalTheory


