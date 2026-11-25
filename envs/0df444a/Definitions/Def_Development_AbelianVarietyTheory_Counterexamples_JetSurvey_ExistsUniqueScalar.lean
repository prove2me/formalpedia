-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniqueScalar
-- name    : Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniqueScalar
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:36.284873+00:00
-- url     : https://prove2.me/theorems/424873d8-b450-4cfa-a401-f6b35d84680e
-- title:
--   Exists Unique Scalar
-- statement:
--   Definitions and structural lemmas for Exists Unique Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniqueScalar.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_ToricData_isIota_pt
import Theorems.Thm_GlobalTheory_ToricData_isNsmul_pt
import Theorems.Thm_GlobalTheory_ToricData_toricPre_tate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.PhiPowerTest
open ToricData
abbrev qq : ℤ → (FractionRing InhTate.R)ˣ := fun n => piK ^ (n ^ 2)
def multData : DegData InhTate.R InhTate.I where
  toPre := toricPre InhTate.R ℤ qq
  psi_even := toricPre_tate ▸ tateData.psi_even
  tau_bimult := toricPre_tate ▸ tateData.tau_bimult
  psi_pos := toricPre_tate ▸ tateData.psi_pos
  psi_tendsto := toricPre_tate ▸ tateData.psi_tendsto
abbrev KK : Type := FractionRing InhTate.R
def halfPeriod : QkPt multData.toPre KK 2 :=
  ⟨(1 : ℤ), pt qq KK (zpowersHom _ piK), pt qq KK (zpowersHom _ piK ^ 2), (isNsmul_pt qq KK 2 _ _).2 rfl,
    (isIota_pt qq KK _ _).2 fun χ => by
      rw [polar_zpow_sq]
      change (((piK ^ χ) ^ 2 : KKˣ) : KK) = ((piK ^ (2 * 1 * χ) : KKˣ) : KK)
      rw [← zpow_natCast, ← zpow_mul, mul_one, mul_comm]
      rfl⟩
def normOne : LB.Gen (LB.LinComb multData.toPre.P.L (DegPre.lineφ multData.toPre KK halfPeriod.g.b) (DegPre.lineε 2)) :=
  cg _ _ (Geo.Tor.unitOn (1 : KKˣ))
end GlobalTheory.PhiPowerTest


