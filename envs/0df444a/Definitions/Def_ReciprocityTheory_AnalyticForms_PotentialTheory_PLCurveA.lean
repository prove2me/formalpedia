-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:19.26626+00:00
-- url     : https://prove2.me/theorems/c96fde79-73bd-4908-a90b-df1125df7c8e
-- title:
--   PLCurve A
-- statement:
--   Definitions and structural lemmas for PLCurve A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace PLC
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def plDefect (A : FinHolAtlas 1 X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (p : Fin r → X) (f : X → ℝ) : ℝ :=
  mInt A ![LocPot.ofFun f] (logNormSec L s) - (∑ k, (m k : ℝ) * f (p k) - mInt A ![L] f)
end PLC
end
end ReciprocityTheory.AnForm.M


