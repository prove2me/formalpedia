-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurve
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:39.712567+00:00
-- url     : https://prove2.me/theorems/7b33d740-fbdc-4303-ac47-5b4c0940ec0c
-- title:
--   PLCurve
-- statement:
--   Definitions and structural lemmas for PLCurve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurve.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
def PLCurveLocalStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X)
    (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X),
    Function.Injective p → IsPotential A L → IsSection A L s → IsSNC A L s m (fun k => {p k}) →
    ∀ (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)), IsCompatChart A ψ →
    ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ.source →
      mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v
namespace PLC
variable {X : Type} [TopologicalSpace X]
end PLC
end
end ReciprocityTheory.AnForm.M


