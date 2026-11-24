-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:54:45.255447+00:00
-- url     : https://prove2.me/theorems/4779267b-d278-4d8d-a70a-f5f88bf03716
-- title:
--   Model Der
-- statement:
--   Definitions and structural lemmas for Model Der, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelDer.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end ExpL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical in

def kcurve (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ → KG ε :=
  if h : inK ε X then Classical.choose (exists_curve ε h) else fun _ => 1
section Op
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
def derOp (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V)) (X : Matrix (Fin n) (Fin n) ℂ) : V →L[ℂ] V :=
  deriv (fun t : ℝ => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) 0
end Op
def rdc (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : KG ε → ℂ) (x : KG ε) : ℂ :=
  deriv (fun t : ℝ => f (x * kcurve ε (cpart1 ε (bdPart ε Z)) t)) 0 +
    Complex.I * deriv (fun t : ℝ => f (x * kcurve ε (cpart2 ε (bdPart ε Z)) t)) 0
end ReciprocityTheory.ChartRestriction.DS.HW


