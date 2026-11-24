-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:04.138024+00:00
-- url     : https://prove2.me/theorems/3e60872b-18a9-44b9-85fa-cf3698bfb628
-- title:
--   St Hess CComp Pluri
-- statement:
--   Definitions and structural lemmas for St Hess CComp Pluri, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHessCCompPluri.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
def HessCCompPluri.Statement : Prop :=
  ∀ (D : ℕ) (F : ℝ → ℝ) (L : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ),
    ContDiffAt ℝ 2 F (L z) → ContDiffAt ℝ 2 L z → hessC L z = 0 →
      hessC (fun w => F (L w)) z = ((deriv (deriv F) (L z) : ℝ) : ℂ) • hessC (fun w => L w ^ 2 / 2) z
end
end GroundTheory.Heights₂.Heights


