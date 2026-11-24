-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:16.056931+00:00
-- url     : https://prove2.me/theorems/42f75c34-e74e-4780-a016-ca5f8e78f268
-- title:
--   Cls Gain A
-- statement:
--   Definitions and structural lemmas for Cls Gain A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
def EntAn (M : MC n → Matrix (Fin n) (Fin n) ℂ) (B₀ : MC n) : Prop := ∀ i j, AnalyticAt ℂ (fun B => M B i j) B₀
def hermL : E n →L[ℝ] MC n := LinearMap.toContinuousLinearMap
  { toFun := fun y => (herm y : MC n)
    map_add' := fun x y => by
      funext i j
      show herm (x + y) i j = herm x i j + herm y i j
      simp only [herm, Pi.add_apply]
      push_cast
      ring
    map_smul' := fun c x => by
      funext i j
      show herm (c • x) i j = c • herm x i j
      simp only [herm, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring }
end PositivityTheory.Rg.Sw.WR.Z


