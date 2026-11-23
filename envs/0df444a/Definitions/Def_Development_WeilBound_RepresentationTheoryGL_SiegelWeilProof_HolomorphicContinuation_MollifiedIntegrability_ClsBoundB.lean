-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:22.351253+00:00
-- url     : https://prove2.me/theorems/9a5d4acc-5c11-4dfb-954e-6fc6552640bd
-- title:
--   Cls Bound B
-- statement:
--   Definitions and structural lemmas for Cls Bound B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
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
namespace PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
theorem herm_add (x y : E n) : herm (x + y) = herm x + herm y := by
  ext i j
  simp only [herm, Pi.add_apply, Matrix.add_apply]
  push_cast; ring
theorem herm_smul (c : ℝ) (x : E n) : herm (c • x) = (c : ℂ) • herm x := by
  ext i j
  simp only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  push_cast; ring
def hermE (a b : Fin n) : E n →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => herm y a b
      map_add' := fun x y => by rw [herm_add]; rfl
      map_smul' := fun c x => by rw [herm_smul]; simp [Matrix.smul_apply, Complex.real_smul] }
end PositivityTheory.Rg.Sw.WR.B


