-- Prove2me | solution 1 for AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8871b123-5a53-56b8-8ac9-4fb0957a5937

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

open NumberField
open MeasureTheory AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  show (∫ x, φ (g * t * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∫ x, φ (g * x) * f (t⁻¹ * x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  have h := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun x => φ (g * x) * f (t⁻¹ * x)) t
  simp only [inv_mul_cancel_left] at h
  simpa only [mul_assoc] using h

end S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
end P2MW
export P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply (solution)
