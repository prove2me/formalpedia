-- Prove2me | Definitions.Def_OAIQ240Bp016
-- name    : OAIQ240Bp016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:33:54.994195+00:00
-- url     : https://prove2.me/theorems/21167318-84b2-47a8-a804-bb11b7b5800a
-- title:
--   Definitions bundle OAIQ240Bp016 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 theorem. The definitions and types are `OAI.PackingSufficiencySupport.CubicModel.recovery`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Fredholm_NonlinearReduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/NonlinearReduction.lean), [`BallPacking_Surfaces_QuadricAnnulusDomain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Surfaces/QuadricAnnulusDomain.lean).
--
--   **Imports.** It imports the bundle `OAIQ240Bp012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp019`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp012

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrK
local instance pfrC_r12f50d_1 : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrX
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrY
include hD in
lemma parametric_zero_is_solution (hz : F (t,x)=0) :
    ∀ᶠ v in 𝓝 (t,x),F v=0 →
      parametricSolution pkg hF hD (v.1,((domCoords pkg) v.2).2)=v.2 := by
  have hh := (parametricEssential_smooth pkg hF).contDiffAt.eventually_apply_eq_iff_implicitFunction
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (parametricEssential_invertible pkg hF hD)
  have hm : Continuous (fun v : ℝ × X => parametricBase pkg v.1 v.2) := by
    exact (continuous_fst.prodMk ((domCoords pkg).continuous.comp continuous_snd).snd).prodMk
      ((domCoords pkg).continuous.comp continuous_snd).fst
  have hb : parametricEssential pkg F (parametricBase pkg t x)=0 := by
    change ((codCoords pkg) (F (t,(domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)))).1=0
    rw [(domCoords pkg).symm_apply_apply,hz,map_zero]; rfl
  filter_upwards [(hm.tendsto (t,x)).eventually hh] with v hv hv0
  have he : parametricEssential pkg F (parametricBase pkg v.1 v.2)=0 := by
    change ((codCoords pkg) (F (v.1,(domCoords pkg).symm (((domCoords pkg) v.2).1,((domCoords pkg) v.2).2)))).1=0
    rw [(domCoords pkg).symm_apply_apply,hv0,map_zero]; rfl
  have hu := hv.mp (he.trans hb.symm)
  change parametricInfiniteSolution pkg hF hD (v.1,((domCoords pkg) v.2).2)=((domCoords pkg) v.2).1 at hu
  rw [parametricSolution,hu]
  exact (domCoords pkg).symm_apply_apply v.2

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

 def recovery (z : PlaneBase) : Affine 2 :=
  let t := -(z.1^2+1)/(2*z.1)
  (t,![t+z.1,t+z.2])

end PackingSufficiencySupport.CubicModel
end

end OAI
end


