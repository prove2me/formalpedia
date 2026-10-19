-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
-- name    : OAI_Probability_Subsphere_Regression_Spheres
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:54.660132+00:00
-- url     : https://prove2.me/theorems/bc3399f0-b07a-44ac-a9d0-361fbbd0f426
-- title:
--   Uniform law on the unit ball, probability normalization of spherical and Gaussian laws, and sphere isometries
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and its Lebesgue measure $\operatorname{vol}$, normalized so that the unit cube of an orthonormal basis has volume $1$. Let $B=\{x\in E:\|x\|<1\}$ and $\overline B=\{x\in E:\|x\|\le1\}$ be the open and closed unit balls and $S_E=\{x\in E:\|x\|=1\}$ the unit sphere. The surface measure of $U\subseteq S_E$ is $(\dim E)\cdot\operatorname{vol}\{ru:0<r<1,\ u\in U\}$, and the uniform law $\sigma_E$ on $S_E$ is the surface measure divided by its total mass.
--
--   1. **Uniform law on the unit ball.** The measure
--   $$\lambda_E=\operatorname{vol}(B)^{-1}\,\operatorname{vol}|_{\overline B},$$
--   together with the fact that $\lambda_E$ is a probability measure.
--   2. **Probability normalizations.** $\sigma_E$ is a probability measure whenever $E\neq\{0\}$, and so is its image $\iota_*\sigma_E$ on $E$ under the inclusion $\iota:S_E\to E$. The Gaussian sample law $N(0,I_d)^{\otimes T}$ on $(\mathbb{R}^d)^T$ is a probability measure for all $d,T\in\mathbb{N}$, and the uniform law on the unit sphere of $\mathbb{R}^d$ is a probability measure whenever $d\ge1$.
--   3. **Sphere isometries.** Every linear isometric isomorphism $e:E\to E$ restricts to a homeomorphism of the unit sphere, $S_E\to S_E$, $x\mapsto e(x)$.
--
--   Recording these normalizations once lets the spherical, ball and Gaussian laws of the model be used directly as probability measures, and the restricted isometries are used to transport the uniform spherical law along orthogonal maps such as reflections.
--
--   **Formalization Note** The definitions are `unitBallLaw` and `sphereIsometry e`; the facts in item 2 are the instances `unitBallLaw_probability`, `sphereLaw_probability` and `ambientSphereLaw_probability` (both under `[Nontrivial E]`), `sampleLaw_probability d T` and `uniformSphere_probability d` (under `[NeZero d]`). Here `sphereLaw` is `(σ univ)⁻¹ • σ` for `σ = volume.toSphere`, and `ambientSphereLaw` is its pushforward by `Subtype.val`. The normalization of `unitBallLaw` uses the volume of the open ball, which equals that of the closed ball.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Spheres.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance ambientSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (ambientSphereLaw (E := E)) := by
  unfold ambientSphereLaw
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def sphereIsometry (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖e x‖ = 1
    rw [e.norm_map])

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

end SubsphereRegression
end
end

end OAI


