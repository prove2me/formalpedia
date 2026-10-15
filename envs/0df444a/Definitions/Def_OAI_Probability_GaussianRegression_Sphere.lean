-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Sphere
-- name    : OAI_Probability_GaussianRegression_Sphere
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:11:59.777463+00:00
-- url     : https://prove2.me/theorems/b21c38d7-255f-406c-b8b2-cf0c60a3748b
-- title:
--   Uniform law on the unit ball, sphere laws as probability measures, and isometries of the sphere
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and canonical volume measure $\mathrm{vol}_E$, and let $S(E)=\{x\in E:\|x\|=1\}$ be its unit sphere. Recall the sphere law $\mathrm{Unif}_{S(E)}=\sigma_E(S(E))^{-1}\sigma_E$, the normalization of the surface measure $\sigma_E(A)=(\dim E)\cdot\mathrm{vol}_E(\{rx:0<r<1,\ x\in A\})$, and its ambient version, the push-forward of $\mathrm{Unif}_{S(E)}$ to $E$ under the inclusion. The file provides:
--
--   1. **Uniform law on the unit ball.** The measure
--      $$\mathrm{Unif}_{\bar B}=\mathrm{vol}_E\big(B(0,1)\big)^{-1}\;\mathrm{vol}_E\big|_{\bar B(0,1)},$$
--      the volume restricted to the closed unit ball and normalized by the volume of the open unit ball. It is recorded as a probability measure, for every $E$.
--
--   2. **Sphere laws are probability measures.** If $\dim E\ge1$, then $\mathrm{Unif}_{S(E)}$ is a probability measure on $S(E)$, and its ambient version is a probability measure on $E$.
--
--   3. **Isometries of the sphere.** For every linear isometric equivalence $e:E\to E$, the restriction
--      $$e|_{S(E)}:S(E)\to S(E)$$
--      is a homeomorphism of the unit sphere onto itself.
--
--   The uniform ball law satisfies a local mass bound with exponent $\dim E$ and serves as a basic regular measure on the unit ball. The sphere law is the prior on the unknown direction, and the restricted isometries express its rotation invariance: each of them preserves $\mathrm{Unif}_{S(E)}$, which is used in symmetrization (reflection) arguments for success probabilities.
--
--   **Formalization Note** The Lean names are `unitBallLaw` with the instance `unitBallLaw_probability`, the instances `sphereLaw_probability` and `ambientSphereLaw_probability` (both assuming `[Nontrivial E]`), and `sphereIsometry e` for `e : E ≃ₗᵢ[ℝ] E`. The open and closed unit balls have the same volume, so the normalization by the open ball is exact.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Sphere.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Sphere.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks

namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance ambientSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (ambientSphereLaw (E := E)) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def sphereIsometry (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖e x‖ = 1
    rw [e.norm_map])

end NoiselessRegression

end

end OAI


