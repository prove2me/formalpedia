-- Prove2me | Definitions.Def_SNumbers_GelfandEmbedding
-- name    : SNumbers_GelfandEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:05:59.670266+00:00
-- url     : https://prove2.me/theorems/da721d84-622c-4cac-8106-31d725723935
-- title:
--   Gelfand Embedding
-- statement:
--   Definitions and structural lemmas for Gelfand Embedding, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Theorems.Thm_SNumbers_IsMetricInjection_norm_le_one

set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal ENNReal
open ContinuousLinearMap
namespace SNumbers
namespace Embedding
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
section ToLInfty
variable {ι : Type u}
lemma memℓp_infty_apply (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC : ∀ i, ‖f i‖ ≤ C) (x : X) :
    Memℓp (fun i => f i x) ∞ := by
  refine memℓp_infty ⟨C * ‖x‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (f i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg x))
noncomputable def toLInfty (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖f i‖ ≤ C) :
    X →L[𝕜] lp (fun _ : ι => 𝕜) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => f i x, memℓp_infty_apply f hC x⟩
      map_add' := fun x y => by ext i; exact map_add (f i) x y
      map_smul' := fun c x => by ext i; exact map_smul (f i) c x }
    C
    (fun x => lp.norm_le_of_forall_le (mul_nonneg hC0 (norm_nonneg x)) fun i =>
      (f i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg x)))
end ToLInfty
abbrev DualBall (𝕜 : Type u) [RCLike 𝕜] (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] : Type u :=
  Metric.closedBall (0 : Y →L[𝕜] 𝕜) 1
lemma norm_le_one (φ : DualBall 𝕜 Y) : ‖(φ : Y →L[𝕜] 𝕜)‖ ≤ 1 := by
  have h := φ.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h
noncomputable def J : Y →L[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞ :=
  toLInfty (fun φ : DualBall 𝕜 Y => (φ : Y →L[𝕜] 𝕜)) zero_le_one norm_le_one
end Embedding
end SNumbers


