-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:42.083825+00:00
-- url     : https://prove2.me/theorems/4567d150-aba7-499a-b8cf-f7e0d80cb0c4
-- title:
--   Integral Conj Inner Mul Inner Of Is Empty Equiv
-- statement:
--   Definitions and structural lemmas for Integral Conj Inner Mul Inner Of Is Empty Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
namespace GlobalTheory
section Haar
variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
noncomputable def haarProb : Measure K := haarMeasure ⊤
instance haarProb_isHaarMeasure : (haarProb K).IsHaarMeasure := by
  unfold haarProb; infer_instance
instance haarProb_isProbabilityMeasure : IsProbabilityMeasure (haarProb K) :=
  ⟨by simpa [haarProb] using (haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K)))⟩
variable {K}
theorem eq_haarProb (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ = haarProb K :=
  isHaarMeasure_eq_of_isProbabilityMeasure _ _
instance haarProb_isMulRightInvariant : (haarProb K).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : IsProbabilityMeasure (Measure.map (fun x => x * g) (haarProb K)) :=
    isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarProb _
instance haarProb_isInvInvariant : (haarProb K).IsInvInvariant := by
  refine ⟨?_⟩
  have : IsProbabilityMeasure (haarProb K).inv :=
    isProbabilityMeasure_map measurable_inv.aemeasurable
  have : (haarProb K).inv.IsHaarMeasure := {}
  exact eq_haarProb _
end Haar
theorem isCompact_unitaryGroup (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜] :
    IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have hK : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1 : Set (Matrix n n 𝕜))) hK
    (isClosed_unitary (R := Matrix n n 𝕜)) ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary hU i j
instance compactSpace_unitaryGroup (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜] :
    CompactSpace (Matrix.unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n 𝕜)
section Schur
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
omit [Group K] [IsTopologicalGroup K] in

theorem integrable_of_continuous_of_compactSpace [IsFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] {f : K → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem inner_map_map_of_norm_map {G : Type*} [Monoid G] {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (ρ : Representation 𝕜 G E)
    (h : ∀ k v, ‖ρ k v‖ = ‖v‖) (k : G) (u v : E) : ⟪ρ k u, ρ k v⟫_𝕜 = ⟪u, v⟫_𝕜 :=
  LinearIsometry.inner_map_map ⟨ρ k, h k⟩ u v
variable [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
noncomputable def rankOneAverage (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (hσc : ∀ w, Continuous fun k => σ k w) (v : V) (w : W) :
    ρ.IntertwiningMap σ where
  toFun x := ∫ k, ⟪ρ k v, x⟫_ℂ • σ k w ∂μ
  map_add' x y := by
    have hi : ∀ z : V, Integrable (fun k => ⟪ρ k v, z⟫_ℂ • σ k w) μ := fun z =>
      integrable_of_continuous_of_compactSpace μ (((hρc v).inner continuous_const).smul (hσc w))
    rw [← integral_add (hi x) (hi y)]
    simp [add_smul]
  map_smul' c x := by
    simp [mul_smul, integral_smul]
  isIntertwining' g := by
    ext x
    have := FiniteDimensional.complete ℂ W
    have h1 := integral_mul_left_eq_self (μ := μ) (fun k => ⟪ρ k v, ρ g x⟫_ℂ • σ k w) g
    have h2 := (LinearMap.toContinuousLinearMap (σ g)).integral_comp_comm
      (integrable_of_continuous_of_compactSpace μ
        (((hρc v).inner (𝕜 := ℂ) (continuous_const (y := x))).smul (hσc w)))
    simp only [map_mul, Module.End.mul_apply, inner_map_map_of_norm_map ρ hρu] at h1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h1]
    simpa using h2
end Schur
section Schur
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
end Schur
section Reducible
variable {𝕜 : Type*} [RCLike 𝕜]
def orthogonalSubrepresentation {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {ρ : Representation 𝕜 G V} (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖)
    (U : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := U.toSubmoduleᗮ
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have h := hv _ (U.apply_mem_toSubmodule g⁻¹ hu)
    rw [← inner_map_map_of_norm_map ρ hρu g] at h
    simpa using h
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
@[reducible] noncomputable def averageCore [MeasurableSpace K] [BorelSpace K] {V E : Type*}
    [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (ρ : Representation 𝕜 K V) (e : V →ₗ[𝕜] E) (he : Function.Injective e)
    (hc : ∀ v, Continuous fun k => e (ρ k v)) : InnerProductSpace.Core 𝕜 V where
  inner u v := ∫ k, ⟪e (ρ k u), e (ρ k v)⟫_𝕜 ∂haarProb K
  conj_inner_symm u v := by
    simp only [← integral_conj, inner_conj_symm]
  re_inner_nonneg v := by
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal, RCLike.ofReal_re]
    exact integral_nonneg fun k => by positivity
  add_left u u' v := by
    have hi : ∀ z : V, Integrable (fun k => ⟪e (ρ k z), e (ρ k v)⟫_𝕜) (haarProb K) := fun z =>
      integrable_of_continuous_of_compactSpace _ ((hc z).inner (hc v))
    simp only [map_add, inner_add_left]
    exact integral_add (hi u) (hi u')
  smul_left u v r := by
    simp only [map_smul, inner_smul_left, integral_const_mul]
  definite v hv := by
    by_contra h
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal,
      RCLike.ofReal_eq_zero] at hv
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := haarProb K) (x := 1)
      (f := fun k => ‖e (ρ k v)‖ ^ 2) ((hc v).norm.pow 2) (HasCompactSupport.of_compactSpace _)
      (fun k => by positivity) ?_).ne' hv
    simpa [map_eq_zero_iff e he] using h
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
end Reducible
end GlobalTheory


