-- Prove2me | solution 1 for AsymptoticOperator.exists_hilbertBasis_eigenvectors_of_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:46:48.85298+00:00
-- url     : https://prove2.me/submissions/54e1484e-5d0a-4af6-a089-4002dc509b46

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open Module End Filter Topology

/-- A compact, symmetric, injective bounded operator on a real Hilbert space has a Hilbert basis
of eigenvectors; the eigenvalues are nonzero and tend to `0` along the cofinite filter. -/
theorem solution {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) (hinj : Function.Injective T) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ E) (ν : ι → ℝ),
      (∀ i, T (b i) = ν i • b i) ∧ (∀ i, ν i ≠ 0) ∧ Tendsto ν cofinite (𝓝 0) := by
  set V : ℝ → Submodule ℝ E := fun μ => eigenspace (T : End ℝ E) μ with hV
  have hclosed : ∀ μ, IsClosed (V μ : Set E) := fun μ => by
    have : (V μ : Set E) = {x | T x = μ • x} := by
      ext x; simp [hV, mem_eigenspace_iff]
    rw [this]; exact isClosed_eq T.continuous (continuous_const_smul μ)
  haveI : ∀ μ, CompleteSpace (V μ) := fun μ => (hclosed μ).completeSpace_coe
  choose w bb hbb using fun μ => exists_hilbertBasis ℝ (V μ)
  set v : (Σ μ, w μ) → E := fun a => ((bb a.1 a.2 : V a.1) : E) with hv
  have hon : Orthonormal ℝ v :=
    (hsym.orthogonalFamily_eigenspaces).orthonormal_sigma_orthonormal
      (v_family := fun μ => bb μ) (fun μ => (bb μ).orthonormal)
  have hev : ∀ a, T (v a) = a.1 • v a := fun a => by
    have := (bb a.1 a.2 : V a.1).2
    exact mem_eigenspace_iff.mp this
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff, ← ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym]
    intro x hx
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro μ
    rw [Submodule.mem_orthogonal]
    intro y hy
    let φ : V μ →L[ℝ] ℝ := (innerSL ℝ x).comp (V μ).subtypeL
    have hker : Submodule.span ℝ (Set.range (bb μ)) ≤ LinearMap.ker (φ : V μ →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h1 : v ⟨μ, j⟩ ∈ Submodule.span ℝ (Set.range v) :=
        Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩
      have h2 := (Submodule.mem_orthogonal' _ _).mp hx _ h1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, φ,
        ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply]
      simpa [hv] using h2
    have hcl : (Submodule.span ℝ (Set.range (bb μ))).topologicalClosure ≤
        LinearMap.ker (φ : V μ →ₗ[ℝ] ℝ) :=
      Submodule.topologicalClosure_minimal _ hker (isClosed_eq φ.continuous continuous_const)
    rw [(bb μ).dense_span] at hcl
    have := hcl (Submodule.mem_top (x := (⟨y, hy⟩ : V μ)))
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, φ, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Submodule.subtypeL_apply] at this
    rw [real_inner_comm]; exact this
  refine ⟨Σ μ, w μ, HilbertBasis.mkOfOrthogonalEqBot hon hsp, fun a => a.1, ?_, ?_, ?_⟩
  · intro a; rw [HilbertBasis.coe_mkOfOrthogonalEqBot]; exact hev a
  · intro a h0
    have h0' : a.1 = 0 := h0
    have h : T (v a) = T 0 := by rw [hev a, h0', zero_smul, map_zero]
    exact (hon.ne_zero a) (hinj h)
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.mp
      (hT.isCompact_closure_image_closedBall 1).totallyBounded (ε / 2) (by positivity)
    have hsmall : ∀ y ∈ t, ∀ᶠ a in cofinite, |inner ℝ (v a) y| < ε / 2 := by
      intro y _
      have h1 := (hon.inner_products_summable (x := y)).tendsto_cofinite_zero
      have h2 : ∀ᶠ a in cofinite, ‖inner ℝ (v a) y‖ ^ 2 < (ε / 2) ^ 2 :=
        h1.eventually (gt_mem_nhds (by positivity))
      filter_upwards [h2] with a ha
      rw [Real.norm_eq_abs, sq_abs] at ha
      exact abs_lt_of_sq_lt_sq ha (by positivity)
    filter_upwards [(eventually_all_finite ht).mpr hsmall] with a ha
    have hmem : T (v a) ∈ closure (T '' Metric.closedBall 0 1) :=
      subset_closure ⟨v a, by simp [hon.1 a], rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (hcov hmem)
    rw [Metric.mem_ball] at hy
    have hval : a.1 = inner ℝ (T (v a) - y) (v a) + inner ℝ y (v a) := by
      rw [inner_sub_left, sub_add_cancel, hev a, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hon.1 a]; ring
    have hb1 : |inner ℝ (T (v a) - y) (v a)| ≤ ‖T (v a) - y‖ := by
      have := abs_real_inner_le_norm (T (v a) - y) (v a)
      rwa [hon.1 a, mul_one] at this
    have hb2 := ha y hyt
    rw [real_inner_comm] at hb2
    rw [dist_eq_norm] at hy
    rw [Real.dist_eq, sub_zero, hval]
    calc |inner ℝ (T (v a) - y) (v a) + inner ℝ y (v a)|
        ≤ |inner ℝ (T (v a) - y) (v a)| + |inner ℝ y (v a)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
