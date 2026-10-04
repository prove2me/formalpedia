-- Prove2me | solution 1 for AnosovPlugs.isHyperbolicSet_of_metric
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T20:58:51.093674+00:00
-- url     : https://prove2.me/submissions/4b5c0511-5752-46d1-afbd-01230c0e1825

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_comparable_of_metrics

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

theorem hm_cmp
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [CompactSpace M] (g₀ g : RiemannianMetric3 M) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (x : M) (v : TangentSpace I3 x),
      c₁ * g₀.norm x v ≤ g.norm x v ∧ g.norm x v ≤ c₂ * g₀.norm x v := by
  have hinj : ∀ x : M, Function.Injective (mfderiv I3 I3 (id : M → M) x) := by
    intro x a b hab
    simpa [mfderiv_id] using hab
  obtain ⟨c₁, c₂, h1, h2, h⟩ :=
    comparable_of_metrics (M := M) (N := M) id contMDiff_id hinj g₀ g
  refine ⟨c₁, c₂, h1, h2, fun x v => ?_⟩
  have := h x v
  simpa [mfderiv_id] using this

theorem hm_norm_nonneg
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (g : RiemannianMetric3 M) (x : M) (v : TangentSpace I3 x) : 0 ≤ g.norm x v :=
  Real.sqrt_nonneg _

theorem hm_est {a b n₀ n c₁ c₂ C E : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hC : 0 < C) (hE : 0 < E)
    (h1 : a ≤ c₂ * b) (h2 : b ≤ C * E * n₀) (h3 : c₁ * n₀ ≤ n) :
    a ≤ C * c₂ / c₁ * E * n := by
  have h4 : n₀ ≤ n / c₁ := by rw [le_div_iff₀ hc₁]; linarith
  have hCE : 0 ≤ C * E := by positivity
  calc a ≤ c₂ * b := h1
    _ ≤ c₂ * (C * E * n₀) := mul_le_mul_of_nonneg_left h2 hc₂.le
    _ ≤ c₂ * (C * E * (n / c₁)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hCE) hc₂.le
    _ = C * c₂ / c₁ * E * n := by field_simp

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [CompactSpace M]
    (X : (x : M) → TangentSpace I3 x) (Λ : Set M) (hΛ : IsHyperbolicSet X Λ)
    (g : RiemannianMetric3 M) :
    ∃ (Es Eu : (x : M) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
      ∀ x ∈ Λ,
        Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
        Es x ⊔ Submodule.span ℝ {X x} ⊔ Eu x = ⊤ ∧
        (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap X t) x).toLinearMap = Es (flowMap X t x)) ∧
        (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap X t) x).toLinearMap = Eu (flowMap X t x)) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
          g.norm (flowMap X t x) (mfderiv I3 I3 (flowMap X t) x v)
            ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
          g.norm (flowMap X (-t) x) (mfderiv I3 I3 (flowMap X (-t)) x v)
            ≤ C * Real.exp (-lam * t) * g.norm x v) := by
  obtain ⟨g₀, Es, Eu, C, lam, hC, hlam, h⟩ := hΛ
  obtain ⟨c₁, c₂, hc₁, hc₂, hcmp⟩ := hm_cmp g₀ g
  refine ⟨Es, Eu, C * c₂ / c₁, lam, by positivity, hlam, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h x hx
  refine ⟨h1, h2, h3, h4, h5, fun t ht v hv => ?_, fun t ht v hv => ?_⟩
  · exact hm_est hc₁ hc₂ hC (Real.exp_pos _) ((hcmp _ _).2) (h6 t ht v hv) ((hcmp x v).1)
  · exact hm_est hc₁ hc₂ hC (Real.exp_pos _) ((hcmp _ _).2) (h7 t ht v hv) ((hcmp x v).1)
