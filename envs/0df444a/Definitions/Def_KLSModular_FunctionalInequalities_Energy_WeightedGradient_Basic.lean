-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic
-- name    : KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:26:45.600999+00:00
-- url     : https://prove2.me/theorems/f6b93e94-4e8d-4cc9-94ea-458e2669b85c
-- title:
--   Weighted gradient tests and operator
-- statement:
--   For a probability measure ν on a finite-dimensional real Hilbert space and a continuous linear map B, `WeightedGradient.apply B g` is B composed with the canonical gradient of g. `WeightedGradient.IsTest` requires g to be globally Lipschitz, square-integrable for ν, and to have square-integrable weighted gradient. Under absolute continuity with respect to a Haar measure, the test class is closed under addition and real scalar multiplication up to ν-almost-everywhere equality of weighted gradients. When the support frontier is ν-null, `WeightedGradient.graph` is the graph of the partially defined operator `WeightedGradient.operator`; its domain and action are characterized by `mem_domain_operator_iff`, `toLp_mem_domain_operator`, and `operator_apply`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.L2.MeanVariance
--   import FunctionalInequalities.Energy.CovarianceGradient.Basic
--   import FunctionalInequalities.Energy.Relaxation.LinearPMap
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def apply (B : V →L[ℝ] V) (g : V → ℝ) (x : V) : V :=
--     B (gradient g x)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43), [`Energy/Relaxation/LinearPMap`](https://prove2.me/theorems/2ed50aac-81dd-45da-b8c8-597e80695a44).
--
--   Theorems in source order:
--
--   - [`weightedTest_iff_exists_test`](https://prove2.me/theorems/6e254f19-783a-445b-a40f-180ee3e4ec09)
--   - [`relaxation_eq_ofLinearPMap`](https://prove2.me/theorems/ecd8db80-1079-4c3b-8976-dc3390ed944f)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean) · `FunctionalInequalities.Energy.WeightedGradient.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean#L49-L292 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.WeightedGradient.Basic`, definition bundle `KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
namespace FunctionalInequalities
namespace Energy
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Gradient
namespace WeightedGradient
omit [InnerProductSpace ℝ V] [CompleteSpace V] in
/-- Real scalar multiples of Lipschitz functions are Lipschitz. -/
theorem lipschitzWith_const_smul_real {g : V → ℝ} {K : NNReal} (hK : LipschitzWith K g) (c : ℝ) :
    LipschitzWith (‖c‖₊ * K) (c • g) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul,
    coe_nnnorm, Real.norm_eq_abs, mul_assoc]
  gcongr
  simpa [Real.dist_eq] using hK.dist_le_mul x y
/-- The gradient is additive at points where both functions are differentiable. -/
theorem gradient_add_of_differentiableAt {g₁ g₂ : V → ℝ} {x : V}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) :
    gradient (g₁ + g₂) x = gradient g₁ x + gradient g₂ x := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient, map_add]
  exact fderiv_add h₁ h₂
/-- The gradient commutes with real scalars at differentiability points. -/
theorem gradient_const_smul_of_differentiableAt {g : V → ℝ} {x : V} (c : ℝ)
    (h : DifferentiableAt ℝ g x) : gradient (c • g) x = c • gradient g x := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient, map_smul]
  exact fderiv_const_smul h c
/-- The weighted gradient `B ∘ ∇g`. -/
def apply (B : V →L[ℝ] V) (g : V → ℝ) (x : V) : V :=
  B (gradient g x)
end WeightedGradient
namespace WeightedGradient
/-- The weighted gradient of a constant vanishes. -/
@[simp]
theorem apply_const (B : V →L[ℝ] V) (c : ℝ) :
    apply B (fun _ ↦ c) = fun _ ↦ 0 := by
  funext x
  simp [apply, gradient_fun_const]
/-- The identity-weighted gradient is the gradient. -/
theorem apply_id (g : V → ℝ) :
    apply (ContinuousLinearMap.id ℝ V) g = gradient g := by
  funext x
  rfl
end WeightedGradient
end Gradient
section Operator
variable [MeasurableSpace V] (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)
namespace WeightedGradient
/-- Test data for the weighted gradient operator: globally Lipschitz, square integrable, with
square-integrable weighted gradient. -/
def IsTest (g : V → ℝ) : Prop :=
  (∃ K : NNReal, LipschitzWith K g) ∧ MemLp g 2 (ν : Measure V) ∧
    MemLp (apply B g) 2 (ν : Measure V)
end WeightedGradient
namespace WeightedGradient
namespace IsTest
variable {ν B} {g : V → ℝ}
theorem continuous (h : IsTest ν B g) : Continuous g := by
  obtain ⟨K, hK⟩ := h.1
  exact hK.continuous
theorem memLp (h : IsTest ν B g) : MemLp g 2 (ν : Measure V) := h.2.1
theorem memLp_apply (h : IsTest ν B g) :
    MemLp (Energy.WeightedGradient.apply B g) 2 (ν : Measure V) := h.2.2
theorem const (c : ℝ) : IsTest ν B (fun _ ↦ c) :=
  ⟨⟨0, LipschitzWith.const c⟩, memLp_const c, by
    rw [Energy.WeightedGradient.apply_const]
    exact memLp_const 0⟩
variable [BorelSpace V] [FiniteDimensional ℝ V] {m : Measure V} [m.IsAddHaarMeasure]
/-- Under absolute continuity, the weighted gradient is additive `ν`-almost everywhere. -/
theorem apply_add_ae (hac : (ν : Measure V) ≪ m) {g₁ g₂ : V → ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) :
    Energy.WeightedGradient.apply B g₁ + Energy.WeightedGradient.apply B g₂ =ᵐ[(ν : Measure V)]
      Energy.WeightedGradient.apply B (g₁ + g₂) := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  filter_upwards [hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
    hK₁.locallyLipschitz m), hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
    hK₂.locallyLipschitz m)] with x hx₁ hx₂
  simp only [Pi.add_apply, Energy.WeightedGradient.apply, Energy.WeightedGradient.gradient_add_of_differentiableAt hx₁ hx₂, map_add]
/-- Under absolute continuity, the weighted gradient is homogeneous `ν`-almost everywhere. -/
theorem apply_smul_ae (hac : (ν : Measure V) ≪ m) (c : ℝ) (h : IsTest ν B g) :
    c • Energy.WeightedGradient.apply B g =ᵐ[(ν : Measure V)] Energy.WeightedGradient.apply B (c • g) := by
  obtain ⟨K, hK⟩ := h.1
  filter_upwards [hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
    hK.locallyLipschitz m)] with x hx
  simp only [Pi.smul_apply, Energy.WeightedGradient.apply, Energy.WeightedGradient.gradient_const_smul_of_differentiableAt c hx,
    map_smul]
theorem add (hac : (ν : Measure V) ≪ m) {g₁ g₂ : V → ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) : IsTest ν B (g₁ + g₂) := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  exact ⟨⟨K₁ + K₂, hK₁.add hK₂⟩, h₁.memLp.add h₂.memLp,
    (h₁.memLp_apply.add h₂.memLp_apply).ae_eq
      (apply_add_ae hac h₁ h₂)⟩
theorem smul (hac : (ν : Measure V) ≪ m) (c : ℝ) (h : IsTest ν B g) :
    IsTest ν B (c • g) := by
  obtain ⟨K, hK⟩ := h.1
  exact ⟨⟨‖c‖₊ * K, Energy.WeightedGradient.lipschitzWith_const_smul_real hK c⟩, h.memLp.const_smul c,
    (h.memLp_apply.const_smul c).ae_eq (apply_smul_ae hac c h)⟩
end IsTest
end WeightedGradient
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : Measure V} [m.IsAddHaarMeasure]
namespace WeightedGradient
/-- The graph `{([g], [B ∇g]) : g test}` of the weighted gradient in `L²(ν) × L²(ν; V)`. It is
a submodule because Rademacher's theorem makes the gradient linear `ν`-almost everywhere. -/
def graph (hac : (ν : Measure V) ≪ m) :
    Submodule ℝ (Lp ℝ 2 (ν : Measure V) × Lp V 2 (ν : Measure V)) where
  carrier := {p | ∃ (g : V → ℝ) (h : IsTest ν B g),
    p = (h.memLp.toLp g, h.memLp_apply.toLp (apply B g))}
  zero_mem' := by
    refine ⟨fun _ ↦ 0, IsTest.const 0, ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_zero]
      symm
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [MemLp.coeFn_toLp (IsTest.const (ν := ν) (B := B) 0).memLp]
        with x hx
      rw [hx]
      rfl
    · simp only [Prod.snd_zero]
      symm
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [MemLp.coeFn_toLp (IsTest.const (ν := ν) (B := B) 0).memLp_apply]
        with x hx
      rw [hx]
      simp
  add_mem' := by
    rintro p₁ p₂ ⟨g₁, h₁, rfl⟩ ⟨g₂, h₂, rfl⟩
    refine ⟨g₁ + g₂, h₁.add hac h₂, Prod.ext ?_ ?_⟩
    · exact (MemLp.toLp_add h₁.memLp h₂.memLp).symm
    · simp only [Prod.snd_add]
      rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (IsTest.apply_add_ae hac h₁ h₂)
  smul_mem' := by
    rintro c p ⟨g, h, rfl⟩
    refine ⟨c • g, h.smul hac c, Prod.ext ?_ ?_⟩
    · exact (MemLp.toLp_const_smul c h.memLp).symm
    · simp only [Prod.smul_snd]
      rw [← MemLp.toLp_const_smul]
      exact MemLp.toLp_congr _ _ (IsTest.apply_smul_ae hac c h)
/-- When the frontier of the support is `ν`-null, the graph contains no pair `(0, y)` with
`y ≠ 0`: two Lipschitz representatives of the zero class have almost everywhere zero gradient. -/
theorem graph_snd_eq_zero (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    ∀ p ∈ graph ν B hac, p.1 = 0 → p.2 = 0 := by
  rintro p ⟨g, h, rfl⟩ h0
  simp only at h0 ⊢
  have hg : g =ᵐ[(ν : Measure V)] fun _ ↦ 0 := by
    have := (Lp.eq_zero_iff_ae_eq_zero.mp h0)
    exact (h.memLp.coeFn_toLp.symm.trans this)
  have hgrad := gradient_ae_eq_of_ae_eq hfr h.continuous continuous_const hg
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [h.memLp_apply.coeFn_toLp, hgrad] with x hx hgx
  rw [hx]
  simp [apply, hgx, gradient_fun_const]
/-- The weighted gradient operator `g ↦ B ∘ ∇g` as a partially defined linear map on `L²(ν)`
with values in `L²(ν; V)`. -/
def operator (hac : (ν : Measure V) ≪ m) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  (graph ν B hac).toLinearPMap
/-- The graph of the operator is the test graph. -/
theorem graph_operator (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    (operator ν B hac).graph = graph ν B hac :=
  Submodule.toLinearPMap_graph_eq _ (graph_snd_eq_zero ν B hac hfr)
omit [SecondCountableTopology V] in
/-- The domain consists exactly of the classes of globally Lipschitz `L²` functions with
square-integrable weighted gradient. -/
theorem mem_domain_operator_iff (hac : (ν : Measure V) ≪ m) (f : Lp ℝ 2 (ν : Measure V)) :
    f ∈ (operator ν B hac).domain ↔
      ∃ (g : V → ℝ) (h : IsTest ν B g), f = h.memLp.toLp g := by
  change f ∈ (graph ν B hac).map (LinearMap.fst ℝ _ _) ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨p, ⟨g, h, rfl⟩, rfl⟩
    exact ⟨g, h, rfl⟩
  · rintro ⟨g, h, rfl⟩
    exact ⟨_, ⟨g, h, rfl⟩, rfl⟩
omit [SecondCountableTopology V] in
/-- Every test class lies in the domain. -/
theorem toLp_mem_domain_operator (hac : (ν : Measure V) ≪ m) {g : V → ℝ}
    (h : IsTest ν B g) : h.memLp.toLp g ∈ (operator ν B hac).domain :=
  (mem_domain_operator_iff ν B hac _).mpr ⟨g, h, rfl⟩
/-- The operator sends the class of a test to the class of its weighted gradient. -/
theorem operator_apply (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {g : V → ℝ}
    (h : IsTest ν B g) {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (operator ν B hac).domain) (hfg : f = h.memLp.toLp g) :
    operator ν B hac ⟨f, hf⟩ = h.memLp_apply.toLp (apply B g) := by
  symm
  rw [LinearPMap.image_iff hf, graph_operator ν B hac hfr]
  exact ⟨g, h, by rw [hfg]⟩
end WeightedGradient
end Operator
end Energy
end FunctionalInequalities


