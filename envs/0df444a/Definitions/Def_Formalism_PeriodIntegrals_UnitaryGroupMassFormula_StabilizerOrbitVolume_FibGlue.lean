-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:59.69461+00:00
-- url     : https://prove2.me/theorems/e75e7f18-c446-46f5-81e1-e371a416e067
-- title:
--   Fib Glue
-- statement:
--   Definitions and structural lemmas for Fib Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FibGlue.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW.Glue
open MeasureTheory Topology Set Filter PI.VolStabSW
open scoped CompactlySupported
section Ext
variable {V : Type} [TopologicalSpace V] [T2Space V]
open Classical in

def extZ (U : Set V) (φ : U → ℝ) : V → ℝ := fun v => if h : v ∈ U then φ ⟨v, h⟩ else 0
theorem extZ_val (U : Set V) (φ : U → ℝ) (u : U) : extZ U φ u = φ u := by
  simp only [extZ, dif_pos u.2]
theorem tsupport_extZ_subset_image (U : Set V) (φ : U → ℝ) (hs : HasCompactSupport φ) :
    tsupport (extZ U φ) ⊆ Subtype.val '' tsupport φ := by
  have hK : IsCompact (Subtype.val '' tsupport φ) := hs.isCompact.image continuous_subtype_val
  refine closure_minimal ?_ hK.isClosed
  intro v hv
  rw [Function.mem_support] at hv
  by_cases h : v ∈ U
  · refine ⟨⟨v, h⟩, subset_tsupport _ ?_, rfl⟩
    rw [Function.mem_support]
    simpa only [extZ, dif_pos h] using hv
  · exact (hv (by simp only [extZ, dif_neg h])).elim
theorem extZ_props {U : Set V} (hU : IsOpen U) (φ : U → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) : IsCcOn U (extZ U φ) := by
  have hK : IsCompact (Subtype.val '' tsupport φ) := hs.isCompact.image continuous_subtype_val
  have hsub := tsupport_extZ_subset_image U φ hs
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hsub, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro v
    by_cases h : v ∈ U
    · have hcomp : extZ U φ ∘ Subtype.val = φ := funext (extZ_val U φ)
      have hat : ContinuousAt (extZ U φ ∘ Subtype.val) (⟨v, h⟩ : U) := by
        rw [hcomp]; exact hc.continuousAt
      exact hU.isOpenEmbedding_subtypeVal.continuousAt_iff.1 hat
    · have hv : v ∉ Subtype.val '' tsupport φ := by
        rintro ⟨u, _, hu⟩
        exact h (hu ▸ u.2)
      have hev : extZ U φ =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with w hw
        by_contra hne
        exact hw (hsub (subset_tsupport _ hne))
      exact continuousAt_const.congr hev.symm
  · refine hsub.trans ?_
    rintro _ ⟨u, _, rfl⟩
    exact u.2
theorem extZ_add (U : Set V) (φ ψ : U → ℝ) : extZ U (φ + ψ) = extZ U φ + extZ U ψ := by
  funext v
  by_cases h : v ∈ U
  · simp only [extZ, dif_pos h, Pi.add_apply]
  · simp only [extZ, dif_neg h, Pi.add_apply, add_zero]
theorem extZ_smul (U : Set V) (c : ℝ) (φ : U → ℝ) : extZ U (c • φ) = c • extZ U φ := by
  funext v
  by_cases h : v ∈ U
  · simp only [extZ, dif_pos h, Pi.smul_apply]
  · simp only [extZ, dif_neg h, Pi.smul_apply, smul_zero]
theorem extZ_nonneg (U : Set V) (φ : U → ℝ) (h : 0 ≤ φ) : 0 ≤ extZ U φ := by
  intro v
  by_cases hv : v ∈ U
  · simp only [extZ, dif_pos hv, Pi.zero_apply]
    exact h ⟨v, hv⟩
  · simp only [extZ, dif_neg hv, Pi.zero_apply, le_refl]
end Ext
section Dens
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
open Classical in

def G (hD : DensAll μ f ι ν U) (φ : V → ℝ) : X → ℝ :=
  if h : IsCcOn U φ then Classical.choose (hD φ h.1 h.2.1 h.2.2) else 0
theorem G_spec (hD : DensAll μ f ι ν U) {φ : V → ℝ} (h : IsCcOn U φ) :
    Continuous (G hD φ) ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, G hD φ b ∂ν := by
  have hc := Classical.choose_spec (hD φ h.1 h.2.1 h.2.2)
  simp only [G, dif_pos h]
  exact hc
variable [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
theorem nonneg_of_setIntegral_compact_nonneg {g : X → ℝ} (hg : Continuous g)
    (h : ∀ S, IsCompact S → 0 ≤ ∫ b in S, g b ∂ν) (b0 : X) : 0 ≤ g b0 := by
  by_contra hlt
  push_neg at hlt
  have hcneg : g b0 / 2 < 0 := by linarith
  have hW : {b | g b < g b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hg continuous_const).mem_nhds (show g b0 < g b0 / 2 by linarith)
  obtain ⟨K, hKn, hKW, hK⟩ := local_compact_nhds hW
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hK.measure_lt_top
  have hmeas : MeasurableSet K := hK.isClosed.measurableSet
  have h1 : ∫ b in K, g b ∂ν ≤ ∫ b in K, g b0 / 2 ∂ν :=
    setIntegral_mono_on (hg.continuousOn.integrableOn_compact hK)
      (continuous_const.continuousOn.integrableOn_compact hK) hmeas (fun b hb => le_of_lt (hKW hb))
  have h2 : ∫ b in K, g b0 / 2 ∂ν < 0 := by
    rw [setIntegral_const, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (ENNReal.toReal_pos hpos.ne' hfin.ne) hcneg
  linarith [h K hK]
theorem dens_unique {g1 g2 : X → ℝ} (h1 : Continuous g1) (h2 : Continuous g2)
    (h : ∀ S, IsCompact S → ∫ b in S, g1 b ∂ν = ∫ b in S, g2 b ∂ν) : g1 = g2 := by
  funext b
  have ha : 0 ≤ g1 b - g2 b := by
    refine nonneg_of_setIntegral_compact_nonneg (ν := ν) (g := fun x => g1 x - g2 x) (h1.sub h2) (fun S hS => ?_) b
    rw [integral_sub (h1.continuousOn.integrableOn_compact hS) (h2.continuousOn.integrableOn_compact hS), h S hS, sub_self]
  have hb : 0 ≤ g2 b - g1 b := by
    refine nonneg_of_setIntegral_compact_nonneg (ν := ν) (g := fun x => g2 x - g1 x) (h2.sub h1) (fun S hS => ?_) b
    rw [integral_sub (h2.continuousOn.integrableOn_compact hS) (h1.continuousOn.integrableOn_compact hS), h S hS, sub_self]
  linarith
theorem dens_nonneg {g : X → ℝ} (hg : Continuous g)
    (h : ∀ S, IsCompact S → 0 ≤ ∫ b in S, g b ∂ν) (b0 : X) : 0 ≤ g b0 := by
  exact nonneg_of_setIntegral_compact_nonneg hg h b0
variable [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace V]
theorem isCc_add {φ ψ : V → ℝ} (hφ : IsCcOn U φ) (hψ : IsCcOn U ψ) : IsCcOn U (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  refine (closure_minimal ?_ ((isClosed_tsupport φ).union (isClosed_tsupport ψ))).trans
    (union_subset hφ.2.2 hψ.2.2)
  intro x hx
  by_contra hn
  simp only [mem_union, not_or] at hn
  apply hx
  simp only [Pi.add_apply, image_eq_zero_of_notMem_tsupport hn.1,
    image_eq_zero_of_notMem_tsupport hn.2, add_zero]
theorem isCc_smul (c : ℝ) {φ : V → ℝ} (hφ : IsCcOn U φ) : IsCcOn U (c • φ) := by
  have hs : Function.support (c • φ) ⊆ Function.support φ := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp only [Pi.smul_apply, h0, smul_zero]
  exact ⟨hφ.1.const_smul c, hφ.2.1.mono hs, (closure_mono hs).trans hφ.2.2⟩
theorem G_add (hD : DensAll μ f ι ν U) {φ ψ : V → ℝ} (hφ : IsCcOn U φ) (hψ : IsCcOn U ψ) :
    G hD (φ + ψ) = G hD φ + G hD ψ := by
  have hs := G_spec hD (isCc_add hφ hψ)
  have h1 := G_spec hD hφ
  have h2 := G_spec hD hψ
  refine dens_unique (ν := ν) hs.1 (h1.1.add h2.1) (fun S hS => ?_)
  rw [← hs.2 S hS]
  simp only [Pi.add_apply]
  rw [integral_add (hφ.1.integrable_of_hasCompactSupport hφ.2.1).integrableOn
      (hψ.1.integrable_of_hasCompactSupport hψ.2.1).integrableOn,
    integral_add (h1.1.continuousOn.integrableOn_compact hS) (h2.1.continuousOn.integrableOn_compact hS),
    h1.2 S hS, h2.2 S hS]
theorem G_smul (hD : DensAll μ f ι ν U) (c : ℝ) {φ : V → ℝ} (hφ : IsCcOn U φ) :
    G hD (c • φ) = c • G hD φ := by
  have hs := G_spec hD (isCc_smul c hφ)
  have h1 := G_spec hD hφ
  refine dens_unique (ν := ν) hs.1 (h1.1.const_smul c) (fun S hS => ?_)
  rw [← hs.2 S hS]
  simp only [Pi.smul_apply]
  rw [integral_smul, integral_smul, h1.2 S hS]
theorem G_nonneg (hD : DensAll μ f ι ν U) {φ : V → ℝ} (hφ : IsCcOn U φ) (h0 : 0 ≤ φ) :
    0 ≤ G hD φ := by
  intro b
  have hs := G_spec hD hφ
  refine dens_nonneg (ν := ν) hs.1 (fun S hS => ?_) b
  rw [← hs.2 S hS]
  exact integral_nonneg (fun v => h0 v)
end Dens
section Riesz
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
def lam (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) : C_c(U, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun ψ => G hD (extZ U ψ) b
      map_add' := fun ψ1 ψ2 => by
        simp only [CompactlySupportedContinuousMap.coe_add, extZ_add]
        rw [G_add hD (extZ_props hU ψ1 ψ1.continuous ψ1.hasCompactSupport)
          (extZ_props hU ψ2 ψ2.continuous ψ2.hasCompactSupport)]
        rfl
      map_smul' := fun c ψ => by
        simp only [CompactlySupportedContinuousMap.coe_smul, extZ_smul, RingHom.id_apply]
        rw [G_smul hD c (extZ_props hU ψ ψ.continuous ψ.hasCompactSupport)]
        rfl }
    (fun ψ hψ => G_nonneg hD (extZ_props hU ψ ψ.continuous ψ.hasCompactSupport)
      (extZ_nonneg U ψ fun u => (CompactlySupportedContinuousMap.le_def.1 hψ) u) b)
variable [OpensMeasurableSpace V]
def fibG (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) : Measure V :=
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  (RealRMK.rieszMeasure (lam hD hU b)).map Subtype.val
def restr (hU : IsOpen U) (φ : V → ℝ) (h : IsCcOn U φ) : C_c(U, ℝ) where
  toFun := fun u => φ u
  continuous_toFun := h.1.comp continuous_subtype_val
  hasCompactSupport' := by
    have hsub : tsupport φ ⊆ Set.range (Subtype.val : U → V) := by
      rw [Subtype.range_coe]; exact h.2.2
    have hK : IsCompact ((Subtype.val : U → V) ⁻¹' tsupport φ) :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).2 h.2.1
    exact HasCompactSupport.intro' hK ((isClosed_tsupport φ).preimage continuous_subtype_val)
      fun u hu => image_eq_zero_of_notMem_tsupport hu
end Riesz
def DisintStep : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → ∀ fib : X → Measure V,
      (∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) →
      (∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤) →
      (∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν) →
      ∀ φ : V → ENNReal, Measurable φ → ∫⁻ v in U, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(fib b) ∂ν
end PI.VolStabSW.Glue


