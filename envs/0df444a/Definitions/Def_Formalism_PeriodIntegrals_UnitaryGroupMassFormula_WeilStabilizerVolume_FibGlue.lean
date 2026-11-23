-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:08.659828+00:00
-- url     : https://prove2.me/theorems/a57375d1-8198-4602-a80a-35644138044a
-- title:
--   Fib Glue
-- statement:
--   Definitions and structural lemmas for Fib Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibGlue.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Theorems.Thm_PI_VolStabW_DensGen_eq_zero_of_setIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW.Glue
open MeasureTheory Topology Set Filter PI.VolStabW
open scoped CompactlySupported
section Ext
variable {V : Type} [TopologicalSpace V] [T2Space V]
open Classical in

def extZ (U : Set V) (φ : U → ℝ) : V → ℝ := fun v => if h : v ∈ U then φ ⟨v, h⟩ else 0
theorem extZ_val (U : Set V) (φ : U → ℝ) (u : U) : extZ U φ u = φ u := by simp [extZ]
theorem extZ_props {U : Set V} (hU : IsOpen U) (φ : U → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) : IsCcOn U (extZ U φ) := by
  set K : Set V := Subtype.val '' tsupport φ with hKdef
  have hK : IsCompact K := hs.image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨u, -, rfl⟩; exact u.2
  have hzero : ∀ v ∉ K, extZ U φ v = 0 := by
    intro v hv
    by_cases h : v ∈ U
    · simp only [extZ, h, dite_true]
      exact image_eq_zero_of_notMem_tsupport (fun hm => hv ⟨⟨v, h⟩, hm, rfl⟩)
    · simp [extZ, h]
  have hsupp : tsupport (extZ U φ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro v hv
    by_contra h
    exact hv (hzero v h)
  refine ⟨?_, HasCompactSupport.intro' hK hK.isClosed hzero, hsupp.trans hKU⟩
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v ∈ U
  · have hcon : ContinuousOn (extZ U φ) U := by
      rw [continuousOn_iff_continuous_restrict]
      convert hc using 1
      funext u; exact extZ_val U φ u
    exact hcon.continuousAt (hU.mem_nhds hv)
  · have hvK : v ∉ K := fun h => hv (hKU h)
    have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 v] extZ U φ := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hvK] with w hw using (hzero w hw).symm
    exact (continuousAt_const (y := (0 : ℝ))).congr hev
theorem extZ_add (U : Set V) (φ ψ : U → ℝ) : extZ U (φ + ψ) = extZ U φ + extZ U ψ := by
  funext v; by_cases h : v ∈ U <;> simp [extZ, h]
theorem extZ_smul (U : Set V) (c : ℝ) (φ : U → ℝ) : extZ U (c • φ) = c • extZ U φ := by
  funext v; by_cases h : v ∈ U <;> simp [extZ, h]
theorem extZ_nonneg (U : Set V) (φ : U → ℝ) (h : 0 ≤ φ) : 0 ≤ extZ U φ := by
  intro v; by_cases hv : v ∈ U
  · simp only [extZ, hv, dite_true]; exact h _
  · simp [extZ, hv]
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
  classical
  simp only [G, dif_pos h]
  exact Classical.choose_spec (hD φ h.1 h.2.1 h.2.2)
variable [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
theorem dens_unique {g1 g2 : X → ℝ} (h1 : Continuous g1) (h2 : Continuous g2)
    (h : ∀ S, IsCompact S → ∫ b in S, g1 b ∂ν = ∫ b in S, g2 b ∂ν) : g1 = g2 := by
  funext b
  have := DensGen.eq_zero_of_setIntegral (ν := ν) (fun b => g1 b - g2 b) univ b univ_mem
    (h1.sub h2).continuousOn (fun S hS _ => by
      rw [integral_sub (h1.continuousOn.integrableOn_compact hS)
        (h2.continuousOn.integrableOn_compact hS), h S hS, sub_self])
  linarith
theorem dens_nonneg {g : X → ℝ} (hg : Continuous g)
    (h : ∀ S, IsCompact S → 0 ≤ ∫ b in S, g b ∂ν) (b0 : X) : 0 ≤ g b0 := by
  by_contra hneg
  have hneg' : 0 < -g b0 := by linarith
  have hev : ∀ᶠ b in 𝓝 b0, -g b0 / 2 < -g b :=
    (hg.neg.continuousAt (x := b0)).eventually (lt_mem_nhds (by simp only [Pi.neg_apply]; linarith))
  obtain ⟨S, hSn, hSsub, hSc⟩ := local_compact_nhds hev
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hlt : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  have hpos' : 0 < ν.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hSn).ne' hlt
  have hge := setIntegral_ge_of_const_le_real (c := -g b0 / 2) hSm hlt
    (fun b hb => (hSsub hb).le) (hg.neg.continuousOn.integrableOn_compact hSc)
  simp only [Pi.neg_apply, integral_neg] at hge
  have := h S hSc
  nlinarith
variable [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace V]
theorem isCc_add {φ ψ : V → ℝ} (hφ : IsCcOn U φ) (hψ : IsCcOn U ψ) : IsCcOn U (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
    (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩
theorem isCc_smul (c : ℝ) {φ : V → ℝ} (hφ : IsCcOn U φ) : IsCcOn U (c • φ) :=
  ⟨hφ.1.const_smul c, hφ.2.1.smul_left,
    (tsupport_smul_subset_right (fun _ : V => c) φ).trans hφ.2.2⟩
theorem G_add (hD : DensAll μ f ι ν U) {φ ψ : V → ℝ} (hφ : IsCcOn U φ) (hψ : IsCcOn U ψ) :
    G hD (φ + ψ) = G hD φ + G hD ψ := by
  have hs := G_spec hD (isCc_add hφ hψ)
  refine dens_unique (ν := ν) hs.1 ((G_spec hD hφ).1.add (G_spec hD hψ).1) fun S hS => ?_
  rw [← hs.2 S hS, Pi.add_def, integral_add
    (hφ.1.integrable_of_hasCompactSupport hφ.2.1).integrableOn
    (hψ.1.integrable_of_hasCompactSupport hψ.2.1).integrableOn, (G_spec hD hφ).2 S hS,
    (G_spec hD hψ).2 S hS, Pi.add_def, integral_add
    ((G_spec hD hφ).1.continuousOn.integrableOn_compact hS)
    ((G_spec hD hψ).1.continuousOn.integrableOn_compact hS)]
theorem G_smul (hD : DensAll μ f ι ν U) (c : ℝ) {φ : V → ℝ} (hφ : IsCcOn U φ) :
    G hD (c • φ) = c • G hD φ := by
  have hs := G_spec hD (isCc_smul c hφ)
  refine dens_unique (ν := ν) hs.1 ((G_spec hD hφ).1.const_smul c) fun S hS => ?_
  rw [← hs.2 S hS]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul, (G_spec hD hφ).2 S hS]
theorem G_nonneg (hD : DensAll μ f ι ν U) {φ : V → ℝ} (hφ : IsCcOn U φ) (h0 : 0 ≤ φ) :
    0 ≤ G hD φ := fun b =>
  dens_nonneg (G_spec hD hφ).1 (fun S hS => by
    rw [← (G_spec hD hφ).2 S hS]; exact integral_nonneg fun v => h0 v) b
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
end PI.VolStabW.Glue


