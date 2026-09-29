-- Prove2me | solution 1 for AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c368d555-66a7-5e3c-ab1e-c46dc45842be

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TransversalMeasure
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

namespace QT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem sum_compl_eq_zero {n : ℕ} {τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ} {S : Set (AdeleRing (𝓞 L) L)ˣ}
    (hτ0 : ∀ j, τ j Sᶜ = 0) : (∑ j, τ j) Sᶜ = 0 := by
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun j _ => hτ0 j

theorem measure_preimage_inter_eq {ν : Measure (AdeleRing (𝓞 L) L)ˣ} {S E : Set (AdeleRing (𝓞 L) L)ˣ}
    (hν : ν Sᶜ = 0) (φ : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) (hφ : ∀ t ∈ S, φ t ∈ S) :
    ν (φ ⁻¹' (E ∩ S)) = ν (φ ⁻¹' E) := by
  apply le_antisymm (measure_mono (Set.preimage_mono Set.inter_subset_left))
  calc ν (φ ⁻¹' E) ≤ ν (φ ⁻¹' E ∩ S ∪ Sᶜ) := measure_mono fun t ht => by
          by_cases hs : t ∈ S
          · exact Or.inl ⟨ht, hs⟩
          · exact Or.inr hs
    _ ≤ ν (φ ⁻¹' E ∩ S) + ν Sᶜ := measure_union_le _ _
    _ = ν (φ ⁻¹' E ∩ S) := by rw [hν, add_zero]
    _ ≤ ν (φ ⁻¹' (E ∩ S)) := measure_mono fun t ht => ⟨ht.1, hφ t ht.2⟩

theorem transfer
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (H : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ => ∫⁻ t, H (t * idelesBaseChange K L s) ∂(∑ j, τ j)) ∧
    ∫⁻ t in saturated K L Sτ, H t ∂(NumberField.Idele.idelicHaar L) =
      cτ * ∫⁻ s, ∫⁻ t, H (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) := by
  have hsum0 : (∑ j, τ j) (saturated K L Sτ)ᶜ = 0 := sum_compl_eq_zero hτ0

  have hmt : ∀ s : (AdeleRing (𝓞 K) K)ˣ, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ => t * idelesBaseChange K L s :=
    fun s => (continuous_mul_right _).measurable
  refine Measurable.ennreal_induction (motive := fun H =>
    Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ => ∫⁻ t, H (t * idelesBaseChange K L s) ∂(∑ j, τ j)) ∧
    ∫⁻ t in saturated K L Sτ, H t ∂(NumberField.Idele.idelicHaar L) =
      cτ * ∫⁻ s, ∫⁻ t, H (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) ?_ ?_ ?_ hH
  ·
    intro c E hE
    have hpre : ∀ s : (AdeleRing (𝓞 K) K)ˣ,
        ∫⁻ t, E.indicator (fun _ => c) (t * idelesBaseChange K L s) ∂(∑ j, τ j) =
          c * (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' (E ∩ saturated K L Sτ)) := by
      intro s
      rw [measure_preimage_inter_eq hsum0 _ (fun t ht => hmul t ht s)]
      rw [show (fun t => E.indicator (fun _ => c) (t * idelesBaseChange K L s)) =
          ((fun t => t * idelesBaseChange K L s) ⁻¹' E).indicator (fun _ => c) from rfl]
      exact lintegral_indicator_const ((hmt s) hE) c
    obtain ⟨hm2, hid2⟩ := hτ2 (E ∩ saturated K L Sτ) (hE.inter hmeas) Set.inter_subset_right
    refine ⟨?_, ?_⟩
    · simp_rw [hpre]; exact hm2.const_mul c
    · simp_rw [hpre]
      rw [lintegral_indicator_const hE, Measure.restrict_apply hE, lintegral_const_mul c hm2, hid2]
      ring
  ·
    intro f g _ hf hg ⟨hfm, hfi⟩ ⟨hgm, hgi⟩
    have hsplit : ∀ s : (AdeleRing (𝓞 K) K)ˣ,
        ∫⁻ t, (f + g) (t * idelesBaseChange K L s) ∂(∑ j, τ j) =
          ∫⁻ t, f (t * idelesBaseChange K L s) ∂(∑ j, τ j) + ∫⁻ t, g (t * idelesBaseChange K L s) ∂(∑ j, τ j) :=
      fun s => lintegral_add_left (hf.comp (hmt s)) _
    refine ⟨?_, ?_⟩
    · simp_rw [hsplit]; exact hfm.add hgm
    · simp_rw [hsplit]
      rw [lintegral_add_left hfm, Pi.add_def, lintegral_add_left hf, hfi, hgi, mul_add]
  ·
    intro f hfmeas hmono hP
    have hsup : ∀ s : (AdeleRing (𝓞 K) K)ˣ,
        ∫⁻ t, (fun x => ⨆ n, f n x) (t * idelesBaseChange K L s) ∂(∑ j, τ j) =
          ⨆ n, ∫⁻ t, f n (t * idelesBaseChange K L s) ∂(∑ j, τ j) := by
      intro s
      exact lintegral_iSup (fun n => (hfmeas n).comp (hmt s)) (fun i j hij t => hmono hij _)
    refine ⟨?_, ?_⟩
    · simp_rw [hsup]; exact Measurable.iSup fun n => (hP n).1
    · simp_rw [hsup]
      rw [lintegral_iSup hfmeas hmono, lintegral_iSup (fun n => (hP n).1)
        (fun i j hij s => lintegral_mono fun t => hmono hij _), ENNReal.mul_iSup]
      exact iSup_congr fun n => (hP n).2

end QT

open scoped Pointwise

namespace QT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem tsum_indicator_smul_ae_eq_one {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    {s : Set α} {μ : Measure α} [Countable G] (h : IsFundamentalDomain G s μ) :
    ∀ᵐ x ∂μ, ∑' g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) = 1 := by
  have hdis : ∀ p : G × G, ∀ᵐ x ∂μ, p.1 ≠ p.2 → ¬ (p.1 • x ∈ s ∧ p.2 • x ∈ s) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h' => (h' hp).elim
    · have h0 : μ (p.1⁻¹ • s ∩ p.2⁻¹ • s) = 0 := h.aedisjoint (inv_injective.ne hp)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
      rintro - ⟨h1, h2⟩
      exact hx ⟨Set.mem_inv_smul_set_iff.2 h1, Set.mem_inv_smul_set_iff.2 h2⟩
  have hall : ∀ᵐ x ∂μ, ∀ p : G × G, p.1 ≠ p.2 → ¬ (p.1 • x ∈ s ∧ p.2 • x ∈ s) := ae_all_iff.2 hdis
  filter_upwards [hall, h.ae_covers] with x hx hcov
  obtain ⟨g₀, hg₀⟩ := hcov
  have huniq : ∀ g, g • x ∈ s → g = g₀ := fun g hg => by
    by_contra hne
    exact hx (g, g₀) hne ⟨hg, hg₀⟩
  rw [tsum_eq_single g₀ (fun g hg => ?_)]
  · rw [Set.indicator_of_mem hg₀]
  · exact Set.indicator_of_notMem (fun hmem => hg (huniq g hmem)) _

theorem idelesBaseChange_map_injective :
    Function.Injective fun k : Kˣ =>
      idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) := by
  intro k₁ k₂ h
  apply Units.ext
  have h' := congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h
  simp only [idelesBaseChange, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at h'
  rw [M4aHerbrand.Bridge.genuineβ_compat, M4aHerbrand.Bridge.genuineβ_compat] at h'
  exact (algebraMap K L).injective (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L h')

end QT

namespace QT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem countable_units (F : Type*) [Field F] [NumberField F] : Countable Fˣ := by
  haveI : Countable F := Countable.of_equiv _ (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.symm
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

theorem clause1
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L))
    (G : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞) (hG : Measurable G)
    (hGinv : ∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      G (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) = G t) :
    ∫⁻ t in Ω ∩ saturated K L Sτ, G t ∂(NumberField.Idele.idelicHaar L) =
      cτ * ∫⁻ s in ΩK, ∫⁻ t, G (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) := by
  classical
  set ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
    with hιK
  set bc : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ := idelesBaseChange K L with hbc
  haveI : Countable Kˣ := countable_units K
  haveI : Countable ιK.range := Function.Surjective.countable (MonoidHom.rangeRestrict_surjective ιK)
  haveI : Countable (bc.comp ιK).range := Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)
  have hmt : ∀ s : (AdeleRing (𝓞 K) K)ˣ, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ => t * bc s :=
    fun s => (continuous_mul_const _).measurable
  have hmγ : ∀ γ : ιK.range, Measurable fun y : (AdeleRing (𝓞 L) L)ˣ => y * bc γ :=
    fun γ => (continuous_mul_const _).measurable

  obtain ⟨-, hA⟩ := transfer Sτ τ cτ hmeas hmul hτ0 hτ2 (Ω.indicator G) (hG.indicator hΩm)
  rw [← Measure.restrict_restrict hΩm, ← lintegral_indicator hΩm, hA]
  rcases eq_or_ne cτ 0 with hc | hc
  · simp [hc]
  congr 1

  rw [hΩK.lintegral_eq_tsum'' (fun s => ∫⁻ t, Ω.indicator G (t * bc s) ∂(∑ j, τ j))]

  have hterm : ∀ (γ : ιK.range) (s : (AdeleRing (𝓞 K) K)ˣ),
      (∫⁻ t, Ω.indicator G (t * bc (γ • s)) ∂(∑ j, τ j)) =
        ∫⁻ t, G (t * bc s) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t * bc s * bc γ) ∂(∑ j, τ j) := by
    intro γ s
    obtain ⟨k, hk⟩ := γ.2
    refine lintegral_congr fun t => ?_
    have e1 : t * bc (γ • s) = t * bc s * bc γ := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul, mul_comm (bc γ) (bc s), mul_assoc]
    rw [e1, Set.indicator_apply, Set.indicator_apply]
    split_ifs with hmem
    · rw [mul_one, ← hk, hGinv k]
    · rw [mul_zero]
  simp_rw [hterm]
  have hpm : ∀ γ : ιK.range, Measurable fun s : (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ t, G (t * bc s) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t * bc s * bc γ) ∂(∑ j, τ j) := by
    intro γ
    exact (transfer Sτ τ cτ hmeas hmul hτ0 hτ2
      (fun y => G y * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ))
      (hG.mul ((measurable_const.indicator hΩm).comp (hmγ γ)))).1
  rw [← lintegral_tsum (fun γ => (hpm γ).aemeasurable)]
  have hinner : ∀ s : (AdeleRing (𝓞 K) K)ˣ,
      ∑' γ : ιK.range, ∫⁻ t, G (t * bc s) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t * bc s * bc γ) ∂(∑ j, τ j) =
        ∫⁻ t, G (t * bc s) * ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t * bc s * bc γ) ∂(∑ j, τ j) := by
    intro s
    rw [← lintegral_tsum (fun γ => ?_)]
    · exact lintegral_congr fun t => ENNReal.tsum_mul_left
    · exact ((hG.comp (hmt s)).mul ((measurable_const.indicator hΩm).comp ((hmγ γ).comp (hmt s)))).aemeasurable
  simp_rw [hinner]

  have hcntm : Measurable fun y : (AdeleRing (𝓞 L) L)ˣ =>
      ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) :=
    Measurable.ennreal_tsum fun γ => (measurable_const.indicator hΩm).comp (hmγ γ)
  have hbij : Function.Bijective (fun γ : ιK.range =>
      (⟨bc γ, by obtain ⟨k, hk⟩ := γ.2; exact ⟨k, by rw [MonoidHom.comp_apply, hk]⟩⟩ : (bc.comp ιK).range)) := by
    constructor
    · rintro ⟨γ₁, ⟨k₁, rfl⟩⟩ ⟨γ₂, ⟨k₂, rfl⟩⟩ h
      have h' : bc (ιK k₁) = bc (ιK k₂) := congrArg Subtype.val h
      have hk : k₁ = k₂ := idelesBaseChange_map_injective (K := K) (L := L) h'
      subst hk
      rfl
    · rintro ⟨g, ⟨k, rfl⟩⟩
      exact ⟨⟨ιK k, ⟨k, rfl⟩⟩, rfl⟩
  have hcov : ∀ᵐ y ∂(NumberField.Idele.idelicHaar L),
      ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) = 1 := by
    filter_upwards [tsum_indicator_smul_ae_eq_one hΩ] with y hy
    rw [← (Equiv.ofBijective _ hbij).tsum_eq (fun g => Ω.indicator (fun _ => (1 : ℝ≥0∞)) (g • y))] at hy
    refine (tsum_congr fun γ => ?_).trans hy
    rw [Subgroup.smul_def, smul_eq_mul]
    exact congrArg (Ω.indicator fun _ => (1 : ℝ≥0∞)) (mul_comm _ _)

  have hbadm : MeasurableSet {y : (AdeleRing (𝓞 L) L)ˣ |
      ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1} :=
    hcntm (measurableSet_singleton 1).compl
  have hbad0 : NumberField.Idele.idelicHaar L {y : (AdeleRing (𝓞 L) L)ˣ |
      ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcov] with y hy
    simpa using hy
  obtain ⟨hBm, hB⟩ := transfer Sτ τ cτ hmeas hmul hτ0 hτ2
    ({y : (AdeleRing (𝓞 L) L)ˣ | ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1}.indicator
      fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hbadm)
  have hle : ∫⁻ t in saturated K L Sτ, {y : (AdeleRing (𝓞 L) L)ˣ |
        ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1}.indicator (fun _ => (1 : ℝ≥0∞)) t
      ∂(NumberField.Idele.idelicHaar L) = 0 := by
    refine le_antisymm ?_ bot_le
    calc _ ≤ ∫⁻ t, {y : (AdeleRing (𝓞 L) L)ˣ |
        ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1}.indicator (fun _ => (1 : ℝ≥0∞)) t
          ∂(NumberField.Idele.idelicHaar L) := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = 0 := by rw [lintegral_indicator_const hbadm, hbad0, mul_zero]
  rw [hle] at hB
  have hB0 := (mul_eq_zero.1 hB.symm).resolve_left hc
  have hae : ∀ᵐ s ∂(NumberField.Idele.idelicHaar K), ∀ᵐ t ∂(∑ j, τ j),
      ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t * bc s * bc γ) = 1 := by
    have h1 := (lintegral_eq_zero_iff hBm).1 hB0
    filter_upwards [h1] with s hs
    have h2 := (lintegral_eq_zero_iff ((measurable_const.indicator hbadm).comp (hmt s))).1 hs
    filter_upwards [h2] with t ht
    change ({y : (AdeleRing (𝓞 L) L)ˣ | ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1}.indicator
      (fun _ => (1 : ℝ≥0∞)) (t * bc s)) = 0 at ht
    by_contra hne
    have h3 : ({y : (AdeleRing (𝓞 L) L)ˣ | ∑' γ : ιK.range, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (y * bc γ) ≠ 1}.indicator
        (fun _ => (1 : ℝ≥0∞)) (t * bc s)) = 1 := Set.indicator_of_mem hne _
    rw [h3] at ht
    exact one_ne_zero ht

  exact lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun s hs =>
    lintegral_congr_ae (hs.mono fun t ht => by simp only [ht, mul_one])))

end QT

namespace QT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem integrable_of_le_norm {α : Type*} [MeasurableSpace α] {ν : Measure α} {F : α → ℂ} {g : α → ℝ}
    (hF : Integrable F ν) (hg : Measurable g) (hg0 : ∀ t, 0 ≤ g t) (hgl : ∀ t, g t ≤ ‖F t‖) : Integrable g ν :=
  hF.norm.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (hg0 t)]; exact hgl t)

theorem clause2_nonneg
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L))
    (g : (AdeleRing (𝓞 L) L)ˣ → ℝ) (hg : Measurable g) (hg0 : ∀ t, 0 ≤ g t)
    (hginv : ∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      g (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) = g t)
    (hfin : ∫⁻ t in Ω ∩ saturated K L Sτ, ENNReal.ofReal (g t) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) :
    ∫ t in Ω ∩ saturated K L Sτ, g t ∂(NumberField.Idele.idelicHaar L) =
      cτ.toReal * ∫ s in ΩK, ∫ t, g (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) := by
  have hmt : ∀ s : (AdeleRing (𝓞 K) K)ˣ, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ => t * idelesBaseChange K L s :=
    fun s => (continuous_mul_const _).measurable
  have hGm : Measurable fun t => ENNReal.ofReal (g t) := hg.ennreal_ofReal
  have hc1 := clause1 Sτ τ cτ hmeas hmul hτ0 hτ2 ΩK hΩK Ω hΩm hΩ (fun t => ENNReal.ofReal (g t)) hGm
    (fun k t => by rw [hginv])
  have hIm := (transfer Sτ τ cτ hmeas hmul hτ0 hτ2 (fun t => ENNReal.ofReal (g t)) hGm).1
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable]
  have hinner : ∀ s : (AdeleRing (𝓞 K) K)ˣ, ∫ t, g (t * idelesBaseChange K L s) ∂(∑ j, τ j) =
      (∫⁻ t, ENNReal.ofReal (g (t * idelesBaseChange K L s)) ∂(∑ j, τ j)).toReal := fun s =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => hg0 _)
      (hg.comp (hmt s)).aestronglyMeasurable
  simp_rw [hinner]
  rw [hc1, ENNReal.toReal_mul]
  rcases eq_or_ne cτ 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne cτ ⊤ with ht | ht
  · simp [ht]
  congr 1
  have hY : ∫⁻ s in ΩK, ∫⁻ t, ENNReal.ofReal (g (t * idelesBaseChange K L s)) ∂(∑ j, τ j)
      ∂(NumberField.Idele.idelicHaar K) ≠ ⊤ := by
    intro hY
    apply hfin
    rw [hc1, hY, ENNReal.mul_top h0]
  exact (integral_toReal hIm.aemeasurable (ae_lt_top hIm hY)).symm

theorem clause2
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L))
    (F : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hF : Measurable F)
    (hFinv : ∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      F (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) = F t)
    (hfin : ∫⁻ t in Ω ∩ saturated K L Sτ, ‖F t‖ₑ ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) :
    ∫ t in Ω ∩ saturated K L Sτ, F t ∂(NumberField.Idele.idelicHaar L) =
      (cτ.toReal : ℂ) *
        ∫ s in ΩK, ∫ t, F (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) := by
  have hmt : ∀ s : (AdeleRing (𝓞 K) K)ˣ, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ => t * idelesBaseChange K L s :=
    fun s => (continuous_mul_const _).measurable

  set g₁ : (AdeleRing (𝓞 L) L)ˣ → ℝ := fun t => max (F t).re 0 with hg₁
  set g₂ : (AdeleRing (𝓞 L) L)ˣ → ℝ := fun t => max (-(F t).re) 0 with hg₂
  set g₃ : (AdeleRing (𝓞 L) L)ˣ → ℝ := fun t => max (F t).im 0 with hg₃
  set g₄ : (AdeleRing (𝓞 L) L)ˣ → ℝ := fun t => max (-(F t).im) 0 with hg₄
  have hre : Measurable fun t => (F t).re := Complex.measurable_re.comp hF
  have him : Measurable fun t => (F t).im := Complex.measurable_im.comp hF
  have hg₁m : Measurable g₁ := hre.max measurable_const
  have hg₂m : Measurable g₂ := hre.neg.max measurable_const
  have hg₃m : Measurable g₃ := him.max measurable_const
  have hg₄m : Measurable g₄ := him.neg.max measurable_const

  have hle : ∀ t, g₁ t ≤ ‖F t‖ ∧ g₂ t ≤ ‖F t‖ ∧ g₃ t ≤ ‖F t‖ ∧ g₄ t ≤ ‖F t‖ := by
    intro t
    refine ⟨max_le ((le_abs_self _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _),
      max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _),
      max_le ((le_abs_self _).trans (Complex.abs_im_le_norm _)) (norm_nonneg _),
      max_le ((neg_le_abs _).trans (Complex.abs_im_le_norm _)) (norm_nonneg _)⟩
  have hfin' : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℝ, (∀ t, g t ≤ ‖F t‖) →
      ∫⁻ t in Ω ∩ saturated K L Sτ, ENNReal.ofReal (g t) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤ := by
    intro g hgl htop
    apply hfin
    refine eq_top_iff.mpr (le_trans (eq_top_iff.mp htop) (lintegral_mono fun t => ?_))
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hgl t)

  have P := fun (g : (AdeleRing (𝓞 L) L)ˣ → ℝ) (hg : Measurable g) (hg0 : ∀ t, 0 ≤ g t)
      (hginv : ∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        g (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) = g t)
      (hgl : ∀ t, g t ≤ ‖F t‖) =>
    clause2_nonneg Sτ τ cτ hmeas hmul hτ0 hτ2 ΩK hΩK Ω hΩm hΩ g hg hg0 hginv (hfin' g hgl)
  have P₁ := P g₁ hg₁m (fun t => le_max_right _ _) (fun k t => by simp only [hg₁, hFinv]) (fun t => (hle t).1)
  have P₂ := P g₂ hg₂m (fun t => le_max_right _ _) (fun k t => by simp only [hg₂, hFinv]) (fun t => (hle t).2.1)
  have P₃ := P g₃ hg₃m (fun t => le_max_right _ _) (fun k t => by simp only [hg₃, hFinv]) (fun t => (hle t).2.2.1)
  have P₄ := P g₄ hg₄m (fun t => le_max_right _ _) (fun k t => by simp only [hg₄, hFinv]) (fun t => (hle t).2.2.2)

  have hFint : Integrable F ((NumberField.Idele.idelicHaar L).restrict (Ω ∩ saturated K L Sτ)) :=
    ⟨hF.aestronglyMeasurable, lt_top_iff_ne_top.mpr hfin⟩
  have hI₁ : Integrable g₁ ((NumberField.Idele.idelicHaar L).restrict (Ω ∩ saturated K L Sτ)) := integrable_of_le_norm hFint hg₁m (fun t => le_max_right _ _) (fun t => (hle t).1)
  have hI₂ : Integrable g₂ ((NumberField.Idele.idelicHaar L).restrict (Ω ∩ saturated K L Sτ)) := integrable_of_le_norm hFint hg₂m (fun t => le_max_right _ _) (fun t => (hle t).2.1)
  have hI₃ : Integrable g₃ ((NumberField.Idele.idelicHaar L).restrict (Ω ∩ saturated K L Sτ)) := integrable_of_le_norm hFint hg₃m (fun t => le_max_right _ _) (fun t => (hle t).2.2.1)
  have hI₄ : Integrable g₄ ((NumberField.Idele.idelicHaar L).restrict (Ω ∩ saturated K L Sτ)) := integrable_of_le_norm hFint hg₄m (fun t => le_max_right _ _) (fun t => (hle t).2.2.2)
  have hLre : ∫ t in Ω ∩ saturated K L Sτ, (F t).re ∂(NumberField.Idele.idelicHaar L) = (∫ t in Ω ∩ saturated K L Sτ, g₁ t ∂(NumberField.Idele.idelicHaar L)) - ∫ t in Ω ∩ saturated K L Sτ, g₂ t ∂(NumberField.Idele.idelicHaar L) := by
    rw [← integral_sub hI₁ hI₂]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => (max_zero_sub_max_neg_zero_eq_self _).symm)
  have hLim : ∫ t in Ω ∩ saturated K L Sτ, (F t).im ∂(NumberField.Idele.idelicHaar L) = (∫ t in Ω ∩ saturated K L Sτ, g₃ t ∂(NumberField.Idele.idelicHaar L)) - ∫ t in Ω ∩ saturated K L Sτ, g₄ t ∂(NumberField.Idele.idelicHaar L) := by
    rw [← integral_sub hI₃ hI₄]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => (max_zero_sub_max_neg_zero_eq_self _).symm)
  have hL : ∫ t in Ω ∩ saturated K L Sτ, F t ∂(NumberField.Idele.idelicHaar L) =
      (((∫ t in Ω ∩ saturated K L Sτ, g₁ t ∂(NumberField.Idele.idelicHaar L)) - ∫ t in Ω ∩ saturated K L Sτ, g₂ t ∂(NumberField.Idele.idelicHaar L) : ℝ) : ℂ) +
        (((∫ t in Ω ∩ saturated K L Sτ, g₃ t ∂(NumberField.Idele.idelicHaar L)) - ∫ t in Ω ∩ saturated K L Sτ, g₄ t ∂(NumberField.Idele.idelicHaar L) : ℝ) : ℂ) * Complex.I := by
    have key := integral_re_add_im hFint
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at key
    rw [hLre, hLim] at key
    exact key.symm
  rw [hL, P₁, P₂, P₃, P₄]

  rcases eq_or_ne cτ.toReal 0 with hc0 | hc0
  · simp [hc0]
  have hcτ0 : cτ ≠ 0 := fun h => hc0 (by simp [h])
  have hcτt : cτ ≠ ⊤ := fun h => hc0 (by simp [h])

  obtain ⟨hNm, -⟩ := transfer Sτ τ cτ hmeas hmul hτ0 hτ2 (fun t => ‖F t‖ₑ) hF.enorm
  have hN := clause1 Sτ τ cτ hmeas hmul hτ0 hτ2 ΩK hΩK Ω hΩm hΩ (fun t => ‖F t‖ₑ) hF.enorm
    (fun k t => by rw [hFinv])
  have hYN : ∫⁻ s in ΩK, ∫⁻ t, ‖F (t * idelesBaseChange K L s)‖ₑ ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) ≠ ⊤ := by
    intro hY
    apply hfin
    show ∫⁻ t in Ω ∩ saturated K L Sτ, ‖F t‖ₑ ∂(NumberField.Idele.idelicHaar L) = ⊤
    rw [hN]
    show cτ * ∫⁻ s in ΩK, ∫⁻ t, ‖F (t * idelesBaseChange K L s)‖ₑ ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) = ⊤
    rw [hY, ENNReal.mul_top hcτ0]
  have hae : ∀ᵐ s ∂((NumberField.Idele.idelicHaar K).restrict ΩK), ∫⁻ t, ‖F (t * idelesBaseChange K L s)‖ₑ ∂(∑ j, τ j) < ⊤ := ae_lt_top hNm hYN

  have hφint : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℝ, Measurable g → (∀ t, 0 ≤ g t) → (∀ t, g t ≤ ‖F t‖) →
      Integrable (fun s => ∫ t, g (t * idelesBaseChange K L s) ∂(∑ j, τ j)) ((NumberField.Idele.idelicHaar K).restrict ΩK) := by
    intro g hg hg0 hgl
    have hGm : Measurable fun t => ENNReal.ofReal (g t) := hg.ennreal_ofReal
    have hIm := (transfer Sτ τ cτ hmeas hmul hτ0 hτ2 (fun t => ENNReal.ofReal (g t)) hGm).1
    have heq : (fun s => ∫ t, g (t * idelesBaseChange K L s) ∂(∑ j, τ j)) =
        fun s => (∫⁻ t, ENNReal.ofReal (g (t * idelesBaseChange K L s)) ∂(∑ j, τ j)).toReal := by
      funext s
      exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => hg0 _)
        (hg.comp (hmt s)).aestronglyMeasurable
    rw [heq]
    refine integrable_toReal_of_lintegral_ne_top hIm.aemeasurable ?_
    refine ne_top_of_le_ne_top hYN (lintegral_mono fun s => lintegral_mono fun t => ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hgl _)
  have hφ₁ := hφint g₁ hg₁m (fun t => le_max_right _ _) (fun t => (hle t).1)
  have hφ₂ := hφint g₂ hg₂m (fun t => le_max_right _ _) (fun t => (hle t).2.1)
  have hφ₃ := hφint g₃ hg₃m (fun t => le_max_right _ _) (fun t => (hle t).2.2.1)
  have hφ₄ := hφint g₄ hg₄m (fun t => le_max_right _ _) (fun t => (hle t).2.2.2)

  have hΦ : ∀ᵐ s ∂((NumberField.Idele.idelicHaar K).restrict ΩK), ∫ t, F (t * idelesBaseChange K L s) ∂(∑ j, τ j) =
      (((∫ t, g₁ (t * idelesBaseChange K L s) ∂(∑ j, τ j)) - ∫ t, g₂ (t * idelesBaseChange K L s) ∂(∑ j, τ j) : ℝ) : ℂ) +
        (((∫ t, g₃ (t * idelesBaseChange K L s) ∂(∑ j, τ j)) - ∫ t, g₄ (t * idelesBaseChange K L s) ∂(∑ j, τ j) : ℝ) : ℂ) * Complex.I := by
    filter_upwards [hae] with s hs
    have hint : Integrable (fun t => F (t * idelesBaseChange K L s)) (∑ j, τ j) :=
      ⟨(hF.comp (hmt s)).aestronglyMeasurable, hs⟩
    have j₁ : Integrable (fun t => g₁ (t * idelesBaseChange K L s)) (∑ j, τ j) :=
      integrable_of_le_norm hint (hg₁m.comp (hmt s)) (fun t => le_max_right _ _) (fun t => (hle _).1)
    have j₂ : Integrable (fun t => g₂ (t * idelesBaseChange K L s)) (∑ j, τ j) :=
      integrable_of_le_norm hint (hg₂m.comp (hmt s)) (fun t => le_max_right _ _) (fun t => (hle _).2.1)
    have j₃ : Integrable (fun t => g₃ (t * idelesBaseChange K L s)) (∑ j, τ j) :=
      integrable_of_le_norm hint (hg₃m.comp (hmt s)) (fun t => le_max_right _ _) (fun t => (hle _).2.2.1)
    have j₄ : Integrable (fun t => g₄ (t * idelesBaseChange K L s)) (∑ j, τ j) :=
      integrable_of_le_norm hint (hg₄m.comp (hmt s)) (fun t => le_max_right _ _) (fun t => (hle _).2.2.2)
    have h1 : ∫ t, (F (t * idelesBaseChange K L s)).re ∂(∑ j, τ j) =
        (∫ t, g₁ (t * idelesBaseChange K L s) ∂(∑ j, τ j)) - ∫ t, g₂ (t * idelesBaseChange K L s) ∂(∑ j, τ j) := by
      rw [← integral_sub j₁ j₂]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => (max_zero_sub_max_neg_zero_eq_self _).symm)
    have h2 : ∫ t, (F (t * idelesBaseChange K L s)).im ∂(∑ j, τ j) =
        (∫ t, g₃ (t * idelesBaseChange K L s) ∂(∑ j, τ j)) - ∫ t, g₄ (t * idelesBaseChange K L s) ∂(∑ j, τ j) := by
      rw [← integral_sub j₃ j₄]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => (max_zero_sub_max_neg_zero_eq_self _).symm)
    have key := integral_re_add_im hint
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at key
    rw [h1, h2] at key
    exact key.symm
  rw [integral_congr_ae hΦ, integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sub hφ₁ hφ₂, integral_sub hφ₃ hφ₄]
  · push_cast
    ring
  · exact (hφ₁.sub hφ₂).ofReal
  · exact ((hφ₃.sub hφ₄).ofReal).mul_const _

end QT

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j)) (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L)) :
    (∀ G : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞, Measurable G →
      (∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        G (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) =
          G t) →
      ∫⁻ t in Ω ∩ saturated K L Sτ, G t ∂(NumberField.Idele.idelicHaar L) =
        cτ * ∫⁻ s in ΩK, ∫⁻ t, G (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) ∧
    (∀ F : (AdeleRing (𝓞 L) L)ˣ → ℂ, Measurable F →
      (∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        F (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) =
          F t) →
      (∫⁻ t in Ω ∩ saturated K L Sτ, ‖F t‖ₑ ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) →
      ∫ t in Ω ∩ saturated K L Sτ, F t ∂(NumberField.Idele.idelicHaar L) =
        (cτ.toReal : ℂ) *
          ∫ s in ΩK, ∫ t, F (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) :=
  ⟨fun G hG hGinv => QT.clause1 Sτ τ cτ hmeas hmul hτ0 hτ2 ΩK hΩK Ω hΩm hΩ G hG hGinv,
    fun F hF hFinv hfin => QT.clause2 Sτ τ cτ hmeas hmul hτ0 hτ2 ΩK hΩK Ω hΩm hΩ F hF hFinv hfin⟩

end S_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
end P2MW
export P2MW.S_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal (solution)
