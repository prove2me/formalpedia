-- Prove2me | solution 1 for AutomorphicForm.isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/dc8b3971-ebba-502c-b962-bd5a0b631e84

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

section Commutant

variable {R : Type*} [CommRing R]

private theorem exists_eq_smul_one_add_smul_of_commute (g m : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) :
    ∃ x y : R, m = x • (1 : Matrix (Fin 2) (Fin 2) R) + y • g := by
  obtain ⟨u, hu⟩ := hg
  have hinv : (↑u⁻¹ : R) * ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) = 1 := by
    have h := u.inv_mul
    rwa [hu, Matrix.trace_fin_two, Matrix.det_fin_two] at h
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨m 0 0 - (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)) * g 0 0,
    (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, if_true, if_false, mul_one, mul_zero, zero_add, one_ne_zero,
    zero_ne_one]
  · ring
  · linear_combination (-(m 0 1)) * hinv + (-((↑u⁻¹ : R) * (g 0 0 - g 1 1))) * h01 + (2 * (↑u⁻¹ : R) * g 0 1) * h00
  · linear_combination (-(m 1 0)) * hinv + ((↑u⁻¹ : R) * (g 0 0 - g 1 1)) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h00
  · linear_combination (m 0 0 - m 1 1) * hinv + (2 * (↑u⁻¹ : R) * g 0 1) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h01

private theorem commute_of_commute_of_commute {g m m' : Matrix (Fin 2) (Fin 2) R}
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) (hm' : m' * g = g * m') : m * m' = m' * m := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m hg hm
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m' hg hm'
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

private theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) R} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (s t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) : s * t = t * s := by
  have hs : ((s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (γ : Matrix (Fin 2) (Fin 2) R) =
      (γ : Matrix (Fin 2) (Fin 2) R) * ((s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_iff.1 s.2) γ rfl]
  have ht : ((t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (γ : Matrix (Fin 2) (Fin 2) R) =
      (γ : Matrix (Fin 2) (Fin 2) R) * ((t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_iff.1 t.2) γ rfl]
  exact Subtype.ext (Units.ext (commute_of_commute_of_commute hγ hs ht))

end Commutant

section IntegralUnits

variable {A : Type*} [CommRing A]

private theorem mul_mem_integralUnitsSet {S : Type*} [SetLike S A] [SubringClass S A] (R : S) {g h : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (R : Set A)) (hh : h ∈ AutomorphicForm.integralUnitsSet (R : Set A)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (R : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hh.2 i k) (hg.2 k j)

private theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet U) :
    g⁻¹ ∈ AutomorphicForm.integralUnitsSet U :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

end IntegralUnits

section SectionFunction

open MeasureTheory
open scoped ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_section_of_forall_eq_of_forall_exists (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (hUo : IsOpen U) (hUc : IsCompact U) (hμU : μ U = 1) (h1U : (1 : G) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
    (hUinv : ∀ a ∈ U, a⁻¹ ∈ U) (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure] (ψ : G → ℂ)
    (hψ : ∀ t ∈ T, ∀ x : G, ∀ u ∈ U, ψ (t * x * u) = ψ x) (S : Finset G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hcov : ∀ x, ψ x ≠ 0 → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, ψ x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∫ x, ψ x * (w x : ℂ) ∂μ = ∑ s ∈ S, ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ) := by
  classical
  have hTemb : Topology.IsClosedEmbedding ((↑) : T → G) := hT.isClosedEmbedding_subtypeVal

  have hst : ∀ s : G,
      IsOpen {t : T | s⁻¹ * (t : G) * s ∈ U} ∧ IsCompact {t : T | s⁻¹ * (t : G) * s ∈ U} := by
    intro s
    have hφ : IsCompact ((fun y : G => s⁻¹ * y * s) ⁻¹' U) :=
      ((Homeomorph.mulLeft s⁻¹).trans (Homeomorph.mulRight s)).isCompact_preimage.2 hUc
    exact ⟨hUo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const),
      hTemb.isCompact_preimage hφ⟩
  have hm : ∀ s : G, 0 < (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal := fun s =>
    ENNReal.toReal_pos ((hst s).1.measure_ne_zero τ ⟨1, by simpa using h1U⟩) (hst s).2.measure_lt_top.ne

  have hA : ∀ s : G, MeasurableSet {y : G | s⁻¹ * y ∈ U} ∧ μ {y : G | s⁻¹ * y ∈ U} = 1 ∧
      IsCompact {y : G | s⁻¹ * y ∈ U} := fun s =>
    ⟨(hUo.preimage (continuous_const.mul continuous_id)).measurableSet, (measure_preimage_mul μ s⁻¹ U).trans hμU,
      (Homeomorph.mulLeft s⁻¹).isCompact_preimage.2 hUc⟩
  have hψA : ∀ s y : G, s⁻¹ * y ∈ U → ψ y = ψ s := fun s y hy => by
    have h := hψ 1 T.one_mem s (s⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  refine ⟨fun y => ∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
      (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) y, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun y => Finset.sum_nonneg fun s _ =>
      Set.indicator_nonneg (fun _ _ => inv_nonneg.2 ENNReal.toReal_nonneg) _
  · exact Finset.measurable_sum _ fun s _ => measurable_const.indicator (hA s).1
  · refine HasCompactSupport.intro (S.isCompact_biUnion fun s _ => (hA s).2.2) fun y hy => ?_
    exact Finset.sum_eq_zero fun s hs =>
      Set.indicator_of_notMem (fun hys => hy (Set.mem_iUnion₂.2 ⟨s, hs, hys⟩)) _
  ·
    intro x hx
    obtain ⟨s₀, hs₀, t₀, ht₀, u₀, hu₀, rfl⟩ := hcov x hx
    have hsum : ∀ t : T,
        (∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹)
          ((t : G) * (t₀ * s₀ * u₀))) =
        ((fun t' : T => t' * ⟨t₀, ht₀⟩) ⁻¹' {t' : T | s₀⁻¹ * (t' : G) * s₀ ∈ U}).indicator
          (fun _ => (τ {t : T | s₀⁻¹ * (t : G) * s₀ ∈ U}).toReal⁻¹) t := by
      intro t
      have h0 : ∀ s ∈ S, s ≠ s₀ → {y : G | s⁻¹ * y ∈ U}.indicator
          (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) ((t : G) * (t₀ * s₀ * u₀)) = 0 := by
        intro s hs hne
        refine Set.indicator_of_notMem (fun h => hne ?_) _
        have h' : s⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) ∈ U := h
        exact hS s₀ hs₀ s hs ((t : G) * t₀) (T.mul_mem t.2 ht₀) (u₀ * (s⁻¹ * ((t : G) * (t₀ * s₀ * u₀)))⁻¹)
          (hUmul _ hu₀ _ (hUinv _ h')) (by group)
      rw [Finset.sum_eq_single_of_mem s₀ hs₀ h0]
      by_cases h : s₀⁻¹ * ((t : G) * t₀) * s₀ ∈ U
      · have h' : (t : G) * (t₀ * s₀ * u₀) ∈ {y : G | s₀⁻¹ * y ∈ U} := by
          have e : s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) = s₀⁻¹ * ((t : G) * t₀) * s₀ * u₀ := by group
          rw [Set.mem_setOf_eq, e]
          exact hUmul _ h _ hu₀
        rw [Set.indicator_of_mem h', Set.indicator_of_mem]
        simpa using h
      · have h' : (t : G) * (t₀ * s₀ * u₀) ∉ {y : G | s₀⁻¹ * y ∈ U} :=
          fun (h' : s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) ∈ U) => h (by
            have e : s₀⁻¹ * ((t : G) * t₀) * s₀ = s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) * u₀⁻¹ := by group
            rw [e]
            exact hUmul _ h' _ (hUinv _ hu₀))
        rw [Set.indicator_of_notMem h', Set.indicator_of_notMem]
        simpa using h
    have hmeas : MeasurableSet
        ((fun t' : T => t' * ⟨t₀, ht₀⟩) ⁻¹' {t' : T | s₀⁻¹ * (t' : G) * s₀ ∈ U}) :=
      (hst s₀).1.measurableSet.preimage (measurable_mul_const _)
    simp only [hsum]
    rw [integral_indicator_const _ hmeas, measureReal_def, measure_preimage_mul_right, smul_eq_mul,
      mul_inv_cancel₀ (hm s₀).ne']
  ·
    have hpt : ∀ y : G,
        ψ y * ((∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
          (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) y : ℝ) : ℂ) =
        ∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
          (fun _ => ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)) y := by
      intro y
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hy : y ∈ {y : G | s⁻¹ * y ∈ U}
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hψA s y hy, Complex.ofReal_inv, div_eq_mul_inv]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, Complex.ofReal_zero, mul_zero]
    have hint : ∀ s ∈ S, Integrable ({y : G | s⁻¹ * y ∈ U}.indicator
        fun _ => ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)) μ := fun s _ =>
      (integrableOn_const (hs := by rw [(hA s).2.1]; exact ENNReal.one_ne_top)).integrable_indicator (hA s).1
    simp only [hpt]
    rw [integral_finsetSum S hint]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_indicator_const _ (hA s).1, measureReal_def, (hA s).2.1, ENNReal.toReal_one, one_smul]

end SectionFunction

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ AutomorphicForm.localIntegralSet K v, ∀ u₂ ∈ AutomorphicForm.localIntegralSet K v,
        f (u₁ * g * u₂) = f g)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ f
      (∑ s ∈ S, f (s⁻¹ * γ * s) /
        ((τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈
            AutomorphicForm.localIntegralSet K v}).toReal : ℂ)) := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := glBorelOf (v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_glBorelOf _
  haveI := borelSpace_localGLBorel K v
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :=
    centralizerBorel (v.adicCompletion K) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ := hτ
  haveI := isHaarMeasure_localHaar K v

  haveI : τ.IsMulRightInvariant := ⟨fun t => by
    rw [show (fun s => s * t) = fun s => t * s from funext fun s => mul_comm_of_mem_centralizer hγ s t]
    exact map_mul_left_eq_self τ t⟩

  have hT : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K)))) := by
    have h : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :
        Set (GL (Fin 2) (v.adicCompletion K)))) = {t | γ * t = t * γ} := by
      ext t
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      exact ⟨fun h' => h' γ rfl, fun h' g hg => by rw [Set.mem_singleton_iff.1 hg]; exact h'⟩
    rw [h]
    exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

  have hψ : ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      ∀ x : GL (Fin 2) (v.adicCompletion K), ∀ u ∈ localIntegralSet K v,
        f ((t * x * u)⁻¹ * γ * (t * x * u)) = f (x⁻¹ * γ * x) := by
    intro t ht x u hu
    have htγ : γ * t = t * γ := (Subgroup.mem_centralizer_iff.1 ht) γ rfl
    have e : (t * x * u)⁻¹ * γ * (t * x * u) = u⁻¹ * (x⁻¹ * (t⁻¹ * (γ * t)) * x) * u := by group
    rw [e, htγ, inv_mul_cancel_left]
    exact hf (x⁻¹ * γ * x) u⁻¹ (inv_mem_integralUnitsSet _ hu) u hu
  obtain ⟨w, h0, hw, hcpt, hsec, hint⟩ := exists_section_of_forall_eq_of_forall_exists (localHaar K v)
    (localIntegralSet K v) (isOpen_localIntegralSet K v) (isCompact_localIntegralSet K v)
    (localHaar_localIntegralSet K v) (one_mem_localIntegralSet K v)
    (fun a ha b hb => mul_mem_integralUnitsSet (v.adicCompletionIntegers K) ha hb)
    (fun a ha => inv_mem_integralUnitsSet _ ha)
    (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) hT τ (fun x => f (x⁻¹ * γ * x)) hψ S hS
    hcov
  exact ⟨w, ⟨h0, hw, hcpt, hsec⟩, hint.symm⟩

end S_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
end P2MW
export P2MW.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists (solution)
