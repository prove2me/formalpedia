-- Prove2me | solution 1 for AntonelliBFSDE.BackwardForward.lipschitz_estimates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:26:56.492118+00:00
-- url     : https://prove2.me/submissions/b095366c-364d-4e8e-8648-248a61ee503f

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal
open MeasureTheory Filter Topology

namespace AntonelliBFSDE.BackwardForward

/-! ### Stieltjes measures of right-continuous monotone paths -/

lemma d35_rc_real (c : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt c (Set.Ici t) t) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => c y.toNNReal) (Set.Ici x) x := by
  have h1 : ContinuousWithinAt (fun y : ℝ => y.toNNReal) (Set.Ici x) x :=
    continuous_real_toNNReal.continuousAt.continuousWithinAt
  exact (hrc x.toNNReal).comp h1 (fun y hy => Real.toNNReal_le_toNNReal hy)

lemma d35_stj_apply (c : ℝ≥0 → ℝ) (h : Monotone (fun x : ℝ => c x.toNNReal))
    (hrc : ∀ t, ContinuousWithinAt c (Set.Ici t) t) (x : ℝ) :
    h.stieltjesFunction x = c x.toNNReal := by
  rw [Monotone.stieltjesFunction_eq]
  have := (d35_rc_real c hrc x).mono (Set.Ioi_subset_Ici_self)
  exact (h.continuousWithinAt_Ioi_iff_rightLim_eq).1 this

lemma d35_stj_Ioc (c : ℝ≥0 → ℝ) (h : Monotone (fun x : ℝ => c x.toNNReal))
    (hrc : ∀ t, ContinuousWithinAt c (Set.Ici t) t) (u v : ℝ) :
    h.stieltjesFunction.measure (Set.Ioc u v) = ENNReal.ofReal (c v.toNNReal - c u.toNNReal) := by
  rw [StieltjesFunction.measure_Ioc, d35_stj_apply c h hrc, d35_stj_apply c h hrc]

lemma d35_restrict_Ioc_apply (μ : Measure ℝ) (T : ℝ≥0) (u v : ℝ) :
    (μ.restrict (Set.Ioc 0 (T:ℝ))) (Set.Ioc u v) = μ (Set.Ioc (max u 0) (min v T)) := by
  rw [Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc]

lemma d35_kernel_meas {Ω : Type*} [MeasurableSpace Ω] (c : ℝ≥0 → Ω → ℝ)
    (h : ∀ ω, Monotone (fun x : ℝ => c x.toNNReal ω))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => c s ω) (Set.Ici t) t)
    (hmeas : ∀ t, Measurable (c t)) (T : ℝ≥0) :
    Measurable (fun ω => ((h ω).stieltjesFunction.measure).restrict (Set.Ioc 0 (T:ℝ))) := by
  have : ∀ ω, IsFiniteMeasure (((h ω).stieltjesFunction.measure).restrict (Set.Ioc 0 (T:ℝ))) :=
    fun ω => isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  refine Measurable.measure_of_isPiSystem (S := {S | ∃ l u : ℝ, l < u ∧ Set.Ioc l u = S})
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ))
    (isPiSystem_Ioc (id : ℝ → ℝ) id) ?_ ?_
  · rintro _ ⟨l, u, -, rfl⟩
    simp_rw [d35_restrict_Ioc_apply, d35_stj_Ioc _ (h _) (hrc _)]
    exact ENNReal.measurable_ofReal.comp ((hmeas _).sub (hmeas _))
  · simp_rw [Measure.restrict_apply_univ, d35_stj_Ioc _ (h _) (hrc _)]
    exact ENNReal.measurable_ofReal.comp ((hmeas _).sub (hmeas _))

/-- The finite kernel `ω ↦ dc(ω)|_(0,T]`. -/
noncomputable def d35_ker {Ω : Type*} [MeasurableSpace Ω] (c : ℝ≥0 → Ω → ℝ)
    (h : ∀ ω, Monotone (fun x : ℝ => c x.toNNReal ω))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => c s ω) (Set.Ici t) t)
    (hmeas : ∀ t, Measurable (c t)) (T : ℝ≥0) : ProbabilityTheory.Kernel Ω ℝ :=
  ⟨fun ω => ((h ω).stieltjesFunction.measure).restrict (Set.Ioc 0 (T:ℝ)),
    d35_kernel_meas c h hrc hmeas T⟩

lemma d35_ker_finite {Ω : Type*} [MeasurableSpace Ω] (c : ℝ≥0 → Ω → ℝ)
    (h : ∀ ω, Monotone (fun x : ℝ => c x.toNNReal ω))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => c s ω) (Set.Ici t) t)
    (hmeas : ∀ t, Measurable (c t)) (T : ℝ≥0) (B : ℝ) (hB : ∀ ω, c T ω - c 0 ω ≤ B) :
    ProbabilityTheory.IsFiniteKernel (d35_ker c h hrc hmeas T) := by
  refine ⟨⟨ENNReal.ofReal B, ENNReal.ofReal_lt_top, fun ω => ?_⟩⟩
  simp only [d35_ker, ProbabilityTheory.Kernel.coe_mk, Measure.restrict_apply_univ]
  rw [d35_stj_Ioc _ (h ω) (hrc ω)]
  simpa using ENNReal.ofReal_le_ofReal (hB ω)

lemma d35_meas_lintegral {Ω : Type*} [MeasurableSpace Ω] (c : ℝ≥0 → Ω → ℝ)
    (h : ∀ ω, Monotone (fun x : ℝ => c x.toNNReal ω))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => c s ω) (Set.Ici t) t)
    (hmeas : ∀ t, Measurable (c t)) (T : ℝ≥0) (B : ℝ) (hB : ∀ ω, c T ω - c 0 ω ≤ B)
    (F : Ω → ℝ → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) (s t : ℝ≥0) (ht : t ≤ T) :
    Measurable (fun ω => ∫⁻ r in Set.Ioc (s:ℝ) t, F ω r ∂(h ω).stieltjesFunction.measure) := by
  have := d35_ker_finite c h hrc hmeas T B hB
  have key : ∀ ω, ∫⁻ r in Set.Ioc (s:ℝ) t, F ω r ∂(h ω).stieltjesFunction.measure =
      ∫⁻ r, (Set.Ioc (s:ℝ) t).indicator (F ω) r ∂(d35_ker c h hrc hmeas T ω) := by
    intro ω
    rw [lintegral_indicator measurableSet_Ioc]
    simp only [d35_ker, ProbabilityTheory.Kernel.coe_mk]
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    exact (Set.inter_eq_left.2 (Set.Ioc_subset_Ioc (by simp) (by exact_mod_cast ht))).symm
  simp_rw [key]
  apply Measurable.lintegral_kernel_prod_right
  have : Function.uncurry (fun ω r => (Set.Ioc (s:ℝ) t).indicator (F ω) r) =
      (Prod.snd ⁻¹' Set.Ioc (s:ℝ) t).indicator (Function.uncurry F) := by
    ext ⟨ω, r⟩; simp [Set.indicator]
  rw [this]
  exact hF.indicator (measurable_snd measurableSet_Ioc)

lemma d35_meas_integral {Ω : Type*} [MeasurableSpace Ω] (c : ℝ≥0 → Ω → ℝ)
    (h : ∀ ω, Monotone (fun x : ℝ => c x.toNNReal ω))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => c s ω) (Set.Ici t) t)
    (hmeas : ∀ t, Measurable (c t)) (T : ℝ≥0) (B : ℝ) (hB : ∀ ω, c T ω - c 0 ω ≤ B)
    (F : Ω → ℝ → ℝ) (hF : Measurable (Function.uncurry F)) (s t : ℝ≥0) (ht : t ≤ T) :
    StronglyMeasurable (fun ω => ∫ r in Set.Ioc (s:ℝ) t, F ω r ∂(h ω).stieltjesFunction.measure) := by
  have := d35_ker_finite c h hrc hmeas T B hB
  have key : ∀ ω, ∫ r in Set.Ioc (s:ℝ) t, F ω r ∂(h ω).stieltjesFunction.measure =
      ∫ r, (Set.Ioc (s:ℝ) t).indicator (F ω) r ∂(d35_ker c h hrc hmeas T ω) := by
    intro ω
    rw [integral_indicator measurableSet_Ioc]
    simp only [d35_ker, ProbabilityTheory.Kernel.coe_mk]
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    exact (Set.inter_eq_left.2 (Set.Ioc_subset_Ioc (by simp) (by exact_mod_cast ht))).symm
  simp_rw [key]
  apply StronglyMeasurable.integral_kernel_prod_right
  have : Function.uncurry (fun ω r => (Set.Ioc (s:ℝ) t).indicator (F ω) r) =
      (Prod.snd ⁻¹' Set.Ioc (s:ℝ) t).indicator (Function.uncurry F) := by
    ext ⟨ω, r⟩; simp [Set.indicator]
  rw [this]
  exact (hF.indicator (measurable_snd measurableSet_Ioc)).stronglyMeasurable


/-! ### Domination -/

lemma d35_dom (T : ℝ≥0) (a b d : ℝ≥0 → ℝ) (ha : Monotone (fun x : ℝ => a x.toNNReal))
    (hb : Monotone (fun x : ℝ => b x.toNNReal)) (hd : Monotone (fun x : ℝ => d x.toNNReal))
    (hra : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (hrb : ∀ t, ContinuousWithinAt b (Set.Ici t) t)
    (hrd : ∀ t, ContinuousWithinAt d (Set.Ici t) t)
    (hmon : MonotoneOn (fun t => d t - (a t + b t)) (Set.Icc 0 T)) :
    (ha.stieltjesFunction.measure + hb.stieltjesFunction.measure).restrict (Set.Ioc 0 (T:ℝ)) ≤
      hd.stieltjesFunction.measure.restrict (Set.Ioc 0 (T:ℝ)) := by
  set m : ℝ → ℝ≥0 := fun x => min x.toNNReal T with hm
  have hmm : Monotone m := fun x y hxy => min_le_min_right _ (Real.toNNReal_le_toNNReal hxy)
  have hmI : ∀ x, m x ∈ Set.Icc 0 T := fun x => ⟨zero_le, min_le_right _ _⟩
  let e : ℝ → ℝ := fun x => d (m x) - (a (m x) + b (m x))
  have he : Monotone e := fun x y hxy => hmon (hmI x) (hmI y) (hmm hxy)
  have hmc : ∀ x, ContinuousWithinAt m (Set.Ici x) x := fun x =>
    ((continuous_real_toNNReal.min continuous_const).continuousAt).continuousWithinAt
  have hre : ∀ x, ContinuousWithinAt e (Set.Ici x) x := by
    intro x
    have hmap : Set.MapsTo m (Set.Ici x) (Set.Ici (m x)) := fun y hy => hmm hy
    exact ((hrd (m x)).comp (hmc x) hmap).sub
      (((hra (m x)).comp (hmc x) hmap).add ((hrb (m x)).comp (hmc x) hmap))
  let E : StieltjesFunction ℝ := ⟨e, he, hre⟩
  have key : ∀ p q : ℝ, 0 ≤ p → q ≤ T →
      hd.stieltjesFunction.measure (Set.Ioc p q) =
        (ha.stieltjesFunction.measure + hb.stieltjesFunction.measure) (Set.Ioc p q) +
          E.measure (Set.Ioc p q) := by
    intro p q hp hq
    rw [Measure.add_apply, d35_stj_Ioc _ hd hrd, d35_stj_Ioc _ ha hra, d35_stj_Ioc _ hb hrb,
      StieltjesFunction.measure_Ioc]
    show _ = _ + _ + ENNReal.ofReal (e q - e p)
    have hqT : q.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hq
    rcases le_or_gt p q with hpq | hpq
    · have hpT : p.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hpq).trans hqT
      have hmq : m q = q.toNNReal := min_eq_left hqT
      have hmp : m p = p.toNNReal := min_eq_left hpT
      have h1 : a p.toNNReal ≤ a q.toNNReal := ha hpq
      have h2 : b p.toNNReal ≤ b q.toNNReal := hb hpq
      have h3 : e p ≤ e q := he hpq
      simp only [e, hmq, hmp] at h3 ⊢
      rw [← ENNReal.ofReal_add (by linarith) (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
    · have h1 : a q.toNNReal ≤ a p.toNNReal := ha hpq.le
      have h2 : b q.toNNReal ≤ b p.toNNReal := hb hpq.le
      have h3 : e q ≤ e p := he hpq.le
      have h4 : d q.toNNReal ≤ d p.toNNReal := hd hpq.le
      rw [ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_of_nonpos (by linarith),
        ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_of_nonpos (by linarith)]
      simp
  have : IsFiniteMeasure (hd.stieltjesFunction.measure.restrict (Set.Ioc 0 (T:ℝ))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have heq : hd.stieltjesFunction.measure.restrict (Set.Ioc 0 (T:ℝ)) =
      (ha.stieltjesFunction.measure + hb.stieltjesFunction.measure).restrict (Set.Ioc 0 (T:ℝ)) +
        E.measure.restrict (Set.Ioc 0 (T:ℝ)) := by
    refine Measure.ext_of_Ioc_finite _ _ ?_ ?_
    · rw [Measure.add_apply, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ]
      exact key 0 T le_rfl le_rfl
    · intro u v _
      rw [Measure.add_apply, d35_restrict_Ioc_apply, d35_restrict_Ioc_apply,
        d35_restrict_Ioc_apply]
      exact key _ _ (le_max_right _ _) (min_le_right _ _)
  rw [heq]
  exact Measure.le_add_right le_rfl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {β : ℝ}

lemma d35_pos_meas (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) : Measurable (I.Apos t) :=
  (I.adapted_pos t).measurable.mono (𝓕.le t) le_rfl

lemma d35_neg_meas (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) : Measurable (I.Aneg t) :=
  (I.adapted_neg t).measurable.mono (𝓕.le t) le_rfl

lemma d35_D_rc (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => Dproc IA IC s ω) (Set.Ici t) t :=
  ((IA.rc_pos ω t).add (IA.rc_neg ω t)).max ((IC.rc_pos ω t).add (IC.rc_neg ω t))

lemma d35_D_meas (IA IC : BVIntegrator 𝓕 T β) (t : ℝ≥0) : Measurable (Dproc IA IC t) :=
  ((d35_pos_meas IA t).add (d35_neg_meas IA t)).max
    ((d35_pos_meas IC t).add (d35_neg_meas IC t))

lemma d35_D_Fmeas (IA IC : BVIntegrator 𝓕 T β) (t : ℝ≥0) :
    Measurable[𝓕 t] (Dproc IA IC t) :=
  (((IA.adapted_pos t).measurable).add ((IA.adapted_neg t).measurable)).max
    (((IC.adapted_pos t).measurable).add ((IC.adapted_neg t).measurable))

lemma d35_pos_nonneg (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : 0 ≤ I.Apos t ω := by
  have := I.mono_pos ω (show (0:ℝ≥0) ≤ t from zero_le); simp only [(I.zero ω).1] at this; exact this

lemma d35_neg_nonneg (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : 0 ≤ I.Aneg t ω := by
  have := I.mono_neg ω (show (0:ℝ≥0) ≤ t from zero_le); simp only [(I.zero ω).2] at this; exact this

lemma d35_D_zero (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) : Dproc IA IC 0 ω = 0 := by
  simp [Dproc, BVIntegrator.totVar, (IA.zero ω).1, (IA.zero ω).2, (IC.zero ω).1, (IC.zero ω).2]

lemma d35_D_nonneg (IA IC : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : 0 ≤ Dproc IA IC t ω := by
  have : Dproc IA IC 0 ω ≤ Dproc IA IC t ω := Dproc_mono IA IC ω (show (0:ℝ≥0) ≤ t from zero_le)
  rwa [d35_D_zero] at this

lemma d35_D_le_T (IA IC : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) :
    Dproc IA IC t ω ≤ Dproc IA IC T ω := by
  rcases le_total t T with h | h
  · exact Dproc_mono IA IC ω h
  · simp [Dproc, BVIntegrator.totVar, (IA.frozen ω t h).1, (IA.frozen ω t h).2,
      (IC.frozen ω t h).1, (IC.frozen ω t h).2]

lemma d35_D_le (IA IC : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : Dproc IA IC t ω ≤ β := by
  refine (d35_D_le_T IA IC t ω).trans (max_le ?_ ?_)
  · exact IA.bound ω
  · exact IC.bound ω

lemma d35_pos_le (I : BVIntegrator 𝓕 T β) (ω : Ω) : I.Apos T ω - I.Apos 0 ω ≤ β := by
  have := I.bound ω; have := d35_neg_nonneg I T ω; rw [(I.zero ω).1]; linarith

lemma d35_neg_le (I : BVIntegrator 𝓕 T β) (ω : Ω) : I.Aneg T ω - I.Aneg 0 ω ≤ β := by
  have := I.bound ω; have := d35_pos_nonneg I T ω; rw [(I.zero ω).2]; linarith

lemma d35_dD_Ioc (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) (u v : ℝ) :
    dD IA IC ω (Set.Ioc u v) =
      ENNReal.ofReal (Dproc IA IC v.toNNReal ω - Dproc IA IC u.toNNReal ω) :=
  d35_stj_Ioc _ _ (d35_D_rc IA IC ω) u v

lemma d35_var_le_dD (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC) (ω : Ω) :
    (IA.varMeasure ω).restrict (Set.Ioc 0 (T:ℝ)) ≤ (dD IA IC ω).restrict (Set.Ioc 0 (T:ℝ)) ∧
    (IC.varMeasure ω).restrict (Set.Ioc 0 (T:ℝ)) ≤ (dD IA IC ω).restrict (Set.Ioc 0 (T:ℝ)) :=
  ⟨d35_dom T (fun t => IA.Apos t ω) (fun t => IA.Aneg t ω) (fun t => Dproc IA IC t ω)
    (fun _ _ h => IA.mono_pos ω (Real.toNNReal_le_toNNReal h))
    (fun _ _ h => IA.mono_neg ω (Real.toNNReal_le_toNNReal h))
    (fun _ _ h => Dproc_mono IA IC ω (Real.toNNReal_le_toNNReal h))
    (IA.rc_pos ω) (IA.rc_neg ω) (d35_D_rc IA IC ω) (hdom.1 ω),
   d35_dom T (fun t => IC.Apos t ω) (fun t => IC.Aneg t ω) (fun t => Dproc IA IC t ω)
    (fun _ _ h => IC.mono_pos ω (Real.toNNReal_le_toNNReal h))
    (fun _ _ h => IC.mono_neg ω (Real.toNNReal_le_toNNReal h))
    (fun _ _ h => Dproc_mono IA IC ω (Real.toNNReal_le_toNNReal h))
    (IC.rc_pos ω) (IC.rc_neg ω) (d35_D_rc IA IC ω) (hdom.2 ω)⟩

lemma d35_lint_var_le (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC) (ω : Ω)
    (F : ℝ → ℝ≥0∞) (s t : ℝ≥0) (ht : t ≤ T) :
    ∫⁻ r in Set.Ioc (s:ℝ) t, F r ∂IA.varMeasure ω ≤ ∫⁻ r in Set.Ioc (s:ℝ) t, F r ∂dD IA IC ω ∧
    ∫⁻ r in Set.Ioc (s:ℝ) t, F r ∂IC.varMeasure ω ≤ ∫⁻ r in Set.Ioc (s:ℝ) t, F r ∂dD IA IC ω := by
  have hsub : Set.Ioc (s:ℝ) t ∩ Set.Ioc 0 T = Set.Ioc (s:ℝ) t :=
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc (by simp) (by exact_mod_cast ht))
  have hr : ∀ μ : Measure ℝ, μ.restrict (Set.Ioc (s:ℝ) t) =
      (μ.restrict (Set.Ioc 0 (T:ℝ))).restrict (Set.Ioc (s:ℝ) t) := by
    intro μ; rw [Measure.restrict_restrict measurableSet_Ioc, hsub]
  constructor
  · rw [hr, hr (dD IA IC ω)]
    exact lintegral_mono' (Measure.restrict_mono subset_rfl (d35_var_le_dD IA IC hdom ω).1) le_rfl
  · rw [hr, hr (dD IA IC ω)]
    exact lintegral_mono' (Measure.restrict_mono subset_rfl (d35_var_le_dD IA IC hdom ω).2) le_rfl

/-! ### Integral bounds -/

lemma d35_enorm_int_sub (μ : Measure ℝ) (h h' : ℝ → ℝ) (hm : AEStronglyMeasurable h μ)
    (hm' : AEStronglyMeasurable h' μ) :
    ‖(∫ x, h x ∂μ) - ∫ x, h' x ∂μ‖ₑ ≤ ∫⁻ x, ‖h x - h' x‖ₑ ∂μ := by
  by_cases hi : Integrable (fun x => h x - h' x) μ
  · by_cases hh : Integrable h μ
    · have hh' : Integrable h' μ := by
        refine (hh.sub hi).congr ?_
        filter_upwards with x; simp
      rw [← integral_sub hh hh']; exact enorm_integral_le_lintegral_enorm _
    · have hh' : ¬ Integrable h' μ := fun hh' => hh (by
        refine (hi.add hh').congr ?_
        filter_upwards with x; simp)
      rw [integral_undef hh, integral_undef hh']; simp
  · have : ¬ HasFiniteIntegral (fun x => h x - h' x) μ := fun hf => hi ⟨hm.sub hm', hf⟩
    simp only [HasFiniteIntegral, not_lt, top_le_iff] at this
    rw [this]; exact le_top

lemma d35_integral_sub_le (I : BVIntegrator 𝓕 T β) (h h' : ℝ≥0 → Ω → ℝ) (ω : Ω) (s t : ℝ≥0)
    (hm : Measurable (fun r : ℝ => h r.toNNReal ω)) (hm' : Measurable (fun r : ℝ => h' r.toNNReal ω)) :
    ‖I.integral h s t ω - I.integral h' s t ω‖ₑ ≤
      ∫⁻ r in Set.Ioc (s:ℝ) t, ‖h r.toNNReal ω - h' r.toNNReal ω‖ₑ ∂I.varMeasure ω := by
  unfold BVIntegrator.integral BVIntegrator.varMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  have e : ∀ a b c d : ℝ, (a - b) - (c - d) = (a - c) - (b - d) := fun _ _ _ _ => by ring
  rw [e]
  refine (enorm_sub_le).trans (add_le_add ?_ ?_)
  · exact d35_enorm_int_sub _ _ _ hm.aestronglyMeasurable hm'.aestronglyMeasurable
  · exact d35_enorm_int_sub _ _ _ hm.aestronglyMeasurable hm'.aestronglyMeasurable

lemma d35_integral_le (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (ω : Ω) (s t : ℝ≥0)
    (hm : Measurable (fun r : ℝ => h r.toNNReal ω)) :
    ‖I.integral h s t ω‖ₑ ≤ ∫⁻ r in Set.Ioc (s:ℝ) t, ‖h r.toNNReal ω‖ₑ ∂I.varMeasure ω := by
  have := d35_integral_sub_le I h (fun _ _ => 0) ω s t hm measurable_const
  simpa [BVIntegrator.integral] using this

lemma d35_sec {U : ℝ≥0 → Ω → ℝ} (hU : Measurable (Function.uncurry U)) :
    Measurable (fun p : Ω × ℝ => U p.2.toNNReal p.1) :=
  hU.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)

lemma d35_sec1 {U : ℝ≥0 → Ω → ℝ} (hU : Measurable (Function.uncurry U)) (ω : Ω) :
    Measurable (fun r : ℝ => U r.toNNReal ω) :=
  (d35_sec hU).comp (measurable_const.prodMk measurable_id)

lemma d35_comp_meas {φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ}
    (hφ : Measurable (fun p : ℝ≥0 × Ω × ℝ × ℝ => φ p.1 p.2.1 p.2.2.1 p.2.2.2))
    {U V : ℝ≥0 → Ω → ℝ} (hU : Measurable (Function.uncurry U))
    (hV : Measurable (Function.uncurry V)) :
    Measurable (Function.uncurry (fun s ω => φ s ω (U s ω) (V s ω))) :=
  hφ.comp (measurable_fst.prodMk (measurable_snd.prodMk (hU.prodMk hV)))

lemma d35_dD_meas (IA IC : BVIntegrator 𝓕 T β) (F : Ω → ℝ → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) (s t : ℝ≥0) (ht : t ≤ T) :
    Measurable (fun ω => ∫⁻ r in Set.Ioc (s:ℝ) t, F ω r ∂dD IA IC ω) :=
  d35_meas_lintegral (Dproc IA IC)
    (fun ω _ _ h => Dproc_mono IA IC ω (Real.toNNReal_le_toNNReal h)) (fun ω => d35_D_rc IA IC ω)
    (d35_D_meas IA IC) T β (fun ω => by rw [d35_D_zero, sub_zero]; exact d35_D_le IA IC T ω)
    F hF s t ht

lemma d35_pos_int_meas (I : BVIntegrator 𝓕 T β) (F : Ω → ℝ → ℝ)
    (hF : Measurable (Function.uncurry F)) (s t : ℝ≥0) (ht : t ≤ T) :
    StronglyMeasurable (fun ω => ∫ r in Set.Ioc (s:ℝ) t, F ω r ∂I.posMeasure ω) :=
  d35_meas_integral I.Apos
    (fun ω _ _ h => I.mono_pos ω (Real.toNNReal_le_toNNReal h)) I.rc_pos
    (d35_pos_meas I) T β (d35_pos_le I) F hF s t ht

lemma d35_neg_int_meas (I : BVIntegrator 𝓕 T β) (F : Ω → ℝ → ℝ)
    (hF : Measurable (Function.uncurry F)) (s t : ℝ≥0) (ht : t ≤ T) :
    StronglyMeasurable (fun ω => ∫ r in Set.Ioc (s:ℝ) t, F ω r ∂I.negMeasure ω) :=
  d35_meas_integral I.Aneg
    (fun ω _ _ h => I.mono_neg ω (Real.toNNReal_le_toNNReal h)) I.rc_neg
    (d35_neg_meas I) T β (d35_neg_le I) F hF s t ht

lemma d35_integral_meas (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ)
    (hh : Measurable (Function.uncurry h)) (s t : ℝ≥0) (ht : t ≤ T) :
    StronglyMeasurable (fun ω => I.integral h s t ω) := by
  unfold BVIntegrator.integral
  have hF : Measurable (Function.uncurry (fun ω (r : ℝ) => h r.toNNReal ω)) := d35_sec hh
  exact (d35_pos_int_meas I _ hF s t ht).sub (d35_neg_int_meas I _ hF s t ht)

lemma d35_L1_meas (IA IC : BVIntegrator 𝓕 T β) (M : ℝ≥0 → Ω → ℝ)
    (hM : Measurable (Function.uncurry M)) (s t : ℝ≥0) (ht : t ≤ T) :
    Measurable (fun ω => ∫⁻ r in Set.Ioc (s:ℝ) t, ‖M r.toNNReal ω‖ₑ ∂dD IA IC ω) :=
  d35_dD_meas IA IC (fun ω r => ‖M r.toNNReal ω‖ₑ) (d35_sec hM).enorm s t ht

lemma d35_L1_meas0 (IA IC : BVIntegrator 𝓕 T β) (M : ℝ≥0 → Ω → ℝ)
    (hM : Measurable (Function.uncurry M)) :
    Measurable (fun ω => ∫⁻ r in Set.Ioc (0:ℝ) T, ‖M r.toNNReal ω‖ₑ ∂dD IA IC ω) := by
  simpa using d35_L1_meas IA IC M hM 0 T le_rfl

lemma d35_dD_meas0 (IA IC : BVIntegrator 𝓕 T β) (F : Ω → ℝ → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) (t : ℝ≥0) (ht : t ≤ T) :
    Measurable (fun ω => ∫⁻ r in Set.Ioc (0:ℝ) t, F ω r ∂dD IA IC ω) := by
  simpa using d35_dD_meas IA IC F hF 0 t ht

lemma d35_lip_pt {φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hlip : ∀ s ≤ T, ∀ ω x y x' y', |φ s ω x y - φ s ω x' y'| ≤ k * (|x - x'| + |y - y'|))
    (s : ℝ≥0) (hs : s ≤ T) (ω : Ω) (x y x' y' : ℝ) :
    ‖φ s ω x y - φ s ω x' y'‖ₑ ≤ ENNReal.ofReal k * (‖x - x'‖ₑ + ‖y - y'‖ₑ) := by
  simp only [Real.enorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ENNReal.ofReal_mul hk]
  exact ENNReal.ofReal_le_ofReal (hlip s hs ω x y x' y')

lemma d35_lip_pt0 {φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hlip : ∀ s ≤ T, ∀ ω x y x' y', |φ s ω x y - φ s ω x' y'| ≤ k * (|x - x'| + |y - y'|))
    (s : ℝ≥0) (hs : s ≤ T) (ω : Ω) (x y : ℝ) :
    ‖φ s ω x y‖ₑ ≤ ‖φ s ω 0 0‖ₑ + ENNReal.ofReal k * (‖x‖ₑ + ‖y‖ₑ) := by
  have h1 := d35_lip_pt hk hlip s hs ω x y 0 0
  simp only [sub_zero] at h1
  calc ‖φ s ω x y‖ₑ = ‖φ s ω 0 0 + (φ s ω x y - φ s ω 0 0)‖ₑ := by congr 1; ring
    _ ≤ ‖φ s ω 0 0‖ₑ + ‖φ s ω x y - φ s ω 0 0‖ₑ := enorm_add_le _ _
    _ ≤ _ := add_le_add le_rfl h1

lemma d35_L1_lip (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β) {φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ} {k : ℝ}
    (hk : 0 ≤ k)
    (hφ : Measurable (fun p : ℝ≥0 × Ω × ℝ × ℝ => φ p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hlip : ∀ s ≤ T, ∀ ω x y x' y', |φ s ω x y - φ s ω x' y'| ≤ k * (|x - x'| + |y - y'|))
    {U V : ℝ≥0 → Ω → ℝ} (hU : Measurable (Function.uncurry U))
    (hV : Measurable (Function.uncurry V)) :
    L1NormD P IA IC (fun s ω => φ s ω (U s ω) (V s ω)) ≤
      L1NormD P IA IC (fun s ω => φ s ω 0 0) +
        ENNReal.ofReal k * (L1NormD P IA IC U + L1NormD P IA IC V) := by
  have h0 : Measurable (Function.uncurry (fun s ω => φ s ω 0 0)) :=
    d35_comp_meas hφ (U := fun _ _ => 0) (V := fun _ _ => 0) measurable_const measurable_const
  unfold L1NormD
  have hpt : ∀ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, ‖φ r.toNNReal ω (U r.toNNReal ω) (V r.toNNReal ω)‖ₑ
      ∂dD IA IC ω ≤ (∫⁻ r in Set.Ioc (0:ℝ) T, ‖φ r.toNNReal ω 0 0‖ₑ ∂dD IA IC ω) +
        ENNReal.ofReal k * ((∫⁻ r in Set.Ioc (0:ℝ) T, ‖U r.toNNReal ω‖ₑ ∂dD IA IC ω) +
          ∫⁻ r in Set.Ioc (0:ℝ) T, ‖V r.toNNReal ω‖ₑ ∂dD IA IC ω) := by
    intro ω
    calc _ ≤ ∫⁻ r in Set.Ioc (0:ℝ) T, ‖φ r.toNNReal ω 0 0‖ₑ +
          ENNReal.ofReal k * (‖U r.toNNReal ω‖ₑ + ‖V r.toNNReal ω‖ₑ) ∂dD IA IC ω := by
          refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
          have hrT : r.toNNReal ≤ T := by
            rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
          exact d35_lip_pt0 hk hlip _ hrT ω _ _
      _ = _ := by
          rw [lintegral_add_left ((d35_sec1 h0 ω).enorm), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left ((d35_sec1 hU ω).enorm)]
  have m0 : Measurable (fun ω => ∫⁻ r in Set.Ioc (0:ℝ) T, ‖φ r.toNNReal ω 0 0‖ₑ ∂dD IA IC ω) :=
    d35_L1_meas0 IA IC _ h0
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_add_left m0, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left (d35_L1_meas0 IA IC _ hU)]

lemma d35_int_le_dD (IA IC I : BVIntegrator 𝓕 T β) (ω : Ω)
    (hI : (I.varMeasure ω).restrict (Set.Ioc 0 (T:ℝ)) ≤ (dD IA IC ω).restrict (Set.Ioc 0 (T:ℝ)))
    (h : ℝ≥0 → Ω → ℝ) (hm : Measurable (fun r : ℝ => h r.toNNReal ω)) (s t : ℝ≥0) (ht : t ≤ T) :
    ‖I.integral h s t ω‖ₑ ≤ ∫⁻ r in Set.Ioc (0:ℝ) T, ‖h r.toNNReal ω‖ₑ ∂dD IA IC ω := by
  refine (d35_integral_le I h ω s t hm).trans ?_
  refine (lintegral_mono_set (Set.Ioc_subset_Ioc (NNReal.coe_nonneg s)
    (NNReal.coe_le_coe.2 ht))).trans ?_
  exact lintegral_mono' hI le_rfl

lemma d35_int_sub_le_dD (IA IC I : BVIntegrator 𝓕 T β) (ω : Ω)
    (hI : (I.varMeasure ω).restrict (Set.Ioc 0 (T:ℝ)) ≤ (dD IA IC ω).restrict (Set.Ioc 0 (T:ℝ)))
    (h h' : ℝ≥0 → Ω → ℝ) (hm : Measurable (fun r : ℝ => h r.toNNReal ω))
    (hm' : Measurable (fun r : ℝ => h' r.toNNReal ω)) (s t : ℝ≥0) (ht : t ≤ T) :
    ‖I.integral h s t ω - I.integral h' s t ω‖ₑ ≤
      ∫⁻ r in Set.Ioc (s:ℝ) t, ‖h r.toNNReal ω - h' r.toNNReal ω‖ₑ ∂dD IA IC ω := by
  refine (d35_integral_sub_le I h h' ω s t hm hm').trans ?_
  have hsub : Set.Ioc (s:ℝ) t ∩ Set.Ioc 0 T = Set.Ioc (s:ℝ) t :=
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc (by simp) (by exact_mod_cast ht))
  have hr : ∀ μ : Measure ℝ, μ.restrict (Set.Ioc (s:ℝ) t) =
      (μ.restrict (Set.Ioc 0 (T:ℝ))).restrict (Set.Ioc (s:ℝ) t) := by
    intro μ; rw [Measure.restrict_restrict measurableSet_Ioc, hsub]
  rw [hr, hr (dD IA IC ω)]
  exact lintegral_mono' (Measure.restrict_mono subset_rfl hI) le_rfl

lemma d35_dD_I (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) :
    dD IA IC ω (Set.Ioc 0 (T:ℝ)) = ENNReal.ofReal (Dproc IA IC T ω) := by
  rw [d35_dD_Ioc]; simp [d35_D_zero]

lemma d35_dD_I_le (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) :
    dD IA IC ω (Set.Ioc 0 (T:ℝ)) ≤ ENNReal.ofReal β := by
  rw [d35_dD_I]; exact ENNReal.ofReal_le_ofReal (d35_D_le IA IC T ω)

/-! ### gamma_maps_L1, parts 1 and 2 -/

theorem d35_gamma12 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ)
    (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V) :
    L1NormD P IA IC (Fop IA J f U V) < ⊤ ∧
    (∀ t ≤ T, Integrable (xiG IC g Y U V t) P) := by
  have hk := hyp.k_pos.le
  have hfm := d35_comp_meas hyp.f_meas hU.1 hV.1
  have hgm := d35_comp_meas hyp.g_meas hU.1 hV.1
  have hfL := (d35_L1_lip P IA IC hk hyp.f_meas hyp.f_lip hU.1 hV.1).trans_lt
    (ENNReal.add_lt_top.2 ⟨hyp.f_zero, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hU.2, hV.2⟩)⟩)
  have hgL := (d35_L1_lip P IA IC hk hyp.g_meas hyp.g_lip hU.1 hV.1).trans_lt
    (ENNReal.add_lt_top.2 ⟨hyp.g_zero, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hU.2, hV.2⟩)⟩)
  constructor
  · set Zf : Ω → ℝ≥0∞ := fun ω => ∫⁻ r in Set.Ioc (0:ℝ) T,
      ‖f r.toNNReal ω (U r.toNNReal ω) (V r.toNNReal ω)‖ₑ ∂dD IA IC ω with hZf
    have hZm : Measurable Zf := d35_L1_meas0 IA IC _ hfm
    have hpt : ∀ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, ‖Fop IA J f U V r.toNNReal ω‖ₑ ∂dD IA IC ω ≤
        (∫⁻ r in Set.Ioc (0:ℝ) T, ‖J r.toNNReal ω‖ₑ ∂dD IA IC ω) + Zf ω * ENNReal.ofReal β := by
      intro ω
      calc _ ≤ ∫⁻ r in Set.Ioc (0:ℝ) T, ‖J r.toNNReal ω‖ₑ + Zf ω ∂dD IA IC ω := by
            refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
            have hrT : r.toNNReal ≤ T := by
              rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
            unfold Fop
            refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
            exact d35_int_le_dD IA IC IA ω (d35_var_le_dD IA IC hdom ω).1 _
              (d35_sec1 hfm ω) 0 _ hrT
        _ = (∫⁻ r in Set.Ioc (0:ℝ) T, ‖J r.toNNReal ω‖ₑ ∂dD IA IC ω) +
              Zf ω * dD IA IC ω (Set.Ioc 0 (T:ℝ)) := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl (d35_dD_I_le IA IC ω))
    unfold L1NormD
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_add_right _ (hZm.mul_const _), lintegral_mul_const _ hZm]
    exact ENNReal.add_lt_top.2 ⟨hyp.J_int, ENNReal.mul_lt_top hfL ENNReal.ofReal_lt_top⟩
  · intro t ht
    refine Integrable.add ⟨(d35_integral_meas IC _ hgm t T le_rfl).aestronglyMeasurable, ?_⟩
      hyp.Y_int
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hgL
    exact d35_int_le_dD IA IC IC ω (d35_var_le_dD IA IC hdom ω).2 _ (d35_sec1 hgm ω) t T le_rfl

/-! ### Conditional expectation step -/

lemma d35_ce {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (V X Z : Ω → ℝ) (k : ℝ) (hk : 0 ≤ k)
    (hV : ∀ᵐ ω ∂P, |V ω| ≤ k * (P[X|m]) ω) (hX : Integrable X P) (hX0 : ∀ ω, 0 ≤ X ω)
    (hZm : StronglyMeasurable[m] Z) (hZ0 : ∀ ω, 0 ≤ Z ω) (B : ℝ) (hZB : ∀ ω, Z ω ≤ B) :
    ∫⁻ ω, ‖V ω‖ₑ * ENNReal.ofReal (Z ω) ∂P ≤
      ENNReal.ofReal k * ∫⁻ ω, ENNReal.ofReal (X ω) * ENNReal.ofReal (Z ω) ∂P := by
  have hZmeas : Measurable[mΩ] Z := hZm.measurable.mono hm le_rfl
  have hbd : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ B := ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]; exact hZB ω)
  have hint : Integrable (fun ω => Z ω * (P[X|m]) ω) P :=
    integrable_condExp.bdd_mul hZmeas.aestronglyMeasurable hbd
  have hint2 : Integrable (fun ω => Z ω * X ω) P :=
    hX.bdd_mul hZmeas.aestronglyMeasurable hbd
  have hce : ∫ ω, Z ω * (P[X|m]) ω ∂P = ∫ ω, Z ω * X ω ∂P := by
    have h1 := condExp_mul_of_stronglyMeasurable_left hZm hint2 hX
    rw [show (∫ ω, Z ω * (P[X|m]) ω ∂P) = ∫ ω, (P[Z * X|m]) ω ∂P from
      (integral_congr_ae h1).symm]
    exact integral_condExp hm
  have hcn : 0 ≤ᵐ[P] P[X|m] := condExp_nonneg (ae_of_all _ hX0)
  calc ∫⁻ ω, ‖V ω‖ₑ * ENNReal.ofReal (Z ω) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal k * ENNReal.ofReal (Z ω * (P[X|m]) ω) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hV] with ω hω
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← ENNReal.ofReal_mul hk]
        apply ENNReal.ofReal_le_ofReal
        have := hZ0 ω
        nlinarith
    _ = ENNReal.ofReal k * ENNReal.ofReal (∫ ω, Z ω * (P[X|m]) ω ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [hcn] with ω hω
        exact mul_nonneg (hZ0 ω) hω
    _ = ENNReal.ofReal k * ∫⁻ ω, ENNReal.ofReal (X ω) * ENNReal.ofReal (Z ω) ∂P := by
        rw [hce, ofReal_integral_eq_lintegral_ofReal hint2
          (ae_of_all _ (fun ω => mul_nonneg (hZ0 ω) (hX0 ω)))]
        congr 1
        refine lintegral_congr (fun ω => ?_)
        rw [ENNReal.ofReal_mul (hZ0 ω), mul_comm]

/-! ### Discretization / Fatou lemma -/

lemma d35_decomp (μ : Measure ℝ) (G : ℝ → ℝ≥0∞) (a : ℕ → ℝ) (ha : Monotone a) (N : ℕ) :
    ∫⁻ r in Set.Ioc (a 0) (a N), G r ∂μ =
      ∑ j ∈ Finset.range N, ∫⁻ r in Set.Ioc (a j) (a (j+1)), G r ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, ← Set.Ioc_union_Ioc_eq_Ioc (ha (Nat.zero_le N))
      (ha (Nat.le_succ N))]
    exact lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)

/-- grid points `T j / 2^n` -/
noncomputable def d35_a (T : ℝ≥0) (n j : ℕ) : ℝ := (T:ℝ) * j / 2 ^ n

/-- index of the grid cell containing `r` -/
noncomputable def d35_idx (T : ℝ≥0) (n : ℕ) (r : ℝ) : ℕ := ⌈r * 2 ^ n / T⌉₊

lemma d35_a_mono (T : ℝ≥0) (n : ℕ) : Monotone (d35_a T n) := by
  intro i j hij
  unfold d35_a
  have : (i:ℝ) ≤ j := by exact_mod_cast hij
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  apply div_le_div_of_nonneg_right _ h2.le
  exact mul_le_mul_of_nonneg_left this (NNReal.coe_nonneg T)

lemma d35_a_zero (T : ℝ≥0) (n : ℕ) : d35_a T n 0 = 0 := by simp [d35_a]

lemma d35_a_top (T : ℝ≥0) (n : ℕ) : d35_a T n (2 ^ n) = T := by
  unfold d35_a; push_cast; field_simp

lemma d35_a_nonneg (T : ℝ≥0) (n j : ℕ) : 0 ≤ d35_a T n j := by
  unfold d35_a; positivity

lemma d35_a_le (T : ℝ≥0) (n j : ℕ) (hj : j ≤ 2 ^ n) : d35_a T n j ≤ T := by
  rw [← d35_a_top T n]; exact d35_a_mono T n hj

lemma d35_idx_eq (T : ℝ≥0) (hT : 0 < T) (n j : ℕ) (r : ℝ)
    (hr : r ∈ Set.Ioc (d35_a T n j) (d35_a T n (j+1))) : d35_idx T n r = j + 1 := by
  unfold d35_idx
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  rw [Nat.ceil_eq_iff (by omega)]
  simp only [Nat.add_sub_cancel]
  unfold d35_a at hr
  obtain ⟨h1, h3⟩ := hr
  push_cast at h1 h3 ⊢
  constructor
  · rw [lt_div_iff₀ hT']
    rw [div_lt_iff₀ h2] at h1
    linarith
  · rw [div_le_iff₀ hT']
    rw [le_div_iff₀ h2] at h3
    linarith

lemma d35_rho_bounds (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (r : ℝ) (hr : r ∈ Set.Ioc (0:ℝ) T) :
    r ≤ d35_a T n (d35_idx T n r) ∧ d35_a T n (d35_idx T n r) < r + T / 2 ^ n ∧
      d35_idx T n r ≤ 2 ^ n := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  have hx0 : 0 ≤ r * 2 ^ n / T := by have := hr.1.le; positivity
  have hc1 := Nat.le_ceil (r * 2 ^ n / T)
  have hc2 := Nat.ceil_lt_add_one hx0
  unfold d35_a d35_idx
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2]
    have e : r * 2 ^ n = T * (r * 2 ^ n / T) := by field_simp
    calc r * 2 ^ n = T * (r * 2 ^ n / T) := e
      _ ≤ _ := mul_le_mul_of_nonneg_left hc1 hT'.le
  · rw [div_lt_iff₀ h2]
    have e : (r + T / 2 ^ n) * 2 ^ n = T * (r * 2 ^ n / T + 1) := by field_simp
    rw [e]
    exact mul_lt_mul_of_pos_left hc2 hT'
  · rw [Nat.ceil_le]
    rw [div_le_iff₀ hT']
    push_cast
    nlinarith [hr.2]

lemma d35_rho_tendsto (T : ℝ≥0) (hT : 0 < T) (r : ℝ) (hr : r ∈ Set.Ioc (0:ℝ) T) :
    Tendsto (fun n => d35_a T n (d35_idx T n r)) atTop (𝓝 r) := by
  have hlim : Tendsto (fun n : ℕ => r + (T:ℝ) / 2 ^ n) atTop (𝓝 (r + 0)) := by
    refine tendsto_const_nhds.add ?_
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  rw [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (d35_rho_bounds T hT n r hr).1) (fun n => (d35_rho_bounds T hT n r hr).2.1.le)

lemma d35_key {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (T : ℝ≥0) (hT : 0 < T)
    (c : ℝ≥0 → Ω → ℝ) (h : ∀ ω, Monotone (fun x : ℝ => c x.toNNReal ω))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => c s ω) (Set.Ici t) t)
    (hcm : ∀ t, Measurable (c t))
    (W : ℝ≥0 → Ω → ℝ) (hWm : ∀ t ≤ T, Measurable (W t))
    (hWrc : ∀ ω, ∀ t < T, ContinuousWithinAt (fun s => W s ω) (Set.Ici t) t)
    (Φ : ℝ≥0 → Ω → ℝ≥0∞) (hΦa : ∀ ω, Antitone (fun t => Φ t ω))
    (hΦm : ∀ t ≤ T, Measurable (Φ t))
    (hH : ∀ t ≤ T, ∀ u ≤ t, ∫⁻ ω, ‖W t ω‖ₑ * ENNReal.ofReal (c t ω - c u ω) ∂P ≤
      ∫⁻ ω, Φ t ω * ENNReal.ofReal (c t ω - c u ω) ∂P) :
    ∫⁻ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, ‖W r.toNNReal ω‖ₑ ∂(h ω).stieltjesFunction.measure ∂P ≤
      ∫⁻ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, Φ r.toNNReal ω ∂(h ω).stieltjesFunction.measure ∂P := by
  -- notation
  set a := d35_a T with ha_def
  set tt : ℕ → ℕ → ℝ≥0 := fun n j => (a n j).toNNReal with htt
  have htt_le : ∀ n j, j ≤ 2 ^ n → tt n j ≤ T := fun n j hj => by
    simp only [htt]; rw [Real.toNNReal_le_iff_le_coe]; exact d35_a_le T n j hj
  have htt_mono : ∀ n j, tt n j ≤ tt n (j+1) := fun n j =>
    Real.toNNReal_le_toNNReal (d35_a_mono T n (Nat.le_succ j))
  let S : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑ j ∈ Finset.range (2 ^ n),
    ‖W (tt n (j+1)) ω‖ₑ * ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω)
  have hSm : ∀ n, Measurable (S n) := by
    intro n
    refine Finset.measurable_fun_sum _ (fun j hj => ?_)
    have hj : j + 1 ≤ 2 ^ n := Finset.mem_range.1 hj
    exact (hWm _ (htt_le n _ hj)).enorm.mul
      (ENNReal.measurable_ofReal.comp ((hcm _).sub (hcm _)))
  -- integral of a step function over a cell
  have hcell : ∀ ω n j (G : ℕ → ℝ≥0∞),
      ∫⁻ r in Set.Ioc (a n j) (a n (j+1)), G (d35_idx T n r) ∂(h ω).stieltjesFunction.measure =
        G (j+1) * ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω) := by
    intro ω n j G
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => G (j+1))
      (fun r hr => by rw [d35_idx_eq T hT n j r hr]), setLIntegral_const,
      d35_stj_Ioc _ (h ω) (hrc ω)]
  have hstep : ∀ ω n (G : ℕ → ℝ≥0∞),
      ∫⁻ r in Set.Ioc (0:ℝ) T, G (d35_idx T n r) ∂(h ω).stieltjesFunction.measure =
        ∑ j ∈ Finset.range (2 ^ n), G (j+1) *
          ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω) := by
    intro ω n G
    have := d35_decomp ((h ω).stieltjesFunction.measure) (fun r => G (d35_idx T n r)) (a n)
      (d35_a_mono T n) (2 ^ n)
    rw [show a n 0 = 0 from d35_a_zero T n, show a n (2 ^ n) = T from d35_a_top T n] at this
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => hcell ω n j G)
  have hidx_meas : ∀ n, Measurable (d35_idx T n) := fun n =>
    Nat.measurable_ceil.comp ((measurable_id.mul_const _).div_const _)
  -- inner Fatou
  have hinner : ∀ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, ‖W r.toNNReal ω‖ₑ ∂(h ω).stieltjesFunction.measure ≤
      liminf (fun n => S n ω) atTop := by
    intro ω
    have hconv : ∀ r ∈ Set.Ioc (0:ℝ) T, Tendsto (fun n => ‖W (tt n (d35_idx T n r)) ω‖ₑ) atTop
        (𝓝 ‖W r.toNNReal ω‖ₑ) := by
      intro r hr
      rcases lt_or_eq_of_le hr.2 with hrT | hrT
      · have hrT' : r.toNNReal < T := by
          rw [Real.toNNReal_lt_iff_lt_coe hr.1.le]; exact hrT
        have h1 : Tendsto (fun n => tt n (d35_idx T n r)) atTop (𝓝[≥] r.toNNReal) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun n => ?_)⟩
          · exact (continuous_real_toNNReal.tendsto r).comp (d35_rho_tendsto T hT r hr)
          · exact Real.toNNReal_le_toNNReal (d35_rho_bounds T hT n r hr).1
        exact (continuous_enorm.tendsto _).comp ((hWrc ω _ hrT').tendsto.comp h1)
      · have : ∀ n, tt n (d35_idx T n r) = r.toNNReal := by
          intro n
          have hb := d35_rho_bounds T hT n r hr
          have : a n (d35_idx T n r) = r := le_antisymm
            ((d35_a_le T n _ hb.2.2).trans hrT.ge) hb.1
          simp only [htt, this]
        simp only [this]
        exact tendsto_const_nhds
    calc _ = ∫⁻ r in Set.Ioc (0:ℝ) T, liminf (fun n => ‖W (tt n (d35_idx T n r)) ω‖ₑ) atTop
          ∂(h ω).stieltjesFunction.measure := by
          refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
          exact ((hconv r hr).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ r in Set.Ioc (0:ℝ) T, ‖W (tt n (d35_idx T n r)) ω‖ₑ
          ∂(h ω).stieltjesFunction.measure) atTop := by
          refine lintegral_liminf_le' (fun n => ?_)
          exact ((measurable_from_nat (f := fun m => ‖W (tt n m) ω‖ₑ)).comp
            (hidx_meas n)).aemeasurable
      _ = liminf (fun n => S n ω) atTop := by
          congr 1; ext n
          exact hstep ω n (fun m => ‖W (tt n m) ω‖ₑ)
  -- bound for each n
  have hbound : ∀ n, ∫⁻ ω, S n ω ∂P ≤
      ∫⁻ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, Φ r.toNNReal ω ∂(h ω).stieltjesFunction.measure ∂P := by
    intro n
    have hmeasT : ∀ j ∈ Finset.range (2 ^ n), Measurable (fun ω =>
        Φ (tt n (j+1)) ω * ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω)) := by
      intro j hj
      have hj : j + 1 ≤ 2 ^ n := Finset.mem_range.1 hj
      exact (hΦm _ (htt_le n _ hj)).mul (ENNReal.measurable_ofReal.comp ((hcm _).sub (hcm _)))
    calc ∫⁻ ω, S n ω ∂P
        = ∑ j ∈ Finset.range (2 ^ n), ∫⁻ ω, ‖W (tt n (j+1)) ω‖ₑ *
            ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω) ∂P := by
          refine lintegral_finsetSum _ (fun j hj => ?_)
          have hj : j + 1 ≤ 2 ^ n := Finset.mem_range.1 hj
          exact (hWm _ (htt_le n _ hj)).enorm.mul
            (ENNReal.measurable_ofReal.comp ((hcm _).sub (hcm _)))
      _ ≤ ∑ j ∈ Finset.range (2 ^ n), ∫⁻ ω, Φ (tt n (j+1)) ω *
            ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω) ∂P := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hj : j + 1 ≤ 2 ^ n := Finset.mem_range.1 hj
          exact hH _ (htt_le n _ hj) _ (htt_mono n j)
      _ = ∫⁻ ω, ∑ j ∈ Finset.range (2 ^ n), Φ (tt n (j+1)) ω *
            ENNReal.ofReal (c (tt n (j+1)) ω - c (tt n j) ω) ∂P :=
          (lintegral_finsetSum _ hmeasT).symm
      _ ≤ _ := by
          refine lintegral_mono (fun ω => ?_)
          have e1 := hstep ω n (fun m => Φ (tt n m) ω)
          rw [← e1]
          refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
          apply hΦa ω
          exact Real.toNNReal_le_toNNReal (d35_rho_bounds T hT n r hr).1
  calc _ ≤ ∫⁻ ω, liminf (fun n => S n ω) atTop ∂P := lintegral_mono hinner
    _ ≤ liminf (fun n => ∫⁻ ω, S n ω ∂P) atTop := lintegral_liminf_le hSm
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-! ### Versions -/

lemma d35_W_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] (T : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (hW : Measurable (Function.uncurry (fun t ω => if t ≤ T then W t ω else 0)))
    (t : ℝ≥0) (ht : t ≤ T) : Measurable (W t) := by
  have := hW.comp (measurable_const.prodMk measurable_id : Measurable (fun ω : Ω => (t, ω)))
  simpa [Function.comp_def, ht] using this

lemma d35_Zbound (IA IC : BVIntegrator 𝓕 T β) (t u : ℝ≥0) (hut : u ≤ t) :
    StronglyMeasurable[𝓕 t] (fun ω => Dproc IA IC t ω - Dproc IA IC u ω) ∧
    (∀ ω, 0 ≤ Dproc IA IC t ω - Dproc IA IC u ω) ∧
    (∀ ω, Dproc IA IC t ω - Dproc IA IC u ω ≤ β) := by
  refine ⟨?_, fun ω => sub_nonneg.2 (Dproc_mono IA IC ω hut), fun ω => ?_⟩
  · exact ((d35_D_Fmeas IA IC t).sub
      ((d35_D_Fmeas IA IC u).mono (𝓕.mono hut) le_rfl)).stronglyMeasurable
  · have := d35_D_le IA IC t ω; have := d35_D_nonneg IA IC u ω; linarith

theorem d35_gamma_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V) :
    L1NormD P IA IC (Fop IA J f U V) < ⊤ ∧
    (∀ t ≤ T, Integrable (xiG IC g Y U V t) P) ∧
    ∀ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → L1NormD P IA IC W < ⊤ := by
  obtain ⟨h1, h2⟩ := d35_gamma12 P 𝓕 T β IA IC hdom k f g Y J hyp U V hU hV
  refine ⟨h1, h2, fun W hW => ?_⟩
  have hk := hyp.k_pos.le
  have hgm := d35_comp_meas hyp.g_meas hU.1 hV.1
  have hgL := (d35_L1_lip P IA IC hk hyp.g_meas hyp.g_lip hU.1 hV.1).trans_lt
    (ENNReal.add_lt_top.2 ⟨hyp.g_zero, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hU.2, hV.2⟩)⟩)
  set Zg : Ω → ℝ≥0∞ := fun ω => ∫⁻ r in Set.Ioc (0:ℝ) T,
      ‖g r.toNNReal ω (U r.toNNReal ω) (V r.toNNReal ω)‖ₑ ∂dD IA IC ω with hZg
  have hZm : Measurable Zg := d35_L1_meas0 IA IC _ hgm
  have hZfin : ∫⁻ ω, Zg ω ∂P ≠ ⊤ := hgL.ne
  have hZae : ∀ᵐ ω ∂P, Zg ω < ⊤ := ae_lt_top hZm hZfin
  set X : Ω → ℝ := fun ω => (Zg ω).toReal + |Y ω| with hXdef
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => add_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hXi : Integrable X P :=
    (integrable_toReal_of_lintegral_ne_top hZm.aemeasurable hZfin).add hyp.Y_int.abs
  have hXm : Measurable X := hZm.ennreal_toReal.add
    (continuous_abs.measurable.comp (hyp.Y_meas.mono (𝓕.le T) le_rfl))
  -- pointwise bound on ξ
  have hxi : ∀ t ≤ T, ∀ᵐ ω ∂P, |xiG IC g Y U V t ω| ≤ X ω := by
    intro t ht
    filter_upwards [hZae] with ω hω
    have hb : ‖xiG IC g Y U V t ω‖ₑ ≤ Zg ω + ‖Y ω‖ₑ := by
      unfold xiG
      refine (enorm_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact d35_int_le_dD IA IC IC ω (d35_var_le_dD IA IC hdom ω).2 _ (d35_sec1 hgm ω) t T le_rfl
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_toReal hω.ne, ← ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _)]
      at hb
    exact (ENNReal.ofReal_le_ofReal_iff (hX0 ω)).1 hb
  -- conditional expectation bound
  have hWb : ∀ t ≤ T, ∀ᵐ ω ∂P, |W t ω| ≤ 1 * (P[X|𝓕 t]) ω := by
    intro t ht
    have hξ := hW.1 t ht
    filter_upwards [hW.2.1.2.2 t ht, abs_condExp_ae_le_condExp_abs (m := 𝓕 t) (μ := P)
      (xiG IC g Y U V t), condExp_mono (m := 𝓕 t) hξ.abs hXi (hxi t ht)] with ω h1 h2 h3
    rw [h1, one_mul]
    exact h2.trans h3
  have hkey := d35_key P T hT (Dproc IA IC)
    (fun ω _ _ h => Dproc_mono IA IC ω (Real.toNNReal_le_toNNReal h)) (fun ω => d35_D_rc IA IC ω)
    (d35_D_meas IA IC) W (d35_W_meas T W hW.2.1.1) (fun ω => (hW.2.2 ω).1)
    (fun _ ω => ENNReal.ofReal (X ω)) (fun ω => antitone_const)
    (fun _ _ => ENNReal.measurable_ofReal.comp hXm) ?_
  · unfold L1NormD
    refine hkey.trans_lt ?_
    have : ∀ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, ENNReal.ofReal (X ω) ∂dD IA IC ω ≤
        ENNReal.ofReal β * ENNReal.ofReal (X ω) := by
      intro ω
      rw [setLIntegral_const, mul_comm]
      exact mul_le_mul' (d35_dD_I_le IA IC ω) le_rfl
    refine (lintegral_mono this).trans_lt ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hXi (ae_of_all _ hX0)]
    exact ENNReal.ofReal_lt_top
  · intro t ht u hut
    obtain ⟨hZ1, hZ2, hZ3⟩ := d35_Zbound IA IC t u hut
    have := d35_ce P (𝓕.le t) (W t) X _ 1 zero_le_one (hWb t ht) hXi hX0 hZ1 hZ2 β hZ3
    simpa using this

/-! ### pathDist helpers and Lipschitz estimates -/

lemma d35_pd_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {β : ℝ}
    (IA IC : BVIntegrator 𝓕 T β) {U V U' V' : ℝ≥0 → Ω → ℝ}
    (hU : Measurable (Function.uncurry U)) (hV : Measurable (Function.uncurry V))
    (hU' : Measurable (Function.uncurry U')) (hV' : Measurable (Function.uncurry V'))
    (s t : ℝ≥0) (ht : t ≤ T) :
    Measurable (fun ω => pathDist IA IC U V U' V' s t ω) :=
  d35_dD_meas IA IC (fun ω r => ‖U r.toNNReal ω - U' r.toNNReal ω‖ₑ +
      ‖V r.toNNReal ω - V' r.toNNReal ω‖ₑ)
    (((d35_sec hU).sub (d35_sec hU')).enorm.add ((d35_sec hV).sub (d35_sec hV')).enorm) s t ht

lemma d35_pd_lint {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {β : ℝ}
    (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β) {U V U' V' : ℝ≥0 → Ω → ℝ}
    (hU : Measurable (Function.uncurry U)) (hV : Measurable (Function.uncurry V))
    (hU' : Measurable (Function.uncurry U')) (hV' : Measurable (Function.uncurry V')) :
    ∫⁻ ω, pathDist IA IC U V U' V' 0 T ω ∂P =
      L1NormD P IA IC (U - U') + L1NormD P IA IC (V - V') := by
  unfold pathDist L1NormD
  have e : ∀ ω, ∫⁻ r in Set.Ioc ((0:ℝ≥0):ℝ) T, ‖U r.toNNReal ω - U' r.toNNReal ω‖ₑ +
      ‖V r.toNNReal ω - V' r.toNNReal ω‖ₑ ∂dD IA IC ω =
      (∫⁻ r in Set.Ioc (0:ℝ) T, ‖(U - U') r.toNNReal ω‖ₑ ∂dD IA IC ω) +
        ∫⁻ r in Set.Ioc (0:ℝ) T, ‖(V - V') r.toNNReal ω‖ₑ ∂dD IA IC ω := by
    intro ω
    have hm : Measurable (fun r : ℝ => ‖U r.toNNReal ω - U' r.toNNReal ω‖ₑ) :=
      ((d35_sec1 hU ω).sub (d35_sec1 hU' ω)).enorm
    rw [NNReal.coe_zero, lintegral_add_left hm]
    rfl
  simp_rw [e]
  have hUU : Measurable (Function.uncurry (U - U')) := hU.sub hU'
  rw [lintegral_add_left (d35_L1_meas0 IA IC _ hUU)]

lemma d35_L1_sub_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0}
    {β : ℝ} (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β) {U U' : ℝ≥0 → Ω → ℝ}
    (hU : MemL1D P IA IC U) (hU' : MemL1D P IA IC U') : L1NormD P IA IC (U - U') < ⊤ := by
  unfold L1NormD
  have : ∀ ω, ∫⁻ r in Set.Ioc (0:ℝ) T, ‖(U - U') r.toNNReal ω‖ₑ ∂dD IA IC ω ≤
      (∫⁻ r in Set.Ioc (0:ℝ) T, ‖U r.toNNReal ω‖ₑ ∂dD IA IC ω) +
        ∫⁻ r in Set.Ioc (0:ℝ) T, ‖U' r.toNNReal ω‖ₑ ∂dD IA IC ω := by
    intro ω
    rw [← lintegral_add_left ((d35_sec1 hU.1 ω).enorm)]
    exact lintegral_mono (fun r => enorm_sub_le)
  refine (lintegral_mono this).trans_lt ?_
  rw [lintegral_add_left (d35_L1_meas0 IA IC _ hU.1)]
  exact ENNReal.add_lt_top.2 ⟨hU.2, hU'.2⟩

theorem d35_lip_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V U' V' : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V)
    (hU' : MemL1D P IA IC U') (hV' : MemL1D P IA IC V') :
    (∀ ω, ∀ t ≤ T, ENNReal.ofReal |Fop IA J f U V t ω - Fop IA J f U' V' t ω| ≤
        ENNReal.ofReal k * pathDist IA IC U V U' V' 0 t ω) ∧
    ∀ W W' : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → IsGVersion 𝓕 P IC g Y U' V' W' →
      ∀ t ≤ T, Integrable (fun ω => (pathDist IA IC U V U' V' t T ω).toReal) P ∧
        ∀ᵐ ω ∂P, |W t ω - W' t ω| ≤
          k * (P[fun ω => (pathDist IA IC U V U' V' t T ω).toReal | 𝓕 t]) ω := by
  have hk := hyp.k_pos.le
  have hfm := d35_comp_meas hyp.f_meas hU.1 hV.1
  have hfm' := d35_comp_meas hyp.f_meas hU'.1 hV'.1
  have hgm := d35_comp_meas hyp.g_meas hU.1 hV.1
  have hgm' := d35_comp_meas hyp.g_meas hU'.1 hV'.1
  -- generic pathwise bound
  have hgen : ∀ (I : BVIntegrator 𝓕 T β) (φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ)
      (hφ : Measurable (fun p : ℝ≥0 × Ω × ℝ × ℝ => φ p.1 p.2.1 p.2.2.1 p.2.2.2))
      (hlip : ∀ s ≤ T, ∀ ω x y x' y', |φ s ω x y - φ s ω x' y'| ≤ k * (|x - x'| + |y - y'|))
      (ω : Ω), (I.varMeasure ω).restrict (Set.Ioc 0 (T:ℝ)) ≤
        (dD IA IC ω).restrict (Set.Ioc 0 (T:ℝ)) → ∀ s t : ℝ≥0, t ≤ T →
      ‖I.integral (fun s ω => φ s ω (U s ω) (V s ω)) s t ω -
        I.integral (fun s ω => φ s ω (U' s ω) (V' s ω)) s t ω‖ₑ ≤
        ENNReal.ofReal k * pathDist IA IC U V U' V' s t ω := by
    intro I φ hφ hlip ω hI s t ht
    refine (d35_int_sub_le_dD IA IC I ω hI _ _ (d35_sec1 (d35_comp_meas hφ hU.1 hV.1) ω)
      (d35_sec1 (d35_comp_meas hφ hU'.1 hV'.1) ω) s t ht).trans ?_
    unfold pathDist
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
    have hrT : r.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hr.2.trans (by exact_mod_cast ht)
    exact d35_lip_pt hk hlip _ hrT ω _ _ _ _
  refine ⟨fun ω t ht => ?_, fun W W' hW hW' t ht => ?_⟩
  · rw [← Real.enorm_eq_ofReal_abs]
    unfold Fop
    rw [show ∀ a b c : ℝ, (a + b) - (a + c) = b - c from fun _ _ _ => by ring]
    exact hgen IA f hyp.f_meas hyp.f_lip ω (d35_var_le_dD IA IC hdom ω).1 0 t ht
  · have hpm := d35_pd_meas IA IC hU.1 hV.1 hU'.1 hV'.1 t T le_rfl
    have hp0 := d35_pd_meas IA IC hU.1 hV.1 hU'.1 hV'.1 0 T le_rfl
    have hfin0 : ∫⁻ ω, pathDist IA IC U V U' V' 0 T ω ∂P < ⊤ := by
      rw [d35_pd_lint P IA IC hU.1 hV.1 hU'.1 hV'.1]
      exact ENNReal.add_lt_top.2 ⟨d35_L1_sub_le P IA IC hU hU', d35_L1_sub_le P IA IC hV hV'⟩
    have hle : ∀ ω, pathDist IA IC U V U' V' t T ω ≤ pathDist IA IC U V U' V' 0 T ω :=
      fun ω => lintegral_mono_set (Set.Ioc_subset_Ioc (by simp) le_rfl)
    have hfin : ∫⁻ ω, pathDist IA IC U V U' V' t T ω ∂P ≠ ⊤ :=
      ((lintegral_mono hle).trans_lt hfin0).ne
    have hint : Integrable (fun ω => (pathDist IA IC U V U' V' t T ω).toReal) P :=
      integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hfin
    refine ⟨hint, ?_⟩
    have hξ := hW.1 t ht
    have hξ' := hW'.1 t ht
    -- pathwise bound on ξ - ξ'
    have hxi : ∀ᵐ ω ∂P, |(xiG IC g Y U V t - xiG IC g Y U' V' t) ω| ≤
        (k • fun ω => (pathDist IA IC U V U' V' t T ω).toReal) ω := by
      filter_upwards [ae_lt_top hpm hfin] with ω hω
      have hb := hgen IC g hyp.g_meas hyp.g_lip ω (d35_var_le_dD IA IC hdom ω).2 t T le_rfl
      have e : (xiG IC g Y U V t - xiG IC g Y U' V' t) ω =
          IC.integral (fun s ω => g s ω (U s ω) (V s ω)) t T ω -
            IC.integral (fun s ω => g s ω (U' s ω) (V' s ω)) t T ω := by
        simp only [Pi.sub_apply, xiG]; ring
      rw [e, Pi.smul_apply, smul_eq_mul]
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.ne) hb
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk, Real.enorm_eq_ofReal_abs,
        ENNReal.toReal_ofReal (abs_nonneg _)] at h2
      exact h2
    filter_upwards [hW.2.1.2.2 t ht, hW'.2.1.2.2 t ht, condExp_sub (m := 𝓕 t) hξ hξ',
      abs_condExp_ae_le_condExp_abs (m := 𝓕 t) (μ := P) (xiG IC g Y U V t - xiG IC g Y U' V' t),
      condExp_mono (m := 𝓕 t) (hξ.sub hξ').abs (hint.smul k) hxi,
      condExp_smul (m := 𝓕 t) (μ := P) k (fun ω => (pathDist IA IC U V U' V' t T ω).toReal)]
      with ω h1 h2 h3 h4 h5 h6
    rw [h1, h2]
    have : (P[xiG IC g Y U V t|𝓕 t]) ω - (P[xiG IC g Y U' V' t|𝓕 t]) ω =
        (P[xiG IC g Y U V t - xiG IC g Y U' V' t|𝓕 t]) ω := by
      rw [h3]; rfl
    rw [this]
    refine h4.trans (h5.trans (le_of_eq ?_))
    rw [h6]; rfl

end AntonelliBFSDE.BackwardForward

open AntonelliBFSDE.BackwardForward


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V U' V' : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V)
    (hU' : MemL1D P IA IC U') (hV' : MemL1D P IA IC V') :
    (∀ ω, ∀ t ≤ T, ENNReal.ofReal |Fop IA J f U V t ω - Fop IA J f U' V' t ω| ≤
        ENNReal.ofReal k * pathDist IA IC U V U' V' 0 t ω) ∧
    ∀ W W' : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → IsGVersion 𝓕 P IC g Y U' V' W' →
      ∀ t ≤ T, Integrable (fun ω => (pathDist IA IC U V U' V' t T ω).toReal) P ∧
        ∀ᵐ ω ∂P, |W t ω - W' t ω| ≤
          k * (P[fun ω => (pathDist IA IC U V U' V' t T ω).toReal | 𝓕 t]) ω := by
  exact d35_lip_core P 𝓕 T β hT husual IA IC hdom k f g Y J hyp U V U' V' hU hV hU' hV'
