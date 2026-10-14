-- Prove2me | solution 1 for AntonelliBFSDE.SingularExample.example_1_positive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:00:33.782558+00:00
-- url     : https://prove2.me/submissions/98ec8811-0c4e-4315-8d03-f0d56785ecf6

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal


namespace AntonelliBFSDE.SingularExample

open Set Filter Topology

lemma d34_fub_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (G : ℝ × Ω → ℝ) (hG : Measurable G)
    (hfin : ∫⁻ ω, ∫⁻ r in Ioc 0 T, ‖G (r, ω)‖ₑ ∂volume ∂P < ⊤) {s t : ℝ} (hs : 0 ≤ s)
    (ht : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc s t, G (r, ω)) P ∧
    ∫ ω, ∫ r in Ioc s t, G (r, ω) ∂volume ∂P = ∫ r in Ioc s t, ∫ ω, G (r, ω) ∂P ∧
    IntegrableOn (fun r => ∫ ω, G (r, ω) ∂P) (Ioc s t) := by
  have hint : Integrable G ((volume.restrict (Ioc s t)).prod P) := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod_symm' _ hG.enorm]
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    exact lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc hs ht) le_rfl) le_rfl
  refine ⟨hint.integral_prod_right, ?_, hint.integral_prod_left⟩
  exact (integral_integral_swap (f := fun r ω => G (r, ω)) hint).symm

lemma d34_procFub {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (hX : AntonelliBFSDE.SingularExample.MemL1Dt P T X)
    (A : Set Ω) (hA : MeasurableSet A) (w : ℝ → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K)
    (hwb : ∀ r ∈ Ioc (0:ℝ) T, |w r| ≤ K) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc s t, w r * X r.toNNReal ω) P ∧
    ∫ ω in A, ∫ r in Ioc s t, w r * X r.toNNReal ω ∂volume ∂P
      = ∫ r in Ioc s t, w r * ∫ ω in A, X r.toNNReal ω ∂P ∧
    IntegrableOn (fun r => ∫ ω in A, X r.toNNReal ω ∂P) (Ioc s t) := by
  have hsub : Ioc s t ⊆ Ioc (0:ℝ) T := Ioc_subset_Ioc hs ht
  let X' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then X p.1.toNNReal p.2 else 0
  have hX'm : Measurable X' := hX.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hX'eq : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, X' (r, ω) = X r.toNNReal ω := by
    intro r hr ω
    have : r.toNNReal ≤ T := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp [X', this]
  have hfinX : ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖X' (r, ω)‖ₑ ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hX.2
    unfold AntonelliBFSDE.SingularExample.L1NormDt
    exact lintegral_congr fun ω =>
      setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hX'eq r hr ω])
  have hfin : ∀ (c : ℝ) (G : ℝ × Ω → ℝ), 0 ≤ c →
      (∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G (r, ω)‖ ≤ c * ‖X' (r, ω)‖) →
      ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖G (r, ω)‖ₑ ∂volume ∂P < ⊤ := by
    intro c G hc hG
    calc ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖G (r, ω)‖ₑ ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ENNReal.ofReal c * ‖X' (r, ω)‖ₑ ∂volume ∂P := by
          refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hc]
          exact ENNReal.ofReal_le_ofReal (hG r hr ω)
      _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖X' (r, ω)‖ₑ ∂volume ∂P := by
          simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinX
  let G1 : ℝ × Ω → ℝ := fun p => w p.1 * X' p
  have hG1m : Measurable G1 := (hw.comp measurable_fst).mul hX'm
  have hG1b : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G1 (r, ω)‖ ≤ K * ‖X' (r, ω)‖ := by
    intro r hr ω
    simp only [G1, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hwb r hr) (abs_nonneg _)
  let G2 : ℝ × Ω → ℝ := (Prod.snd ⁻¹' A).indicator G1
  have hG2m : Measurable G2 := hG1m.indicator (measurable_snd hA)
  have hG2eq : ∀ r ω, G2 (r, ω) = A.indicator (fun ω => G1 (r, ω)) ω := by
    intro r ω; by_cases h : ω ∈ A <;> simp [G2, h]
  have hG2b : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G2 (r, ω)‖ ≤ K * ‖X' (r, ω)‖ := by
    intro r hr ω
    rw [hG2eq]
    by_cases h : ω ∈ A
    · simp only [h, indicator_of_mem]; exact hG1b r hr ω
    · simp only [h, not_false_eq_true, indicator_of_notMem, norm_zero]; positivity
  let G3 : ℝ × Ω → ℝ := (Prod.snd ⁻¹' A).indicator X'
  have hG3m : Measurable G3 := hX'm.indicator (measurable_snd hA)
  have hG3eq : ∀ r ω, G3 (r, ω) = A.indicator (fun ω => X' (r, ω)) ω := by
    intro r ω; by_cases h : ω ∈ A <;> simp [G3, h]
  have hG3b : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G3 (r, ω)‖ ≤ 1 * ‖X' (r, ω)‖ := by
    intro r hr ω
    rw [hG3eq, one_mul]
    by_cases h : ω ∈ A
    · simp [h]
    · simp [h]
  obtain ⟨i1, -, -⟩ := d34_fub_core P T G1 hG1m (hfin K G1 hK hG1b) hs ht
  obtain ⟨-, e2, -⟩ := d34_fub_core P T G2 hG2m (hfin K G2 hK hG2b) hs ht
  obtain ⟨-, -, i3⟩ := d34_fub_core P T G3 hG3m (hfin 1 G3 zero_le_one hG3b) hs ht
  have hin1 : ∀ ω, ∫ r in Ioc s t, G1 (r, ω) = ∫ r in Ioc s t, w r * X r.toNNReal ω := by
    intro ω
    exact setIntegral_congr_fun measurableSet_Ioc (fun r hr => by
      simp only [G1]; rw [hX'eq r (hsub hr) ω])
  refine ⟨i1.congr (ae_of_all _ hin1), ?_, ?_⟩
  · rw [← integral_indicator hA]
    have h1 : ∀ ω, A.indicator (fun ω => ∫ r in Ioc s t, w r * X r.toNNReal ω) ω
        = ∫ r in Ioc s t, G2 (r, ω) := by
      intro ω
      by_cases h : ω ∈ A
      · rw [indicator_of_mem h, ← hin1]
        exact setIntegral_congr_fun measurableSet_Ioc (fun r _ => by
          rw [hG2eq, indicator_of_mem h])
      · rw [indicator_of_notMem h]
        symm
        refine (setIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)).trans (integral_zero _ _)
        show G2 (r, ω) = 0
        rw [hG2eq, indicator_of_notMem h]
    simp_rw [h1]
    rw [e2]
    refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    simp only [hG2eq]
    rw [integral_indicator hA, ← integral_const_mul]
    refine setIntegral_congr_fun hA (fun ω _ => ?_)
    simp only [G1]; rw [hX'eq r (hsub hr) ω]
  · refine i3.congr_fun (fun r hr => ?_) measurableSet_Ioc
    simp only [hG3eq]
    rw [integral_indicator hA]
    refine setIntegral_congr_fun hA (fun ω _ => ?_)
    rw [hX'eq r (hsub hr) ω]

lemma d34_procFub1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (hX : AntonelliBFSDE.SingularExample.MemL1Dt P T X)
    (A : Set Ω) (hA : MeasurableSet A) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc s t, X r.toNNReal ω) P ∧
    ∫ ω in A, ∫ r in Ioc s t, X r.toNNReal ω ∂volume ∂P
      = ∫ r in Ioc s t, ∫ ω in A, X r.toNNReal ω ∂P ∧
    IntegrableOn (fun r => ∫ ω in A, X r.toNNReal ω ∂P) (Ioc s t) := by
  have := d34_procFub P T X hX A hA (fun _ => 1) measurable_const 1 zero_le_one
    (fun r _ => by simp) hs ht
  simpa using this

lemma d34_L1zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (D : ℝ≥0 → Ω → ℝ)
    (hDm : Measurable (Function.uncurry (fun t ω => if t ≤ T then D t ω else 0)))
    (hD : ∀ t ≤ T, D t =ᵐ[P] 0) :
    AntonelliBFSDE.SingularExample.L1NormDt P T D = 0 := by
  unfold AntonelliBFSDE.SingularExample.L1NormDt
  let D' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then D p.1.toNNReal p.2 else 0
  have hD'm : Measurable D' := hDm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hT' : ∀ r ∈ Ioc (0:ℝ) T, r.toNNReal ≤ T := fun r hr => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have h1 : ∀ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖D r.toNNReal ω‖ₑ = ∫⁻ r in Ioc 0 (T:ℝ), ‖D' (r, ω)‖ₑ :=
    fun ω => setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by simp [D', hT' r hr])
  simp_rw [h1]
  rw [lintegral_lintegral_swap (f := fun ω r => ‖D' (r, ω)‖ₑ)
    ((hD'm.comp measurable_swap).enorm.aemeasurable)]
  refine le_antisymm ?_ (by simp)
  calc ∫⁻ r in Ioc 0 (T:ℝ), ∫⁻ ω, ‖D' (r, ω)‖ₑ ∂P ≤ ∫⁻ r in Ioc 0 (T:ℝ), 0 := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => le_of_eq ?_
        rw [lintegral_congr_ae (g := fun _ => (0:ℝ≥0∞)) ((hD _ (hT' r hr)).mono fun ω h => by
          simp [D', hT' r hr, h])]
        simp
    _ = 0 := lintegral_zero

lemma d34_ae_path {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (D : ℝ≥0 → Ω → ℝ)
    (hDm : Measurable (Function.uncurry (fun t ω => if t ≤ T then D t ω else 0)))
    (h0 : AntonelliBFSDE.SingularExample.L1NormDt P T D = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Ioc (0:ℝ) T)), D s.toNNReal ω = 0 := by
  unfold AntonelliBFSDE.SingularExample.L1NormDt at h0
  let D' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then D p.1.toNNReal p.2 else 0
  have hD'm : Measurable D' := hDm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hT' : ∀ r ∈ Ioc (0:ℝ) T, r.toNNReal ≤ T := fun r hr => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have h1 : ∀ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖D r.toNNReal ω‖ₑ = ∫⁻ r in Ioc 0 (T:ℝ), ‖D' (r, ω)‖ₑ :=
    fun ω => setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by simp [D', hT' r hr])
  simp_rw [h1] at h0
  have hm : Measurable fun ω => ∫⁻ r in Ioc 0 (T:ℝ), ‖D' (r, ω)‖ₑ :=
    Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => ‖D' (p.2, p.1)‖ₑ)
      (hD'm.comp measurable_swap).enorm
  rw [lintegral_eq_zero_iff hm] at h0
  filter_upwards [h0] with ω hω
  have hω' : ∫⁻ r in Ioc 0 (T:ℝ), ‖D' (r, ω)‖ₑ = 0 := hω
  have hsm : Measurable fun r : ℝ => ‖D' (r, ω)‖ₑ :=
    (hD'm.comp (measurable_id.prodMk measurable_const)).enorm
  filter_upwards [(lintegral_eq_zero_iff hsm).1 hω', ae_restrict_mem measurableSet_Ioc] with s hs hsI
  have : ‖D' (s, ω)‖ₑ = 0 := hs
  rw [enorm_eq_zero] at this
  simpa [D', hT' s hsI] using this

lemma d34_prim_meas {Ω : Type*} [MeasurableSpace Ω] (F : ℝ × Ω → ℝ) (hF : Measurable F) :
    Measurable (fun p : ℝ≥0 × Ω => ∫ s in Ioc (0:ℝ) p.1, F (s, p.2)) := by
  let G : (ℝ≥0 × Ω) × ℝ → ℝ := fun q => if 0 < q.2 ∧ q.2 ≤ q.1.1 then F (q.2, q.1.2) else 0
  have hG : Measurable G := by
    refine Measurable.ite ?_ (hF.comp (measurable_snd.prodMk measurable_fst.snd)) measurable_const
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst.coe_nnreal_real)
  have e : (fun p : ℝ≥0 × Ω => ∫ s in Ioc (0:ℝ) p.1, F (s, p.2)) =
      fun p => ∫ s, G (p, s) ∂volume := by
    funext p
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
    funext s
    simp only [G, Set.indicator_apply, mem_Ioc]
  rw [e]
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

lemma d34_memL1_of {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1Dt P T U) (hV : MemL1Dt P T V)
    (F : ℝ → ℝ → ℝ) (hF : Measurable (Function.uncurry F)) (hF0 : F 0 0 = 0)
    (hFb : ∀ x y, |F x y| ≤ |x| + |y|) :
    MemL1Dt P T (fun t ω => F (U t ω) (V t ω)) := by
  have hT' : ∀ r ∈ Ioc (0:ℝ) T, r.toNNReal ≤ T := fun r hr => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  let U' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then U p.1.toNNReal p.2 else 0
  let V' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then V p.1.toNNReal p.2 else 0
  have hU'm : Measurable U' := hU.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hV'm : Measurable V' := hV.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  constructor
  · have e : (Function.uncurry fun t ω => if t ≤ T then F (U t ω) (V t ω) else 0) =
        fun p => Function.uncurry F ((Function.uncurry (fun t ω => if t ≤ T then U t ω else 0)) p,
          (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) p) := by
      funext p; simp only [Function.uncurry]; split_ifs <;> simp [hF0]
    rw [e]; exact hF.comp (hU.1.prodMk hV.1)
  · have hfU : ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖U' (r, ω)‖ₑ ∂volume ∂P < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq ?_) hU.2
      unfold L1NormDt
      exact lintegral_congr fun ω =>
        setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by simp [U', hT' r hr])
    have hfV : ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖V' (r, ω)‖ₑ ∂volume ∂P < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq ?_) hV.2
      unfold L1NormDt
      exact lintegral_congr fun ω =>
        setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by simp [V', hT' r hr])
    unfold L1NormDt
    calc ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖F (U r.toNNReal ω) (V r.toNNReal ω)‖ₑ ∂volume ∂P
        ≤ ∫⁻ ω, ((∫⁻ r in Ioc 0 (T:ℝ), ‖U' (r, ω)‖ₑ) + ∫⁻ r in Ioc 0 (T:ℝ), ‖V' (r, ω)‖ₑ) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hm : Measurable fun r => ‖U' (r, ω)‖ₑ :=
            (hU'm.comp (measurable_id.prodMk measurable_const)).enorm
          rw [← lintegral_add_left hm]
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          simp only [U', V', hT' r hr, if_true]
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _)
            (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hFb _ _)
      _ = (∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖U' (r, ω)‖ₑ ∂volume ∂P) +
            ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖V' (r, ω)‖ₑ ∂volume ∂P := by
          rw [lintegral_add_left]
          exact Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => ‖U' (p.2, p.1)‖ₑ)
            (hU'm.comp measurable_swap).enorm
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hfU, hfV⟩

lemma d34_memL1_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1Dt P T U) (hV : MemL1Dt P T V) :
    MemL1Dt P T (fun t ω => U t ω + V t ω) :=
  d34_memL1_of P T U V hU hV (fun x y => x + y) (by fun_prop) (by simp)
    (fun x y => abs_add_le x y)

lemma d34_memL1_add_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1Dt P T U) (hV : MemL1Dt P T V) :
    MemL1Dt P T (fun t ω => U t ω + |V t ω|) :=
  d34_memL1_of P T U V hU hV (fun x y => x + |y|) (by fun_prop) (by simp)
    (fun x y => by simpa using abs_add_le x |y|)

/-- expectation-level system. -/
lemma d34_sys {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) (f g : ℝ → ℝ → ℝ) (hJint : Integrable J₀ P)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ f g Y U V)
    (hF : MemL1Dt P T (fun t ω => f (U t ω) (V t ω)))
    (hG : MemL1Dt P T (fun t ω => g (U t ω) (V t ω)))
    (t0 : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 t0] A) :
    IntegrableOn (fun r : ℝ => ∫ ω in A, f (U r.toNNReal ω) (V r.toNNReal ω) ∂P) (Ioc 0 T) ∧
    IntegrableOn (fun r : ℝ => ∫ ω in A, g (U r.toNNReal ω) (V r.toNNReal ω) ∂P) (Ioc 0 T) ∧
    (∀ x ∈ Icc (0:ℝ) T, Integrable (U x.toNNReal) P ∧ (∫ ω in A, U x.toNNReal ω ∂P) =
      (∫ ω in A, J₀ ω ∂P) + ∫ r in Ioc 0 x, ∫ ω in A, f (U r.toNNReal ω) (V r.toNNReal ω) ∂P) ∧
    (∀ x ∈ Icc (t0:ℝ) T, Integrable (V x.toNNReal) P ∧ (∫ ω in A, V x.toNNReal ω ∂P) =
      (∫ ω in A, Y ω ∂P) + ∫ r in Ioc x T, ∫ ω in A, g (U r.toNNReal ω) (V r.toNNReal ω) ∂P) ∧
    Integrable Y P := by
  obtain ⟨hU, hV, hUad, hVad, hpath, hξ, W, hW, hUV, hVT⟩ := hsol
  have hAm : MeasurableSet A := 𝓕.le t0 A hA
  have hYint : Integrable Y P := by
    have h := hξ T le_rfl
    have e : xiDt T g Y U V T = Y := by
      funext ω; unfold xiDt; simp
    rwa [e] at h
  refine ⟨(d34_procFub1 P T _ hF A hAm le_rfl le_rfl).2.2,
    (d34_procFub1 P T _ hG A hAm le_rfl le_rfl).2.2, ?_, ?_, hYint⟩
  · intro x hx
    have htx : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx.1
    have htxT : x.toNNReal ≤ T := by rw [← NNReal.coe_le_coe, htx]; exact hx.2
    have h1 := (hUV x.toNNReal htxT).1
    simp only [htx] at h1
    obtain ⟨i1, e1, -⟩ := d34_procFub1 P T _ hF A hAm le_rfl hx.2
    obtain ⟨i1', -, -⟩ := d34_procFub1 P T _ hF univ MeasurableSet.univ le_rfl hx.2
    refine ⟨(hJint.add i1').congr h1.symm, ?_⟩
    rw [integral_congr_ae (ae_restrict_of_ae h1), integral_add hJint.integrableOn i1.integrableOn,
      e1]
  · intro x hx
    have hx0 : (0:ℝ) ≤ x := le_trans t0.2 hx.1
    have htx : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx0
    have htxT : x.toNNReal ≤ T := by rw [← NNReal.coe_le_coe, htx]; exact hx.2
    have ht0x : t0 ≤ x.toNNReal := by rw [← NNReal.coe_le_coe, htx]; exact hx.1
    have hAx : MeasurableSet[𝓕 x.toNNReal] A := 𝓕.mono ht0x A hA
    have h1 := (hUV x.toNNReal htxT).2
    have h2 := hW.2.2 x.toNNReal htxT
    refine ⟨integrable_condExp.congr (h1.trans h2).symm, ?_⟩
    rw [integral_congr_ae (ae_restrict_of_ae (h1.trans h2)),
      setIntegral_condExp (𝓕.le _) (hξ _ htxT) hAx]
    obtain ⟨i1, e1, -⟩ := d34_procFub1 P T _ hG A hAm hx0 le_rfl
    simp only [xiDt, htx]
    rw [integral_add i1.integrableOn hYint.integrableOn, e1, add_comm]

lemma d34_Jpos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J₀ Y : Ω → ℝ) (hJint : Integrable J₀ P) (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYint : Integrable Y P) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω) :
    0 < ∫ ω, J₀ ω + Y ω ∂P := by
  rw [integral_add hJint hYint]
  have hJ0 : 0 ≤ ∫ ω, J₀ ω ∂P := integral_nonneg_of_ae (hJpos.mono fun ω h => h.le)
  have hY0 : 0 ≤ ∫ ω, Y ω ∂P := integral_nonneg_of_ae (hYpos.mono fun ω h => h.le)
  have hJne : ∫ ω, J₀ ω ∂P ≠ 0 := by
    intro hJz
    rw [integral_eq_zero_iff_of_nonneg_ae (hJpos.mono fun ω h => h.le) hJint] at hJz
    obtain ⟨ω, h1, h2⟩ := (hJz.and hJpos).exists
    rw [h1] at h2
    exact lt_irrefl _ h2
  have := lt_of_le_of_ne hJ0 (Ne.symm hJne)
  linarith

theorem example_1_beta_core {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V) :
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      Integrable (fun ω => U r.toNNReal ω + V r.toNNReal ω) P ∧
      (∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P) =
        (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) ∧
      (∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P) =
        (∫ ω, J₀ ω ∂P) +
        (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ ω, U s.toNNReal ω + V s.toNNReal ω ∂P) +
        (∫ ω, Y ω ∂P)) ∧
    (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) *
      (1 - (T : ℝ)) = ∫ ω, J₀ ω + Y ω ∂P ∧
    0 < ∫ ω, J₀ ω + Y ω ∂P := by
  have hS := d34_memL1_add P T U V hsol.1 hsol.2.1
  obtain ⟨-, iG, hφ, hψ, hYint⟩ :=
    d34_sys P 𝓕 T J₀ Y U V (fun u v => u + v) (fun u v => u + v) hJint hsol hS hS 0 univ
      MeasurableSet.univ
  simp only [Measure.restrict_univ, NNReal.coe_zero] at hφ hψ iG
  set k : ℝ → ℝ := fun r => ∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P with hk_def
  set I : ℝ := ∫ r in Ioc (0:ℝ) T, k r with hI
  have hk : ∀ r ∈ Ioc (0:ℝ) T, Integrable (fun ω => U r.toNNReal ω + V r.toNNReal ω) P ∧
      k r = (∫ ω, J₀ ω ∂P) + (∫ ω, Y ω ∂P) + I := by
    intro r hr
    obtain ⟨iU, eU⟩ := hφ r ⟨hr.1.le, hr.2⟩
    obtain ⟨iV, eV⟩ := hψ r ⟨hr.1.le, hr.2⟩
    refine ⟨iU.add iV, ?_⟩
    simp only [hk_def]
    rw [integral_add iU iV, eU, eV, hI]
    have hu : Ioc (0:ℝ) r ∪ Ioc r (T:ℝ) = Ioc 0 (T:ℝ) := Ioc_union_Ioc_eq_Ioc hr.1.le hr.2
    rw [← hu, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (iG.mono_set (Ioc_subset_Ioc le_rfl hr.2)) (iG.mono_set (Ioc_subset_Ioc hr.1.le le_rfl))]
    ring
  have hxi : Integrable (xiDt T (fun u v => u + v) Y U V 0) P := hsol.2.2.2.2.2.1 0 bot_le
  have eXi : (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) =
      (∫ ω, J₀ ω ∂P) + I + (∫ ω, Y ω ∂P) := by
    obtain ⟨i1, e1, -⟩ := d34_procFub1 P T _ hS univ MeasurableSet.univ le_rfl le_rfl
    simp only [Measure.restrict_univ] at e1
    rw [integral_add hJint hxi]
    simp only [xiDt, NNReal.coe_zero]
    rw [integral_add i1 hYint, e1]
    ring
  have hIT : I = (T:ℝ) * ((∫ ω, J₀ ω ∂P) + (∫ ω, Y ω ∂P) + I) := by
    have h1 : I = (volume (Ioc (0:ℝ) T)).toReal • ((∫ ω, J₀ ω ∂P) + (∫ ω, Y ω ∂P) + I) :=
      (setIntegral_congr_fun measurableSet_Ioc (fun r hr => (hk r hr).2)).trans
        (setIntegral_const _)
    simp only [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg T),
      smul_eq_mul] at h1
    exact h1
  refine ⟨(ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_), ?_,
    d34_Jpos P J₀ Y hJint hJpos hYint hYpos⟩
  · refine ⟨(hk r hr).1, ?_, ?_⟩
    · show k r = _
      rw [(hk r hr).2, eXi]; ring
    · show k r = _
      rw [(hk r hr).2]; ring
  · rw [eXi, integral_add hJint hYint]
    linarith

lemma d34_key {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V) (t : ℝ≥0) (ht : t ≤ T) :
    (fun ω => U t ω + V t ω) =ᵐ[P]
      (fun ω => J₀ ω + P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] ω) := by
  have hS := d34_memL1_add P T U V hsol.1 hsol.2.1
  obtain ⟨hU, hV, hUad, hVad, hpath, hξ, W, hW, hUV, hVT⟩ := hsol
  have h1 := (hUV t ht).1
  have h2 := (hUV t ht).2.trans (hW.2.2 t ht)
  obtain ⟨Z, hZ⟩ : ∃ Z : Ω → ℝ, Z = fun ω => ∫ s in Ioc (0:ℝ) t, (U s.toNNReal ω + V s.toNNReal ω) :=
    ⟨_, rfl⟩
  have hZi : Integrable Z P := by
    have := (d34_procFub1 P T _ hS univ MeasurableSet.univ le_rfl (t := t)
      (by exact_mod_cast ht)).1
    rw [hZ]; exact this
  have hJt : StronglyMeasurable[𝓕 t] J₀ :=
    (hJmeas.mono (𝓕.mono (bot_le : (0:ℝ≥0) ≤ t)) le_rfl).stronglyMeasurable
  have hZm : AEStronglyMeasurable[𝓕 t] Z P := by
    refine (((hUad t ht).stronglyMeasurable.sub hJt).aestronglyMeasurable).congr ?_
    filter_upwards [h1] with ω hω
    rw [Pi.sub_apply, hω, hZ]
    beta_reduce
    ring
  have hxi : xiDt T (fun u v => u + v) Y U V 0 =ᵐ[P]
      Z + xiDt T (fun u v => u + v) Y U V t := by
    filter_upwards [hpath] with ω hω
    have hg := hω.2
    rw [Pi.add_apply, hZ]
    simp only [xiDt, NNReal.coe_zero]
    have hu : Ioc (0:ℝ) t ∪ Ioc (t:ℝ) T = Ioc 0 (T:ℝ) :=
      Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg t) (by exact_mod_cast ht)
    rw [← hu, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hg.mono_set (Ioc_subset_Ioc le_rfl (by exact_mod_cast ht)))
      (hg.mono_set (Ioc_subset_Ioc (NNReal.coe_nonneg t) le_rfl))]
    ring
  have hc1 : P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] =ᵐ[P]
      P[Z | 𝓕 t] + P[xiDt T (fun u v => u + v) Y U V t | 𝓕 t] :=
    (condExp_congr_ae hxi).trans (condExp_add hZi (hξ t ht) _)
  have hc2 : P[Z | 𝓕 t] =ᵐ[P] Z := condExp_of_aestronglyMeasurable' (𝓕.le t) hZm hZi
  filter_upwards [h1, h2, hc1, hc2] with ω e1 e2 e3 e4
  rw [e3, Pi.add_apply, e4, e2, e1, hZ]
  beta_reduce
  ring

theorem example_1_martingale_core {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V) :
    ∃ N : ℝ≥0 → Ω → ℝ,
      Measurable (Function.uncurry N) ∧
      (∀ t ≤ T, Integrable (N t) P ∧ StronglyMeasurable[𝓕 t] (N t) ∧
        N t =ᵐ[P] (fun ω => J₀ ω + P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] ω)) ∧
      (∀ s ≤ T, ∀ t ≤ T, s ≤ t → N s =ᵐ[P] P[N t | 𝓕 s]) ∧
      L1NormDt P T (fun t ω => U t ω + V t ω - N t ω) = 0 := by
  have hkey := d34_key P 𝓕 T J₀ Y U V hJmeas hJint hsol
  let N : ℝ≥0 → Ω → ℝ := fun t ω => if t ≤ T then U t ω + V t ω else 0
  have hNt : ∀ t ≤ T, N t = fun ω => U t ω + V t ω := fun t ht => by
    funext ω; simp [N, ht]
  have hN : ∀ t ≤ T, N t =ᵐ[P] (fun ω => J₀ ω + P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] ω) :=
    fun t ht => by rw [hNt t ht]; exact hkey t ht
  refine ⟨N, ?_, fun t ht => ⟨?_, ?_, hN t ht⟩, ?_, ?_⟩
  · have e : Function.uncurry N =
        fun p => (Function.uncurry (fun t ω => if t ≤ T then U t ω else 0)) p +
          (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) p := by
      funext p; simp only [Function.uncurry, N]; split_ifs <;> simp
    rw [e]; exact hsol.1.1.add hsol.2.1.1
  · exact (hJint.add integrable_condExp).congr (hN t ht).symm
  · rw [hNt t ht]
    exact ((hsol.2.2.1 t ht).add (hsol.2.2.2.1 t ht)).stronglyMeasurable
  · intro s hs t ht hst
    have hJs : StronglyMeasurable[𝓕 s] J₀ :=
      (hJmeas.mono (𝓕.mono (bot_le : (0:ℝ≥0) ≤ s)) le_rfl).stronglyMeasurable
    have e1 : P[N t | 𝓕 s] =ᵐ[P]
        P[J₀ | 𝓕 s] + P[P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] | 𝓕 s] :=
      (condExp_congr_ae (hN t ht)).trans (condExp_add hJint integrable_condExp _)
    have e2 : P[J₀ | 𝓕 s] = J₀ := condExp_of_stronglyMeasurable (𝓕.le s) hJs hJint
    have e3 : P[P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] | 𝓕 s] =ᵐ[P]
        P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 s] := condExp_condExp_of_le (𝓕.mono hst) (𝓕.le t)
    filter_upwards [e1, e3, hN s hs] with ω h1 h2 h3
    rw [h1, h3, Pi.add_apply, e2, h2]
  · apply d34_L1zero
    · have e : (Function.uncurry fun t ω => if t ≤ T then U t ω + V t ω - N t ω else 0) =
          fun _ => (0:ℝ) := by
        funext p; simp only [Function.uncurry, N]; split_ifs <;> simp
      rw [e]; exact measurable_const
    · intro t ht
      exact Eventually.of_forall fun ω => by simp [N, ht]

lemma d34_const {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f b = f a := by
  obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0:ℝ)) hab hc hd
  have hne : b - a ≠ 0 := by linarith
  have h := hc'.symm
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hne

/-- forward linear equation with integrable forcing, solved pathwise. -/
lemma d34_ode1 {u w : ℝ → ℝ} {J T : ℝ} (hT : 0 ≤ T) (hu : IntegrableOn u (Ioc 0 T))
    (hw : IntegrableOn w (Ioc 0 T))
    (h : ∀ᵐ r ∂(volume.restrict (Ioc 0 T)), u r = J + ∫ s in Ioc 0 r, (u s + w s)) :
    ∀ᵐ r ∂(volume.restrict (Ioc 0 T)),
      u r = Real.exp r * (J + ∫ s in Ioc 0 r, Real.exp (-s) * w s) := by
  have hg : IntervalIntegrable (fun s => u s + w s) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hu.add hw)
  have hew : IntegrableOn (fun s => Real.exp (-s) * w s) (Ioc 0 T) := by
    refine hw.bdd_mul (c := Real.exp 0) ?_ ?_
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (by linarith [hs.1])
  have hm : IntervalIntegrable (fun s => Real.exp (-s) * w s) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hew
  have h0mem : (0:ℝ) ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ⟨le_rfl, hT⟩
  let F : ℝ → ℝ := fun x => J + ∫ s in (0:ℝ)..x, (u s + w s)
  let M : ℝ → ℝ := fun x => ∫ s in (0:ℝ)..x, Real.exp (-s) * w s
  let H : ℝ → ℝ := fun x => Real.exp (-x) * F x - M x
  have hFac : AbsolutelyContinuousOnInterval F 0 T := by
    have h1 := hg.absolutelyContinuousOnInterval_intervalIntegral h0mem
    have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => J) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    exact h2.add h1
  have hMac : AbsolutelyContinuousOnInterval M 0 T :=
    hm.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hEac : AbsolutelyContinuousOnInterval (fun x : ℝ => Real.exp (-x)) 0 T :=
    (Real.contDiff_exp.comp contDiff_neg).contDiffOn.absolutelyContinuousOnInterval
  have hHac : AbsolutelyContinuousOnInterval H 0 T := (hEac.mul hFac).sub hMac
  have hD1 := hg.ae_hasDerivAt_integral
  have hD2 := hm.ae_hasDerivAt_integral
  have h' := (ae_restrict_iff' measurableSet_Ioc).1 h
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
  have hHd : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt H 0 x := by
    filter_upwards [hD1, hD2, h', hne] with x h1 h2 h3 h4 hx
    rw [uIcc_of_le hT] at hx
    have hxI : x ∈ Ioc 0 T := ⟨lt_of_le_of_ne hx.1 (Ne.symm h4), hx.2⟩
    have hx' : x ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact hx
    have d1 := (h1 hx' 0 h0mem).const_add J
    have d2 := h2 hx' 0 h0mem
    have dE : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
      (hasDerivAt_neg x).exp
    have hFx : F x = u x := by
      rw [h3 hxI]
      simp only [F]
      rw [intervalIntegral.integral_of_le hxI.1.le]
    have := (dE.mul d1).sub d2
    refine this.congr_deriv ?_
    have : J + ∫ s in (0:ℝ)..x, (u s + w s) = u x := hFx
    rw [this]; ring
  obtain ⟨C, hC⟩ := hHac.const_of_ae_hasDerivAt_zero hHd
  have hH0 : H 0 = J := by simp [H, F, M]
  have hHx : ∀ x ∈ Icc 0 T, F x = Real.exp x * (J + M x) := by
    intro x hx
    have e1 := hC x (by rw [uIcc_of_le hT]; exact hx)
    have e0 := hC 0 h0mem
    rw [hH0] at e0
    have e2 : Real.exp (-x) * F x - M x = J := by
      have : H x = J := e1.trans e0.symm
      exact this
    have hex : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    calc F x = Real.exp x * (Real.exp (-x) * F x) := by rw [← mul_assoc, hex, one_mul]
      _ = Real.exp x * (J + M x) := by rw [show Real.exp (-x) * F x = J + M x by linarith]
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with r hr hrI
  rw [hr]
  have := hHx r ⟨hrI.1.le, hrI.2⟩
  simp only [F, M] at this
  rw [intervalIntegral.integral_of_le hrI.1.le, intervalIntegral.integral_of_le hrI.1.le] at this
  exact this

/-- backward linear equation with continuous forcing. -/
lemma d34_ode2 {φ ψ : ℝ → ℝ} {t T d : ℝ} (htT : t ≤ T)
    (hφc : ContinuousOn φ (Icc t T)) (hψi : IntegrableOn ψ (Ioc t T))
    (hψ : ∀ x ∈ Icc t T, ψ x = d + ∫ r in Ioc x T, (φ r + ψ r)) :
    ψ t = Real.exp (T - t) * d + ∫ r in Ioc t T, Real.exp (r - t) * φ r := by
  rcases eq_or_lt_of_le htT with heq | hlt
  · subst heq; rw [hψ t ⟨le_rfl, le_rfl⟩]; simp
  have hφi : IntegrableOn φ (Ioc t T) :=
    (hφc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hgi : IntegrableOn (fun r => φ r + ψ r) (Ioc t T) := hφi.add hψi
  have hgii : IntervalIntegrable (fun r => φ r + ψ r) volume t T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le htT).2 hgi
  have hψ' : ∀ x ∈ Icc t T, ψ x = d + ((∫ r in t..T, (φ r + ψ r)) - ∫ r in t..x, (φ r + ψ r)) := by
    intro x hx
    rw [hψ x hx, intervalIntegral.integral_interval_sub_left hgii
      (hgii.mono_set (by rw [uIcc_of_le htT, uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2)),
      intervalIntegral.integral_of_le hx.2]
  have hPc : ContinuousOn (fun x => ∫ r in t..x, (φ r + ψ r)) (Icc t T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun r => φ r + ψ r) (a := t) (b := T) (by rw [uIcc_of_le htT, integrableOn_Icc_iff_integrableOn_Ioc]; exact hgi)
    rwa [uIcc_of_le htT] at this
  have hψc : ContinuousOn ψ (Icc t T) :=
    (continuousOn_const.add (continuousOn_const.sub hPc)).congr hψ'
  have hgc : ContinuousOn (fun r => φ r + ψ r) (Icc t T) := hφc.add hψc
  have hnhds : ∀ x ∈ Ioo t T, Icc t T ∈ 𝓝 x := fun x hx => Icc_mem_nhds hx.1 hx.2
  have hDψ : ∀ x ∈ Ioo t T, HasDerivAt ψ (-(φ x + ψ x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y => ∫ r in t..y, (φ r + ψ r)) (φ x + ψ x) x :=
      intervalIntegral.integral_hasDerivAt_right
        (hgii.mono_set (by rw [uIcc_of_le htT, uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le))
        ((hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
        (hgc.continuousAt (hnhds x hx))
    refine ((h1.const_sub (∫ r in t..T, (φ r + ψ r))).const_add d).congr_of_eventuallyEq ?_
    filter_upwards [hnhds x hx] with y hy
    exact hψ' y hy
  have hec : ContinuousOn (fun r => Real.exp r * φ r) (Icc t T) :=
    Real.continuous_exp.continuousOn.mul hφc
  have hPe : ContinuousOn (fun y => ∫ r in t..y, Real.exp r * φ r) (Icc t T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun r => Real.exp r * φ r) (a := t) (b := T) (by
        rw [uIcc_of_le htT]; exact hec.integrableOn_compact isCompact_Icc)
    rwa [uIcc_of_le htT] at this
  have hDe : ∀ x ∈ Ioo t T, HasDerivAt (fun y => ∫ r in t..y, Real.exp r * φ r)
      (Real.exp x * φ x) x := by
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_right
      ((hec.mono (uIcc_subset_Icc ⟨le_rfl, htT⟩ ⟨hx.1.le, hx.2.le⟩)).intervalIntegrable)
      ((hec.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (hec.continuousAt (hnhds x hx))
  have e := d34_const (f := fun y => Real.exp y * ψ y + ∫ r in t..y, Real.exp r * φ r) hlt
    ((Real.continuous_exp.continuousOn.mul hψc).add hPe) (by
      intro x hx
      have h := ((Real.hasDerivAt_exp x).mul (hDψ x hx)).add (hDe x hx)
      exact h.congr_deriv (by ring))
  have hψT : ψ T = d := by rw [hψ T ⟨htT, le_rfl⟩]; simp
  simp only [intervalIntegral.integral_same, add_zero, hψT] at e
  rw [intervalIntegral.integral_of_le htT] at e
  have hex : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have e2 : ∫ r in Ioc t T, Real.exp (r - t) * φ r = Real.exp (-t) * ∫ r in Ioc t T, Real.exp r * φ r := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)
    rw [sub_eq_add_neg, Real.exp_add]; ring
  rw [e2, Real.exp_sub]
  have : ψ t = Real.exp (-t) * (Real.exp t * ψ t) := by rw [← mul_assoc, hex, one_mul]
  rw [this, ← e, Real.exp_neg]
  field_simp

lemma d34_path_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (hX : MemL1Dt P T X) :
    ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => X s.toNNReal ω) (Ioc 0 T) := by
  let X' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then X p.1.toNNReal p.2 else 0
  have hX'm : Measurable X' := hX.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hT' : ∀ r ∈ Ioc (0:ℝ) T, r.toNNReal ≤ T := fun r hr => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have key : ∫⁻ ω, ∫⁻ s in Ioc 0 (T:ℝ), ‖X' (s, ω)‖ₑ ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hX.2
    unfold L1NormDt
    exact lintegral_congr fun ω =>
      setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by simp [X', hT' r hr])
  have hm : Measurable fun ω => ∫⁻ r in Ioc 0 (T:ℝ), ‖X' (r, ω)‖ₑ :=
    Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => ‖X' (p.2, p.1)‖ₑ)
      (hX'm.comp measurable_swap).enorm
  filter_upwards [ae_lt_top hm key.ne] with ω hω
  have hsl : Measurable fun s : ℝ => X' (s, ω) := hX'm.comp (measurable_id.prodMk measurable_const)
  refine ⟨hsl.aestronglyMeasurable.congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [X', hT' s hs]
  · refine lt_of_le_of_lt (le_of_eq (setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_)) hω
    simp [X', hT' s hs]

lemma d34_Upath {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ → ℝ)
    (hJmeas : Measurable[𝓕 0] J₀)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|) g Y U V) :
    ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)),
      U r.toNNReal ω = Real.exp r * (J₀ ω + ∫ s in Ioc 0 r, Real.exp (-s) * |V s.toNNReal ω|) := by
  obtain ⟨hU, hV, hUad, hVad, hpath, hξ, W, hW, hUV, hVT⟩ := hsol
  have hJm : Measurable J₀ := hJmeas.mono (𝓕.le 0) le_rfl
  let D : ℝ≥0 → Ω → ℝ := fun t ω =>
    U t ω - (J₀ ω + ∫ s in Ioc (0:ℝ) t, (U s.toNNReal ω + |V s.toNNReal ω|))
  let G : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then
    U p.1.toNNReal p.2 + |V p.1.toNNReal p.2| else 0
  have hGm : Measurable G := by
    have e : G = fun p => (Function.uncurry (fun t ω => if t ≤ T then U t ω else 0))
        (p.1.toNNReal, p.2) +
        |(Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) (p.1.toNNReal, p.2)| := by
      funext p; simp only [G, Function.uncurry]; split_ifs <;> simp
    rw [e]
    exact (hU.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)).add
      (hV.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)).abs
  have hDm : Measurable (Function.uncurry (fun t ω => if t ≤ T then D t ω else 0)) := by
    have e : (Function.uncurry (fun t ω => if t ≤ T then D t ω else 0)) = fun p =>
        (Function.uncurry (fun t ω => if t ≤ T then U t ω else 0)) p -
        (if p.1 ≤ T then J₀ p.2 + ∫ s in Ioc (0:ℝ) p.1, G (s, p.2) else 0) := by
      funext p
      simp only [Function.uncurry, D]
      split_ifs with h
      · congr 2
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
        have : s.toNNReal ≤ T := by
          rw [Real.toNNReal_le_iff_le_coe]; exact hs.2.trans (by exact_mod_cast h)
        simp [G, this]
      · simp
    rw [e]
    refine hU.1.sub (Measurable.ite (measurableSet_le measurable_fst measurable_const)
      ((hJm.comp measurable_snd).add (d34_prim_meas G hGm)) measurable_const)
  have hD : ∀ t ≤ T, D t =ᵐ[P] 0 := by
    intro t ht
    filter_upwards [(hUV t ht).1] with ω hω
    simp only [D, Pi.zero_apply]
    rw [hω]; ring
  have hp := d34_ae_path P T D hDm (d34_L1zero P T D hDm hD)
  filter_upwards [hp, d34_path_int P T U hU, d34_path_int P T V hV] with ω h1 hu hv
  refine d34_ode1 (u := fun r => U r.toNNReal ω) (w := fun s => |V s.toNNReal ω|) (J := J₀ ω)
    (NNReal.coe_nonneg T) hu hv.abs ?_
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with r hr hrI
  simp only [D] at hr
  rw [Real.coe_toNNReal r hrI.1.le] at hr
  linarith

lemma d34_Vcond {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) (hJint : Integrable J₀ P)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
      (fun u v => u + v) Y U V) (t : ℝ≥0) (ht : t ≤ T) :
    Integrable (fun ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
        ∫ s in Set.Ioc (t : ℝ) (T : ℝ), Real.exp (s - (t : ℝ)) * U s.toNNReal ω) P ∧
    V t =ᵐ[P] P[fun ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
        ∫ s in Set.Ioc (t : ℝ) (T : ℝ), Real.exp (s - (t : ℝ)) * U s.toNNReal ω | 𝓕 t] := by
  have hF := d34_memL1_add_abs P T U V hsol.1 hsol.2.1
  have hG := d34_memL1_add P T U V hsol.1 hsol.2.1
  have htT : (t:ℝ) ≤ T := by exact_mod_cast ht
  have ht0 : (0:ℝ) ≤ t := NNReal.coe_nonneg t
  have hwb : ∀ r ∈ Ioc (0:ℝ) T, |(fun r : ℝ => Real.exp (r - t)) r| ≤ Real.exp T := by
    intro r hr
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [hr.2])
  have hwm : Measurable (fun r : ℝ => Real.exp (r - t)) := by fun_prop
  have hYint : Integrable Y P :=
    (d34_sys P 𝓕 T J₀ Y U V _ _ hJint hsol hF hG 0 univ MeasurableSet.univ).2.2.2.2
  have hpf := d34_procFub P T U hsol.1 univ MeasurableSet.univ _ hwm _ (Real.exp_pos _).le hwb
    ht0 le_rfl
  have hint : Integrable (fun ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
        ∫ s in Set.Ioc (t : ℝ) (T : ℝ), Real.exp (s - (t : ℝ)) * U s.toNNReal ω) P :=
    (hYint.const_mul _).add hpf.1
  refine ⟨hint, ?_⟩
  have hVt : V t =ᵐ[P] _ := (hsol.2.2.2.2.2.2.choose_spec.2.1 t ht).2.trans
    (hsol.2.2.2.2.2.2.choose_spec.1.2.2 t ht)
  have hVint : Integrable (V t) P := integrable_condExp.congr hVt.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) hint
    (fun _ _ _ => hVint.integrableOn) (fun A hA _ => ?_) (hsol.2.2.2.1 t ht).aestronglyMeasurable
  have hAm : MeasurableSet A := 𝓕.le t A hA
  obtain ⟨iF, iG, hφ, hψ, -⟩ := d34_sys P 𝓕 T J₀ Y U V _ _ hJint hsol hF hG t A hA
  set φ : ℝ → ℝ := fun x => ∫ ω in A, U x.toNNReal ω ∂P with hφdef
  set ψ : ℝ → ℝ := fun x => ∫ ω in A, V x.toNNReal ω ∂P with hψdef
  have hφc : ContinuousOn φ (Icc 0 T) := by
    have hI : IntegrableOn (fun r : ℝ => ∫ ω in A, (U r.toNNReal ω + |V r.toNNReal ω|) ∂P)
        (uIcc 0 T) := by
      rw [uIcc_of_le (NNReal.coe_nonneg T), integrableOn_Icc_iff_integrableOn_Ioc]; exact iF
    have hP := intervalIntegral.continuousOn_primitive_interval hI
    rw [uIcc_of_le (NNReal.coe_nonneg T)] at hP
    refine ((continuousOn_const (c := ∫ ω in A, J₀ ω ∂P)).add hP).congr (fun x hx => ?_)
    refine (hφ x hx).2.trans ?_
    simp only [Pi.add_apply]
    rw [intervalIntegral.integral_of_le hx.1]
  have hφi : IntegrableOn φ (Ioc t T) :=
    ((hφc.mono (Icc_subset_Icc ht0 le_rfl)).integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hsplit : ∀ r ∈ Ioc (t:ℝ) T,
      (∫ ω in A, (U r.toNNReal ω + V r.toNNReal ω) ∂P) = φ r + ψ r := by
    intro r hr
    have h0r : (0:ℝ) ≤ r := ht0.trans hr.1.le
    rw [integral_add (hφ r ⟨h0r, hr.2⟩).1.integrableOn (hψ r ⟨hr.1.le, hr.2⟩).1.integrableOn]
  have hψi : IntegrableOn ψ (Ioc t T) := by
    refine ((iG.mono_set (Ioc_subset_Ioc ht0 le_rfl)).sub hφi).congr_fun (fun r hr => ?_)
      measurableSet_Ioc
    simp only [Pi.sub_apply]
    rw [hsplit r hr]; ring
  have hode := d34_ode2 (φ := φ) (ψ := ψ) (d := ∫ ω in A, Y ω ∂P) htT
    (hφc.mono (Icc_subset_Icc ht0 le_rfl)) hψi (fun x hx => by
      refine (hψ x hx).2.trans ?_
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
      exact hsplit r ⟨lt_of_le_of_lt hx.1 hr.1, hr.2⟩)
  have hψt : ψ t = ∫ ω in A, V t ω ∂P := by simp [hψdef]
  rw [← hψt, hode, integral_add (hYint.const_mul _).integrableOn hpf.1.integrableOn,
    integral_const_mul]
  have e4 := (d34_procFub P T U hsol.1 A hAm _ hwm _ (Real.exp_pos _).le hwb ht0 le_rfl).2.1
  rw [e4]

theorem example_1_formulas_core {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
      (fun u v => u + v) Y U V) :
    L1NormDt P T (fun t ω => U t ω -
      Real.exp (t : ℝ) * (J₀ ω +
        ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
          Real.exp (-s) * |V s.toNNReal ω|)) = 0 ∧
    (∀ t ≤ T, Integrable
      (fun ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
        ∫ s in Set.Ioc (t : ℝ) (T : ℝ),
          Real.exp (s - (t : ℝ)) * U s.toNNReal ω) P) ∧
    ∃ W : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T
        (fun t ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
          ∫ s in Set.Ioc (t : ℝ) (T : ℝ),
            Real.exp (s - (t : ℝ)) * U s.toNNReal ω) W ∧
      L1NormDt P T (fun t ω => W t ω - V t ω) = 0 := by
  have hint := fun t ht => (d34_Vcond P 𝓕 T J₀ Y U V hJint hsol t ht).1
  refine ⟨?_, hint, V, ⟨hsol.2.1.1, hint, fun t ht => (d34_Vcond P 𝓕 T J₀ Y U V hJint hsol t ht).2⟩,
    by simp [L1NormDt]⟩
  have hp := d34_Upath P 𝓕 T J₀ Y U V _ hJmeas hsol
  unfold L1NormDt
  refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans (by simp)
  filter_upwards [hp] with ω hω
  refine (lintegral_congr_ae ?_).trans (lintegral_zero (μ := volume.restrict (Ioc (0:ℝ) T)))
  filter_upwards [hω, ae_restrict_mem measurableSet_Ioc] with r hr hrI
  rw [Real.coe_toNNReal r hrI.1.le, ← hr]
  simp

lemma d34_condExp_pos {Ω : Type*} {m mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) (X : Ω → ℝ) (hX : Integrable X P)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) : ∀ᵐ ω ∂P, 0 < P[X | m] ω := by
  have hgm : StronglyMeasurable[m] (P[X | m]) := stronglyMeasurable_condExp
  set B : Set Ω := {ω | P[X | m] ω ≤ 0} with hB
  have hBm : MeasurableSet[m] B := measurableSet_le hgm.measurable measurable_const
  have e := setIntegral_condExp hm hX hBm
  have h1 : ∫ ω in B, P[X | m] ω ∂P ≤ 0 :=
    setIntegral_nonpos (hm B hBm) (fun ω hω => hω)
  have h2 : 0 ≤ ∫ ω in B, X ω ∂P :=
    integral_nonneg_of_ae (ae_restrict_of_ae (hpos.mono fun ω h => h.le))
  have h3 : ∫ ω in B, X ω ∂P = 0 := by linarith
  rw [setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae (hpos.mono fun ω h => h.le))
    hX.integrableOn] at h3
  have hB0 : P B = 0 := by
    have h4 : ∀ᵐ ω ∂(P.restrict B), False := by
      filter_upwards [h3, ae_restrict_of_ae hpos] with ω a b
      have a' : X ω = 0 := a
      rw [a'] at b; exact lt_irrefl _ b
    rw [ae_iff] at h4
    simpa [Measure.restrict_apply' (hm B hBm)] using h4
  have : ∀ᵐ ω ∂P, ω ∉ B := measure_eq_zero_iff_ae_notMem.1 hB0
  filter_upwards [this] with ω hω
  simpa [hB] using hω

lemma d34_swap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ)
    (hXm : Measurable (Function.uncurry (fun t ω => if t ≤ T then X t ω else 0))) :
    (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), 0 < X r.toNNReal ω) ↔
    (∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), ∀ᵐ ω ∂P, 0 < X r.toNNReal ω) := by
  let X' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then X p.1.toNNReal p.2 else 0
  have hX'm : Measurable X' := hXm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hT' : ∀ r ∈ Ioc (0:ℝ) T, r.toNNReal ≤ T := fun r hr => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have hS : MeasurableSet {x : Ω × ℝ | 0 < X' (x.2, x.1)} :=
    measurableSet_lt measurable_const (hX'm.comp measurable_swap)
  have hc := Measure.ae_ae_comm (μ := P) (ν := volume.restrict (Ioc (0:ℝ) T))
    (p := fun ω r => 0 < X' (r, ω)) hS
  have e1 : (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), 0 < X r.toNNReal ω) ↔
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), 0 < X' (r, ω)) := by
    refine Filter.eventually_congr (Eventually.of_forall fun ω => ?_)
    refine Filter.eventually_congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp [X', hT' r hr]
  have e2 : (∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), ∀ᵐ ω ∂P, 0 < X r.toNNReal ω) ↔
      (∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), ∀ᵐ ω ∂P, 0 < X' (r, ω)) := by
    refine Filter.eventually_congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp [X', hT' r hr]
  rw [e1, e2]
  exact hc

theorem example_1_positive_core {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
      (fun u v => u + v) Y U V) :
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      ∀ᵐ ω ∂P, 0 < U r.toNNReal ω ∧ 0 < V r.toNNReal ω) ∧
    IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V := by
  have hUpath := d34_Upath P 𝓕 T J₀ Y U V _ hJmeas hsol
  have hUpos : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), 0 < U r.toNNReal ω := by
    filter_upwards [hUpath, hJpos] with ω h hJ
    filter_upwards [h] with r hr
    rw [hr]
    refine mul_pos (Real.exp_pos _) ?_
    have : 0 ≤ ∫ s in Ioc 0 r, Real.exp (-s) * |V s.toNNReal ω| :=
      setIntegral_nonneg measurableSet_Ioc (fun s _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
    linarith
  have hUswap := (d34_swap P T U hsol.1.1).1 hUpos
  have hVpos : ∀ r ∈ Ioc (0:ℝ) T, ∀ᵐ ω ∂P, 0 < V r.toNNReal ω := by
    intro r hr
    have hrT : r.toNNReal ≤ T := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    obtain ⟨hint, hc⟩ := d34_Vcond P 𝓕 T J₀ Y U V hJint hsol r.toNNReal hrT
    have hξpos : ∀ᵐ ω ∂P, 0 < Real.exp ((T : ℝ) - (r.toNNReal : ℝ)) * Y ω +
        ∫ s in Set.Ioc (r.toNNReal : ℝ) (T : ℝ), Real.exp (s - (r.toNNReal : ℝ)) * U s.toNNReal ω := by
      filter_upwards [hUpos, hYpos] with ω h1 h2
      have hsub : Ioc (r.toNNReal : ℝ) T ⊆ Ioc 0 T := Ioc_subset_Ioc (NNReal.coe_nonneg _) le_rfl
      have : 0 ≤ ∫ s in Set.Ioc (r.toNNReal : ℝ) (T : ℝ),
          Real.exp (s - (r.toNNReal : ℝ)) * U s.toNNReal ω := by
        refine setIntegral_nonneg_of_ae_restrict ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h1] with s hs
        exact mul_nonneg (Real.exp_pos _).le hs.le
      have := mul_pos (Real.exp_pos ((T : ℝ) - (r.toNNReal : ℝ))) h2
      linarith
    filter_upwards [hc, d34_condExp_pos P (𝓕.le _) _ hint hξpos] with ω h1 h2
    rw [h1]; exact h2
  have hVswap : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Ioc (0:ℝ) T)), 0 < V r.toNNReal ω :=
    (d34_swap P T V hsol.2.1.1).2 ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall hVpos))
  refine ⟨?_, ?_⟩
  · filter_upwards [hUswap, ae_restrict_mem measurableSet_Ioc] with r h1 hrI
    filter_upwards [h1, hVpos r hrI] with ω a b
    exact ⟨a, b⟩
  · have hS := d34_memL1_add P T U V hsol.1 hsol.2.1
    obtain ⟨hU, hV, hUad, hVad, hpath, hξ, W, hW, hUV, hVT⟩ := hsol
    refine ⟨hU, hV, hUad, hVad, ?_, hξ, W, hW, fun t ht => ⟨?_, (hUV t ht).2⟩, hVT⟩
    · filter_upwards [d34_path_int P T _ hS] with ω h
      exact ⟨h, h⟩
    · refine (hUV t ht).1.trans ?_
      filter_upwards [hVswap] with ω hω
      congr 1
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      have hω' := (ae_restrict_iff' measurableSet_Ioc).1 hω
      filter_upwards [hω'] with s hs hst
      have hsT : s ∈ Ioc (0:ℝ) T := ⟨hst.1, hst.2.trans (by exact_mod_cast ht)⟩
      rw [abs_of_pos (hs hsT)]

end AntonelliBFSDE.SingularExample

open AntonelliBFSDE.SingularExample


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (hT : 0 < T)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYint : Integrable Y P)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
      (fun u v => u + v) Y U V) :
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      ∀ᵐ ω ∂P, 0 < U r.toNNReal ω ∧ 0 < V r.toNNReal ω) ∧
    IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V := by
  exact example_1_positive_core P 𝓕 T J₀ Y U V hJmeas hJint hJpos hYpos hsol
