-- Prove2me | solution 1 for AllocationIndices.Branching.minCoeffSum_ge_entryDiscount
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T08:59:29.82795+00:00
-- url     : https://prove2.me/submissions/8b142e71-b800-4629-8e4b-df752a9a6449

import Mathlib
import Definitions.Def_AllocationIndices_Branching_Parallel

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices

namespace P2MCF

variable {N : ℕ}

lemma prob (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

lemma marg0 (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    (markovChainMeasure P x).map (Preorder.frestrictLe 0) = Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

lemma ext_marg (μ ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν]
    (h : ∀ a, μ.map (Preorder.frestrictLe a) = ν.map (Preorder.frestrictLe a)) : μ = ν := by
  have hproj : IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ Fin N)
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → Fin N) (i : I) ↦ f i)) := by
    intro I J hJI
    dsimp only
    rw [Measure.map_map (Finset.measurable_restrict₂ _)
      (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _))]
    rfl
  have h1 : IsProjectiveLimit (α := fun _ : ℕ ↦ Fin N) μ
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → Fin N) (i : I) ↦ f i)) :=
    (isProjectiveLimit_nat_iff hproj μ).2 h
  have h2 : IsProjectiveLimit (α := fun _ : ℕ ↦ Fin N) ν
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → Fin N) (i : I) ↦ f i)) :=
    fun I ↦ rfl
  exact h1.unique h2

/-- cylinder set -/
def cyl (b : ℕ) (w : ℕ → Fin N) : Set (ℕ → Fin N) := {ω | ∀ i ≤ b, ω i = w i}

lemma cyl_eq (b : ℕ) (w : ℕ → Fin N) :
    cyl b w = Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin N) b ⁻¹' {Preorder.frestrictLe b w} := by
  ext ω
  simp only [cyl, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    Preorder.frestrictLe_apply, Subtype.forall, Finset.mem_Iic]

lemma measurableSet_cyl (b : ℕ) (w : ℕ → Fin N) : MeasurableSet (cyl b w) := by
  rw [cyl_eq]
  exact Preorder.measurable_frestrictLe b (measurableSet_singleton _)

lemma cyl_formula (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) (b : ℕ)
    (w : ℕ → Fin N) :
    markovChainMeasure P x (cyl b w) =
      (if w 0 = x then 1 else 0) * ∏ i ∈ range b, P (w i) {w (i + 1)} := by
  haveI := prob P x
  induction b with
  | zero =>
    have hs : MeasurableSet {h : Finset.Iic 0 → Fin N | h ⟨0, by simp⟩ = w 0} :=
      (Set.toFinite _).measurableSet
    have : cyl 0 w = Preorder.frestrictLe 0 ⁻¹' {h : Finset.Iic 0 → Fin N | h ⟨0, by simp⟩ = w 0} := by
      ext ω
      simp [cyl, Preorder.frestrictLe]
    rw [this, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hs, marg0,
      Measure.dirac_apply' _ hs]
    by_cases hw : w 0 = x
    · simp [Set.indicator, hw]
    · have : x ≠ w 0 := fun h ↦ hw h.symm
      simp [Set.indicator, hw, this]
  | succ b ih =>
    have hA : MeasurableSet {h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i} :=
      (Set.toFinite _).measurableSet
    have hset : cyl (b + 1) w = (fun ω ↦ (Preorder.frestrictLe b ω, ω (b + 1))) ⁻¹'
        ({h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i} ×ˢ {w (b + 1)}) := by
      ext ω
      simp only [cyl, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
        Preorder.frestrictLe_apply, Subtype.forall, Finset.mem_Iic]
      constructor
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h (b + 1) le_rfl⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_or_ge i (b + 1) with h | h
        · exact h1 i (by omega)
        · have : i = b + 1 := by omega
          subst this; exact h2
    have hF1 : (markovChainMeasure P x).map (Preorder.frestrictLe b) ⊗ₘ markovChainStep P b =
        (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe b ω, ω (b + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    rw [hset, ← Measure.map_apply (by fun_prop) (hA.prod (measurableSet_singleton _)), ← hF1,
      Measure.compProd_apply_prod hA (measurableSet_singleton _)]
    have hc : ∀ h ∈ {h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i},
        markovChainStep P b h {w (b + 1)} = P (w b) {w (b + 1)} := by
      intro h hh
      simp only [markovChainStep, Kernel.comap_apply]
      rw [hh ⟨b, Finset.mem_Iic.2 le_rfl⟩]
    rw [setLIntegral_congr_fun hA hc, setLIntegral_const,
      Measure.map_apply (Preorder.measurable_frestrictLe b) hA]
    have : Preorder.frestrictLe b ⁻¹' {h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i}
        = cyl b w := by
      ext ω
      simp [cyl, Preorder.frestrictLe]
    rw [this, ih, prod_range_succ]
    ring

lemma ae_zero (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    ∀ᵐ ω ∂markovChainMeasure P x, ω 0 = x := by
  rw [ae_iff]
  have hs : MeasurableSet {h : Finset.Iic 0 → Fin N | ¬ h ⟨0, by simp⟩ = x} :=
    (Set.toFinite _).measurableSet
  have : {ω : ℕ → Fin N | ¬ ω 0 = x} =
      Preorder.frestrictLe 0 ⁻¹' {h : Finset.Iic 0 → Fin N | ¬ h ⟨0, by simp⟩ = x} := by
    ext ω; simp [Preorder.frestrictLe]
  rw [this, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hs, marg0,
    Measure.dirac_apply' _ hs]
  simp [Set.indicator]

/-- the shift -/
def shift (ω : ℕ → Fin N) : ℕ → Fin N := fun n ↦ ω (n + 1)

lemma measurable_shift : Measurable (shift (N := N)) :=
  measurable_pi_lambda _ (fun n ↦ measurable_pi_apply (n + 1))

lemma shift_law (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    (markovChainMeasure P x).map shift = ∑ y, P x {y} • markovChainMeasure P y := by
  haveI := prob P x
  refine (ext_marg _ _ (fun b ↦ ?_)).symm
  refine Measure.ext_iff_singleton.2 (fun h ↦ ?_)
  let w : ℕ → Fin N := fun i ↦ if hi : i ≤ b then h ⟨i, Finset.mem_Iic.2 hi⟩ else x
  have hw : Preorder.frestrictLe b w = h := by
    funext i
    simp [w, Preorder.frestrictLe, Finset.mem_Iic.1 i.2]
  have hpre : Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin N) b ⁻¹' {h} = cyl b w := by
    rw [cyl_eq, hw]
  rw [Measure.map_apply (Preorder.measurable_frestrictLe b) (measurableSet_singleton _),
    Measure.map_apply (Preorder.measurable_frestrictLe b) (measurableSet_singleton _), hpre,
    Measure.map_apply measurable_shift (measurableSet_cyl b w)]
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, cyl_formula]
  let w' : ℕ → Fin N := fun i ↦ match i with
    | 0 => x
    | i + 1 => w i
  have hinter : cyl (b + 1) w' = shift ⁻¹' cyl b w ∩ {ω | ω 0 = x} := by
    ext ω
    simp only [cyl, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, shift]
    constructor
    · intro hω
      exact ⟨fun i hi ↦ hω (i + 1) (by omega), hω 0 (by omega)⟩
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => exact h2
      | succ i => exact h1 i (by omega)
  have hnull : markovChainMeasure P x {ω | ω 0 = x}ᶜ = 0 := by
    have := ae_zero P x
    rw [ae_iff] at this
    exact this
  have hL : markovChainMeasure P x (shift ⁻¹' cyl b w) = markovChainMeasure P x (cyl (b + 1) w') := by
    rw [hinter, measure_inter_conull hnull]
  rw [hL, cyl_formula, prod_range_succ']
  simp [w', mul_ite, Finset.sum_ite_eq]
  ring

lemma shift_integral (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N)
    (F : (ℕ → Fin N) → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F (shift ω) ∂markovChainMeasure P x = ∑ y, (P x).real {y} * ∫ ω, F ω ∂markovChainMeasure P y := by
  rw [← integral_map measurable_shift.aemeasurable hF.aestronglyMeasurable, shift_law,
    integral_finsetSum_measure]
  · simp [integral_smul_measure, measureReal_def]
  · intro y _
    haveI := prob P y
    exact (Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun ω ↦ by
      simpa [Real.norm_eq_abs] using hC ω)).smul_measure (measure_ne_top _ _)

/-! ### hitting times -/

lemma hit_eq_nat (s : Set (Fin N)) (ω : ℕ → Fin N) (m : ℕ) (hm : 1 ≤ m) (hs : ω m ∈ s)
    (hlt : ∀ t, 1 ≤ t → t < m → ω t ∉ s) : hittingTime s ω = m := by
  unfold hittingTime
  apply le_antisymm
  · exact iInf_le_of_le ⟨m, hm, hs⟩ le_rfl
  · refine le_iInf fun t ↦ ?_
    have : m ≤ (t : ℕ) := by
      by_contra hc
      push_neg at hc
      exact hlt t t.2.1 hc t.2.2
    exact_mod_cast this

lemma hit_eq_top (s : Set (Fin N)) (ω : ℕ → Fin N) (h : ∀ t, 1 ≤ t → ω t ∉ s) :
    hittingTime s ω = ⊤ := by
  unfold hittingTime
  haveI : IsEmpty {t : ℕ // 1 ≤ t ∧ ω t ∈ s} := ⟨fun t ↦ h t t.2.1 t.2.2⟩
  exact iInf_of_empty _

lemma hit_eq_nat_iff (s : Set (Fin N)) (ω : ℕ → Fin N) (m : ℕ) :
    hittingTime s ω = m ↔ (1 ≤ m ∧ ω m ∈ s ∧ ∀ t, 1 ≤ t → t < m → ω t ∉ s) := by
  classical
  constructor
  · intro hT
    by_cases hex : ∃ t, 1 ≤ t ∧ ω t ∈ s
    · have ht0 := Nat.find_spec hex
      have hmin : ∀ t, 1 ≤ t → t < Nat.find hex → ω t ∉ s :=
        fun t h1 h2 hs ↦ Nat.find_min hex h2 ⟨h1, hs⟩
      have h0 := hit_eq_nat s ω (Nat.find hex) ht0.1 ht0.2 hmin
      rw [h0] at hT
      have hm : Nat.find hex = m := by exact_mod_cast hT
      rw [← hm]
      exact ⟨ht0.1, ht0.2, hmin⟩
    · push_neg at hex
      rw [hit_eq_top s ω hex] at hT
      simp at hT
  · rintro ⟨h1, h2, h3⟩
    exact hit_eq_nat s ω m h1 h2 h3

lemma measurable_hit (s : Set (Fin N)) : Measurable (hittingTime s) := by
  rw [ENat.measurable_iff]
  intro m
  have : hittingTime s ⁻¹' {(m : ℕ∞)} =
      {ω | 1 ≤ m ∧ ω m ∈ s ∧ ∀ t, 1 ≤ t → t < m → ω t ∉ s} := by
    ext ω
    exact hit_eq_nat_iff s ω m
  rw [this]
  have hc : ∀ t, Measurable (fun ω : ℕ → Fin N ↦ ω t ∈ s) := fun t ↦
    measurableSet_setOf.1 (measurable_pi_apply t (Set.toFinite s).measurableSet)
  exact measurableSet_setOf.2 (measurable_const.and ((hc m).and
    (Measurable.forall fun t ↦ measurable_const.imp (measurable_const.imp (hc t).not))))

/-- discount function -/
noncomputable def dfun (a : ℝ) (e : ℕ∞) : ℝ := match e with
  | (n : ℕ) => a ^ n
  | ⊤ => 0

lemma dfun_coe (a : ℝ) (n : ℕ) : dfun a n = a ^ n := rfl
lemma dfun_top (a : ℝ) : dfun a ⊤ = 0 := rfl

lemma discountAtStop_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (τ : (ℕ → Fin N) → ℕ∞) (x : Fin N) :
    AllocationIndices.discountAtStop P a τ x = ∫ ω, dfun a (τ ω) ∂markovChainMeasure P x := rfl

lemma measurable_D (a : ℝ) (s : Set (Fin N)) :
    Measurable (fun ω : ℕ → Fin N ↦ dfun a (hittingTime s ω)) :=
  (measurable_of_countable (dfun a)).comp (measurable_hit s)

lemma D_bounds (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : Set (Fin N)) (ω : ℕ → Fin N) :
    0 ≤ dfun a (hittingTime s ω) ∧ dfun a (hittingTime s ω) ≤ a := by
  generalize hT : hittingTime s ω = e
  induction e using ENat.recTopCoe with
  | top => exact ⟨le_rfl, ha0⟩
  | coe m =>
    have hm := ((hit_eq_nat_iff s ω m).1 hT).1
    rw [dfun_coe]
    exact ⟨pow_nonneg ha0 m, pow_le_of_le_one ha0 ha1 (by omega)⟩

lemma D_step (a : ℝ) (S : Finset (Fin N)) (ω : ℕ → Fin N) :
    dfun a (hittingTime (↑S : Set (Fin N)) ω) =
      a * (if shift ω 0 ∈ S then 1 else dfun a (hittingTime (↑S : Set (Fin N)) (shift ω))) := by
  classical
  by_cases h1 : ω 1 ∈ S
  · have : hittingTime (↑S : Set (Fin N)) ω = ((1 : ℕ) : ℕ∞) :=
      hit_eq_nat _ ω 1 le_rfl (Finset.mem_coe.2 h1) (fun t h1 h2 ↦ by omega)
    have h1' : shift ω 0 ∈ S := h1
    rw [this, dfun_coe, if_pos h1']
    ring
  · have hs0 : ¬ shift ω 0 ∈ S := h1
    rw [if_neg hs0]
    by_cases hex : ∃ t, 1 ≤ t ∧ ω (t + 1) ∈ S
    · have hm := Nat.find_spec hex
      have hmin : ∀ t, 1 ≤ t → t < Nat.find hex → ω (t + 1) ∉ S :=
        fun t h1 h2 hs ↦ Nat.find_min hex h2 ⟨h1, hs⟩
      have e1 : hittingTime (↑S : Set (Fin N)) (shift ω) = (Nat.find hex : ℕ) :=
        hit_eq_nat _ _ _ hm.1 (by
            show ω (Nat.find hex + 1) ∈ (↑S : Set (Fin N)); exact Finset.mem_coe.2 hm.2)
          (fun t ht1 ht2 ↦ by
            show ω (t + 1) ∉ (↑S : Set (Fin N))
            exact fun h ↦ hmin t ht1 ht2 (Finset.mem_coe.1 h))
      have e2 : hittingTime (↑S : Set (Fin N)) ω = ((Nat.find hex + 1 : ℕ) : ℕ∞) := by
        refine hit_eq_nat _ ω _ (by omega) (Finset.mem_coe.2 hm.2) (fun t ht1 ht2 ↦ ?_)
        rcases Nat.lt_or_ge t 2 with h | h
        · have : t = 1 := by omega
          subst this
          exact fun h ↦ h1 (Finset.mem_coe.1 h)
        · have := hmin (t - 1) (by omega) (by omega)
          rw [show t - 1 + 1 = t by omega] at this
          exact fun h ↦ this (Finset.mem_coe.1 h)
      rw [e1, e2, dfun_coe, dfun_coe, pow_succ]
      ring
    · push_neg at hex
      have e1 : hittingTime (↑S : Set (Fin N)) (shift ω) = ⊤ :=
        hit_eq_top _ _ (fun t ht h ↦ hex t ht (Finset.mem_coe.1 h))
      have e2 : hittingTime (↑S : Set (Fin N)) ω = ⊤ := by
        refine hit_eq_top _ _ (fun t ht ↦ ?_)
        rcases Nat.lt_or_ge t 2 with h | h
        · have : t = 1 := by omega
          subst this
          exact fun h ↦ h1 (Finset.mem_coe.1 h)
        · have := hex (t - 1) (by omega)
          rw [show t - 1 + 1 = t by omega] at this
          exact fun h ↦ this (Finset.mem_coe.1 h)
      rw [e1, e2, dfun_top, mul_zero]

lemma dss_eq (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (e : ℕ∞) :
    (∑' t : ℕ, if (t : ℕ∞) < e then a ^ t * 1 else 0) = (1 - dfun a e) / (1 - a) := by
  have h1a : (1 - a) ≠ 0 := by linarith
  induction e using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, if_true, mul_one, dfun_top, sub_zero]
    rw [tsum_geometric_of_lt_one ha0 ha1, one_div]
  | coe m =>
    rw [tsum_eq_sum (s := range m) (fun t ht ↦ by
      have : ¬ t < m := by simpa using ht
      simp [this])]
    rw [Finset.sum_congr rfl (fun t ht ↦ by
      have : t < m := Finset.mem_range.1 ht
      simp [this] : ∀ t ∈ range m, (if (t : ℕ∞) < (m : ℕ∞) then a ^ t * 1 else 0) = a ^ t)]
    have ha1' : a - 1 ≠ 0 := by linarith
    rw [geom_sum_eq (ne_of_lt ha1), dfun_coe, div_eq_div_iff ha1' h1a]
    ring

lemma D_integrable (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (s : Set (Fin N)) (x : Fin N) :
    Integrable (fun ω ↦ dfun a (hittingTime s ω)) (markovChainMeasure P x) := by
  haveI := prob P x
  refine Integrable.of_bound (measurable_D a s).aestronglyMeasurable a (ae_of_all _ fun ω ↦ ?_)
  have := D_bounds a ha0 ha1 s ω
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

lemma g_bounds (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (s : Set (Fin N)) (x : Fin N) :
    0 ≤ AllocationIndices.discountAtStop P a (hittingTime s) x ∧
      AllocationIndices.discountAtStop P a (hittingTime s) x ≤ a := by
  haveI := prob P x
  rw [discountAtStop_eq]
  refine ⟨integral_nonneg fun ω ↦ (D_bounds a ha0 ha1 s ω).1, ?_⟩
  calc ∫ ω, dfun a (hittingTime s ω) ∂markovChainMeasure P x
      ≤ ∫ _ω, a ∂markovChainMeasure P x :=
        integral_mono (D_integrable P a ha0 ha1 s x) (integrable_const a)
          (fun ω ↦ (D_bounds a ha0 ha1 s ω).2)
    _ = a := by simp

lemma stoppedTime_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (s : Set (Fin N)) (x : Fin N) :
    AllocationIndices.stoppedTime P a (hittingTime s) x =
      (1 - AllocationIndices.discountAtStop P a (hittingTime s) x) / (1 - a) := by
  haveI := prob P x
  have hpt : ∀ ω, discountedStoppedSum a (fun _ ↦ (1 : ℝ)) (hittingTime s) ω =
      (1 - dfun a (hittingTime s ω)) / (1 - a) := by
    intro ω
    unfold discountedStoppedSum
    exact dss_eq a ha0 ha1 _
  unfold AllocationIndices.stoppedTime
  simp_rw [hpt]
  rw [discountAtStop_eq, integral_div, integral_sub (integrable_const 1)
    (D_integrable P a ha0 ha1.le s x)]
  simp

lemma first_step (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (S : Finset (Fin N)) (x : Fin N) :
    AllocationIndices.discountAtStop P a (hittingTime (↑S : Set (Fin N))) x =
      a * ∑ y, (P x).real {y} * (if y ∈ S then 1 else
        AllocationIndices.discountAtStop P a (hittingTime (↑S : Set (Fin N))) y) := by
  let Φ : (ℕ → Fin N) → ℝ := fun ω ↦
    if ω 0 ∈ S then 1 else dfun a (hittingTime (↑S : Set (Fin N)) ω)
  have hΦm : Measurable Φ :=
    Measurable.ite (measurable_pi_apply 0 (Set.toFinite (↑S : Set (Fin N))).measurableSet)
      measurable_const (measurable_D a _)
  have hΦb : ∀ ω, |Φ ω| ≤ 1 := by
    intro ω
    simp only [Φ]
    split_ifs
    · simp
    · have := D_bounds a ha0 ha1 (↑S : Set (Fin N)) ω
      rw [abs_of_nonneg this.1]
      linarith [this.2]
  rw [discountAtStop_eq]
  have hstep : ∫ ω, dfun a (hittingTime (↑S : Set (Fin N)) ω) ∂markovChainMeasure P x =
      ∫ ω, a * Φ (shift ω) ∂markovChainMeasure P x :=
    integral_congr_ae (ae_of_all _ fun ω ↦ D_step a S ω)
  rw [hstep, integral_const_mul, shift_integral P x Φ hΦm 1 hΦb]
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  congr 1
  haveI := prob P y
  have : ∫ ω, Φ ω ∂markovChainMeasure P y = ∫ ω, (if y ∈ S then 1 else
      dfun a (hittingTime (↑S : Set (Fin N)) ω)) ∂markovChainMeasure P y :=
    integral_congr_ae ((ae_zero P y).mono fun ω hω ↦ by simp only [Φ, hω])
  rw [this]
  split_ifs with hy
  · simp
  · rfl

lemma real_sum_one {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] : ∑ j, ν.real {j} = 1 := by
  have := integral_fintype (μ := ν) (f := fun _ ↦ (1 : ℝ)) Integrable.of_finite
  simpa using this.symm


/-! ### first entry times -/

section FE

open AllocationIndices.Branching

variable {K : ℕ}

lemma fe_eq_nat (s : Set (Fin (K + 1))) (ω : ℕ → Fin (K + 1)) (m : ℕ) (hs : ω m ∈ s)
    (hlt : ∀ t, t < m → ω t ∉ s) : firstEntryTime s ω = m := by
  unfold firstEntryTime
  apply le_antisymm
  · exact iInf_le_of_le ⟨m, hs⟩ le_rfl
  · refine le_iInf fun t ↦ ?_
    have : m ≤ (t : ℕ) := by
      by_contra hc
      push_neg at hc
      exact hlt t hc t.2
    exact_mod_cast this

lemma fe_eq_top (s : Set (Fin (K + 1))) (ω : ℕ → Fin (K + 1)) (h : ∀ t, ω t ∉ s) :
    firstEntryTime s ω = ⊤ := by
  unfold firstEntryTime
  haveI : IsEmpty {t : ℕ // ω t ∈ s} := ⟨fun t ↦ h t t.2⟩
  exact iInf_of_empty _

lemma fe_eq_nat_iff (s : Set (Fin (K + 1))) (ω : ℕ → Fin (K + 1)) (m : ℕ) :
    firstEntryTime s ω = m ↔ (ω m ∈ s ∧ ∀ t, t < m → ω t ∉ s) := by
  classical
  constructor
  · intro hT
    by_cases hex : ∃ t, ω t ∈ s
    · have ht0 := Nat.find_spec hex
      have hmin : ∀ t, t < Nat.find hex → ω t ∉ s :=
        fun t h2 hs ↦ Nat.find_min hex h2 hs
      have h0 := fe_eq_nat s ω (Nat.find hex) ht0 hmin
      rw [h0] at hT
      have hm : Nat.find hex = m := by exact_mod_cast hT
      rw [← hm]
      exact ⟨ht0, hmin⟩
    · push_neg at hex
      rw [fe_eq_top s ω hex] at hT
      simp at hT
  · rintro ⟨h2, h3⟩
    exact fe_eq_nat s ω m h2 h3

lemma measurable_fe (s : Set (Fin (K + 1))) : Measurable (firstEntryTime s) := by
  rw [ENat.measurable_iff]
  intro m
  have : firstEntryTime s ⁻¹' {(m : ℕ∞)} =
      {ω | ω m ∈ s ∧ ∀ t, t < m → ω t ∉ s} := by
    ext ω
    exact fe_eq_nat_iff s ω m
  rw [this]
  have hc : ∀ t, Measurable (fun ω : ℕ → Fin (K + 1) ↦ ω t ∈ s) := fun t ↦
    measurableSet_setOf.1 (measurable_pi_apply t (Set.toFinite s).measurableSet)
  exact measurableSet_setOf.2 ((hc m).and
    (Measurable.forall fun t ↦ measurable_const.imp (hc t).not))

lemma fe_zero (s : Set (Fin (K + 1))) (ω : ℕ → Fin (K + 1)) (h : ω 0 ∈ s) :
    firstEntryTime s ω = 0 := by
  have := fe_eq_nat s ω 0 h (fun t ht ↦ by omega)
  simpa using this

lemma fe_succ (s : Set (Fin (K + 1))) (ω : ℕ → Fin (K + 1)) (h : ω 0 ∉ s) :
    firstEntryTime s ω = 1 + firstEntryTime s (shift ω) := by
  generalize hT : firstEntryTime s (shift ω) = e
  induction e using ENat.recTopCoe with
  | top =>
    have h1 : ∀ t, ω (t + 1) ∉ s := by
      intro t ht
      have := fe_eq_top s (shift ω)
      by_contra hc
      have hne : ∃ t, shift ω t ∈ s := ⟨t, ht⟩
      classical
      have := (fe_eq_nat_iff s (shift ω) (Nat.find hne)).2
        ⟨Nat.find_spec hne, fun u hu hs ↦ Nat.find_min hne hu hs⟩
      rw [hT] at this
      simp at this
    rw [fe_eq_top s ω (fun t ↦ by
      cases t with
      | zero => exact h
      | succ t => exact h1 t)]
    simp
  | coe m =>
    have hm := (fe_eq_nat_iff s (shift ω) m).1 hT
    have : firstEntryTime s ω = ((m + 1 : ℕ) : ℕ∞) := by
      refine fe_eq_nat s ω (m + 1) hm.1 (fun t ht ↦ ?_)
      cases t with
      | zero => exact h
      | succ t => exact hm.2 t (by omega)
    rw [this]
    push_cast
    ring

end FE

/-! ### the value function `v` -/

section V

/-- `v R = m/(1-a) - ∑_{j<R} a^⌊j/m⌋`, `v ⊤ = 0`. -/
noncomputable def vfun (a : ℝ) (m : ℕ) (e : ℕ∞) : ℝ := match e with
  | (R : ℕ) => m / (1 - a) - ∑ j ∈ range R, a ^ (j / m)
  | ⊤ => 0

lemma vfun_coe (a : ℝ) (m R : ℕ) :
    vfun a m R = m / (1 - a) - ∑ j ∈ range R, a ^ (j / m) := rfl
lemma vfun_top (a : ℝ) (m : ℕ) : vfun a m ⊤ = 0 := rfl

lemma dsum_add_m (a : ℝ) (m : ℕ) (hm : 0 < m) (R : ℕ) :
    ∑ j ∈ range (m + R), a ^ (j / m) = m + a * ∑ j ∈ range R, a ^ (j / m) := by
  rw [Finset.sum_range_add]
  congr 1
  · rw [Finset.sum_congr rfl (fun j hj ↦ by
      rw [Nat.div_eq_of_lt (Finset.mem_range.1 hj), pow_zero])]
    simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have : (m + x) / m = x / m + 1 := by
      rw [Nat.add_comm, Nat.add_div_right x hm]
    rw [this, pow_succ]
    ring

lemma vfun_add_m (a : ℝ) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (R : ℕ∞) :
    vfun a m (R + m) = a * vfun a m R := by
  induction R using ENat.recTopCoe with
  | top => simp [vfun_top]
  | coe R =>
    rw [← Nat.cast_add, vfun_coe, vfun_coe, Nat.add_comm, dsum_add_m a m hm]
    have h1a : (1 - a) ≠ 0 := by linarith
    field_simp
    ring

lemma vfun_bellman (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (p e : ℕ)
    (hpe : m ≤ p + e) (R : ℕ∞) :
    vfun a m (R + e) ≤ p + a * vfun a m R := by
  rw [← vfun_add_m a ha1 m hm]
  induction R using ENat.recTopCoe with
  | top => simp [vfun_top]
  | coe R =>
    rw [← Nat.cast_add, ← Nat.cast_add, vfun_coe, vfun_coe]
    have hnn : ∀ j, 0 ≤ a ^ (j / m) := fun j ↦ pow_nonneg ha0 _
    rcases le_or_gt m e with hme | hme
    · have : ∑ j ∈ range (R + m), a ^ (j / m) ≤ ∑ j ∈ range (R + e), a ^ (j / m) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun j _ _ ↦ hnn j)
      have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith
    · have hsplit : R + m = (R + e) + (m - e) := by omega
      rw [hsplit, Finset.sum_range_add (fun j ↦ a ^ (j / m)) (R + e) (m - e)]
      have hle : ∑ x ∈ range (m - e), a ^ ((R + e + x) / m) ≤ ((m - e : ℕ) : ℝ) := by
        calc ∑ x ∈ range (m - e), a ^ ((R + e + x) / m)
            ≤ ∑ x ∈ range (m - e), (1 : ℝ) :=
              Finset.sum_le_sum fun x _ ↦ pow_le_one₀ ha0 ha1.le
          _ = ((m - e : ℕ) : ℝ) := by simp
      have hp : ((m - e : ℕ) : ℝ) ≤ p := by exact_mod_cast (by omega : m - e ≤ p)
      linarith

lemma vfun_closed (a : ℝ) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : r ≤ m) (q : ℕ) :
    vfun a m ((m * q + r : ℕ) : ℕ∞) = a ^ q * (m / (1 - a) - r) := by
  induction q with
  | zero =>
    simp only [mul_zero, zero_add, pow_zero, one_mul]
    rw [vfun_coe]
    congr 1
    rw [Finset.sum_congr rfl (fun j hj ↦ by
      rw [Nat.div_eq_of_lt (by have := Finset.mem_range.1 hj; omega), pow_zero])]
    simp
  | succ q ih =>
    have : ((m * (q + 1) + r : ℕ) : ℕ∞) = ((m * q + r : ℕ) : ℕ∞) + (m : ℕ∞) := by
      push_cast; ring
    rw [this, vfun_add_m a ha1 m hm, ih, pow_succ]
    ring

lemma vfun_lower (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (R : ℕ) :
    (m / (1 - a)) * a ^ ((R : ℝ) / m) ≤ vfun a m R := by
  have hR := Nat.div_add_mod R m
  have hr : R % m ≤ m := (Nat.mod_lt R hm).le
  have hv := vfun_closed a ha1 m hm (R % m) hr (R / m)
  rw [hR] at hv
  rw [hv]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : (R : ℝ) / m = ((R / m : ℕ) : ℝ) + ((R % m : ℕ) : ℝ) / m := by
    have : (R : ℝ) = (m : ℝ) * ((R / m : ℕ) : ℝ) + ((R % m : ℕ) : ℝ) := by
      exact_mod_cast hR.symm
    rw [this]
    field_simp
  rw [hcast, Real.rpow_add ha0, Real.rpow_natCast]
  set x : ℝ := ((R % m : ℕ) : ℝ) / m with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hmR]
    exact_mod_cast hr
  have hb : a ^ x ≤ 1 + x * (a - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := a - 1) (by linarith) hx0 hx1
    simpa using this
  have h1a : 0 < 1 - a := by linarith
  have hq : 0 ≤ a ^ (R / m) := pow_nonneg ha0.le _
  have hrx : ((R % m : ℕ) : ℝ) = m * x := by
    rw [hx]; field_simp
  rw [hrx]
  have key : m / (1 - a) * a ^ x ≤ m / (1 - a) - m * x := by
    have : m / (1 - a) * (1 + x * (a - 1)) = m / (1 - a) - m * x := by
      field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  calc m / (1 - a) * (a ^ (R / m) * a ^ x) = a ^ (R / m) * (m / (1 - a) * a ^ x) := by ring
    _ ≤ a ^ (R / m) * (m / (1 - a) - m * x) := mul_le_mul_of_nonneg_left key hq

lemma vfun_nonneg (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (R : ℕ∞) :
    0 ≤ vfun a m R := by
  induction R using ENat.recTopCoe with
  | top => simp [vfun_top]
  | coe R =>
    refine le_trans ?_ (vfun_lower a ha0 ha1 m hm R)
    have h1a : 0 < 1 - a := by linarith
    have := Real.rpow_nonneg ha0.le ((R : ℝ) / m)
    positivity

lemma vfun_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (m : ℕ) (R : ℕ∞) :
    vfun a m R ≤ m / (1 - a) := by
  have h1a : 0 < 1 - a := by linarith
  induction R using ENat.recTopCoe with
  | top => rw [vfun_top]; positivity
  | coe R =>
    rw [vfun_coe]
    have : 0 ≤ ∑ j ∈ range R, a ^ (j / m) := Finset.sum_nonneg fun j _ ↦ pow_nonneg ha0 _
    linarith

end V

/-! ### the excursion weights -/

section W

variable {K : ℕ}

/-- `W j = 0` on `S`, the expected discounted time to enter `S` off `S`. -/
noncomputable def Wf (P : Kernel (Fin K) (Fin K)) [IsMarkovKernel P] (a : ℝ) (S : Finset (Fin K))
    (j : Fin K) : ℝ :=
  if j ∈ S then 0 else stoppedTime P a (hittingTime (↑S : Set (Fin K))) j

lemma st_nonneg (P : Kernel (Fin K) (Fin K)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin K)) (j : Fin K) :
    0 ≤ stoppedTime P a (hittingTime (↑S : Set (Fin K))) j := by
  rw [stoppedTime_eq P a ha0 ha1]
  have := (g_bounds P a ha0 ha1.le (↑S : Set (Fin K)) j).2
  have h1a : 0 < 1 - a := by linarith
  exact div_nonneg (by linarith) h1a.le

lemma Wf_nonneg (P : Kernel (Fin K) (Fin K)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin K)) (j : Fin K) : 0 ≤ Wf P a S j := by
  unfold Wf
  split_ifs
  · exact le_rfl
  · exact st_nonneg P a ha0 ha1 S j

lemma st_first (P : Kernel (Fin K) (Fin K)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin K)) (j : Fin K) :
    stoppedTime P a (hittingTime (↑S : Set (Fin K))) j =
      1 + a * ∑ y, (P j).real {y} * Wf P a S y := by
  have h1a : (1 - a) ≠ 0 := by linarith
  have hW : ∀ y, Wf P a S y = (1 - (if y ∈ S then 1 else
      discountAtStop P a (hittingTime (↑S : Set (Fin K))) y)) / (1 - a) := by
    intro y
    unfold Wf
    split_ifs
    · simp
    · exact stoppedTime_eq P a ha0 ha1 _ y
  simp_rw [hW]
  rw [stoppedTime_eq P a ha0 ha1, first_step P a ha0 ha1.le S j]
  have hs := real_sum_one (P j)
  have hsum : ∑ x, (P j).real {x} * ((1 - (if x ∈ S then 1 else
      discountAtStop P a (hittingTime (↑S : Set (Fin K))) x)) / (1 - a)) =
      (1 - ∑ x, (P j).real {x} * (if x ∈ S then 1 else
        discountAtStop P a (hittingTime (↑S : Set (Fin K))) x)) / (1 - a) := by
    have hx : ∀ x, (P j).real {x} * ((1 - (if x ∈ S then 1 else
        discountAtStop P a (hittingTime (↑S : Set (Fin K))) x)) / (1 - a)) =
        ((P j).real {x} - (P j).real {x} * (if x ∈ S then 1 else
        discountAtStop P a (hittingTime (↑S : Set (Fin K))) x)) / (1 - a) := fun x ↦ by ring
    simp_rw [hx]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hs]
  rw [hsum]
  field_simp
  ring

end W

/-! ### product of chains and one parallel move -/

section Move

open AllocationIndices.Branching

variable {N n : ℕ}

instance probInst (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (x : Fin (N + 1)) :
    IsProbabilityMeasure (markovChainMeasure P x) := prob P x

/-- the product of the arms' chain laws -/
noncomputable def μpi (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (x : Fin n → Fin (N + 1)) : Measure (Fin n → ℕ → Fin (N + 1)) :=
  Measure.pi fun b ↦ markovChainMeasure P (x b)

instance μpi_prob (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (x : Fin n → Fin (N + 1)) : IsProbabilityMeasure (μpi P x) := by
  unfold μpi; infer_instance

/-- shift the processed coordinates -/
def σf (s : Fin n → Bool) (b : Fin n) : (ℕ → Fin (N + 1)) → (ℕ → Fin (N + 1)) :=
  if s b then shift else id

lemma measurable_σf (s : Fin n → Bool) (b : Fin n) : Measurable (σf (N := N) s b) := by
  unfold σf; split_ifs
  · exact measurable_shift
  · exact measurable_id

lemma measurable_σ (s : Fin n → Bool) :
    Measurable (fun (ω : Fin n → ℕ → Fin (N + 1)) b ↦ σf s b (ω b)) :=
  measurable_pi_lambda _ fun b ↦ (measurable_σf s b).comp (measurable_pi_apply b)

lemma σf_law (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (s : Fin n → Bool)
    (x : Fin n → Fin (N + 1)) (b : Fin n) (A : Set (ℕ → Fin (N + 1))) (hA : MeasurableSet A) :
    ((markovChainMeasure P (x b)).map (σf s b)) A =
      ∑ y, (armKernel P (s b) (x b)) {y} * markovChainMeasure P y A := by
  unfold σf armKernel
  by_cases hs : s b = true
  · simp only [hs, if_true]
    rw [shift_law, Measure.coe_finset_sum, Finset.sum_apply]
    simp
  · simp only [hs, Bool.false_eq_true, if_false, Measure.map_id, Kernel.id_apply]
    rw [Finset.sum_eq_single (x b)]
    · simp
    · intro y _ hy
      rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
      simp [Set.indicator, Ne.symm hy]
    · simp

lemma pi_move (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (s : Fin n → Bool)
    (x : Fin n → Fin (N + 1)) :
    (μpi P x).map (fun ω b ↦ σf s b (ω b)) =
      ∑ x' : Fin n → Fin (N + 1), (parallelMove P (x, s)) {x'} • μpi P x' := by
  unfold μpi
  rw [Measure.pi_map_pi (fun b ↦ (measurable_σf s b).aemeasurable)]
  refine Measure.pi_eq fun A hA ↦ ?_
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  have hsing : ∀ x' : Fin n → Fin (N + 1), (parallelMove P (x, s)) {x'} =
      ∏ b, (armKernel P (s b) (x b)) {x' b} := by
    intro x'
    have : ({x'} : Set (Fin n → Fin (N + 1))) = Set.univ.pi fun b ↦ {x' b} := by
      ext z; simp [funext_iff]
    simp only [parallelMove, Kernel.coe_mk]
    rw [this, Measure.pi_pi]
  simp_rw [hsing, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun b y ↦ (armKernel P (s b) (x b)) {y} * markovChainMeasure P y (A b))]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  exact (σf_law P s x b (A b) (hA b)).symm

lemma move_integral (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (s : Fin n → Bool) (x : Fin n → Fin (N + 1)) (Φ : (Fin n → ℕ → Fin (N + 1)) → ℝ)
    (hΦ : Measurable Φ) (C : ℝ) (hC : ∀ ω, |Φ ω| ≤ C) :
    ∫ x', (∫ ω, Φ ω ∂μpi P x') ∂(parallelMove P (x, s)) =
      ∫ ω, Φ (fun b ↦ σf s b (ω b)) ∂μpi P x := by
  rw [← integral_map (measurable_σ s).aemeasurable hΦ.aestronglyMeasurable, pi_move,
    integral_finsetSum_measure, integral_fintype Integrable.of_finite]
  · simp [integral_smul_measure, measureReal_def]
  · intro y _
    exact (Integrable.of_bound hΦ.aestronglyMeasurable C (ae_of_all _ fun ω ↦ by
      simpa [Real.norm_eq_abs] using hC ω)).smul_measure (measure_ne_top _ _)

lemma ae_init (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (x : Fin n → Fin (N + 1)) : ∀ᵐ ω ∂μpi P x, ∀ b, ω b 0 = x b := by
  rw [ae_all_iff]
  intro b
  exact (measurePreserving_eval (fun b ↦ markovChainMeasure P (x b)) b).quasiMeasurePreserving.ae
    (ae_zero P (x b))

lemma move_coord (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (s : Fin n → Bool) (x : Fin n → Fin (N + 1)) (b : Fin n) (f : Fin (N + 1) → ℝ) :
    ∫ x', f (x' b) ∂(parallelMove P (x, s)) =
      if s b then ∑ y, (P (x b)).real {y} * f y else f (x b) := by
  have hmp : MeasurePreserving (Function.eval b) (parallelMove P (x, s))
      (armKernel P (s b) (x b)) := by
    simp only [parallelMove, Kernel.coe_mk]
    exact measurePreserving_eval (fun b ↦ armKernel P (s b) (x b)) b
  rw [show (fun x' : Fin n → Fin (N + 1) ↦ f (x' b)) = fun x' ↦ f (Function.eval b x') from rfl,
    ← integral_map (measurable_pi_apply b).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable, hmp.map_eq]
  unfold armKernel
  split_ifs
  · rw [integral_fintype Integrable.of_finite]
    rfl
  · rw [Kernel.id_apply, integral_dirac]

/-- the entry-time sum over a set of arms -/
noncomputable def Tsum (S : Finset (Fin (N + 1))) (I : Finset (Fin n))
    (ω : Fin n → ℕ → Fin (N + 1)) : ℕ∞ :=
  ∑ b ∈ I, firstEntryTime (↑S : Set (Fin (N + 1))) (ω b)

lemma measurable_Tsum (S : Finset (Fin (N + 1))) (I : Finset (Fin n)) :
    Measurable (Tsum (n := n) S I) := by
  have h1 : Measurable (fun (ω : Fin n → ℕ → Fin (N + 1)) b ↦
      firstEntryTime (↑S : Set (Fin (N + 1))) (ω b)) :=
    measurable_pi_lambda _ fun b ↦ (measurable_fe _).comp (measurable_pi_apply b)
  exact (measurable_of_countable (fun z : Fin n → ℕ∞ ↦ ∑ b ∈ I, z b)).comp h1

lemma Tsum_step (S : Finset (Fin (N + 1))) (I : Finset (Fin n)) (s : Fin n → Bool)
    (x : Fin n → Fin (N + 1)) (ω : Fin n → ℕ → Fin (N + 1)) (hω : ∀ b, ω b 0 = x b) :
    Tsum S I ω = Tsum S (I.filter fun b ↦ x b ∉ S) (fun b ↦ σf s b (ω b)) +
      ((I.filter fun b ↦ x b ∉ S).filter fun b ↦ s b = true).card := by
  unfold Tsum
  rw [← Finset.sum_filter_add_sum_filter_not I (fun b ↦ x b ∉ S)]
  have h0 : ∑ b ∈ I.filter (fun b ↦ ¬ (x b ∉ S)), firstEntryTime (↑S : Set (Fin (N + 1))) (ω b)
      = 0 := by
    refine Finset.sum_eq_zero fun b hb ↦ ?_
    have : x b ∈ S := by simpa using (Finset.mem_filter.1 hb).2
    exact fe_zero _ _ (by rw [hω b]; exact Finset.mem_coe.2 this)
  rw [h0, add_zero]
  rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hxb : x b ∉ S := (Finset.mem_filter.1 hb).2
  unfold σf
  by_cases hs : s b = true
  · simp only [hs, if_true, Nat.cast_one]
    rw [fe_succ _ _ (by rw [hω b]; exact fun h ↦ hxb (Finset.mem_coe.1 h)), add_comm]
  · simp [hs]

end Move

/-! ### the potential and the one-step inequality -/

section Pot

open AllocationIndices.Branching

variable {N n : ℕ}

/-- arms that were in `S` at some recorded past time -/
def Qset (S : Finset (Fin (N + 1))) {t : ℕ} (h : ParallelHistory n N t) : Finset (Fin n) :=
  univ.filter fun b ↦ ∃ u : Fin t, (h.1 u).1 b ∈ S

noncomputable def Gv (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ) (m : ℕ)
    (S : Finset (Fin (N + 1))) (I : Finset (Fin n)) (x : Fin n → Fin (N + 1)) : ℝ :=
  ∫ ω, vfun a m (Tsum S I ω) ∂μpi P x

noncomputable def Λf (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ) (m : ℕ)
    (S : Finset (Fin (N + 1))) (B : Finset (Fin n)) (t : ℕ) (h : ParallelHistory n N t) : ℝ :=
  Gv P a m S ((univ \ B) \ Qset S h) h.2 - ∑ b ∈ Qset S h \ B, Wf P a S (h.2 b)

noncomputable def cost (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin (N + 1))) (x : Fin n → Fin (N + 1)) (s : Fin n → Bool) : ℝ :=
  ∑ b, if s b then conservationCoeff P a S (x b) else 0

lemma cc_nonneg (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (a : ℝ) (ha₀ : 0 < a) (S : Finset (Fin (N + 1))) (i : Fin (N + 1)) :
    0 ≤ conservationCoeff P a S i := by
  unfold conservationCoeff
  split_ifs
  · unfold stoppedTime
    refine integral_nonneg fun ω ↦ ?_
    unfold discountedStoppedSum
    refine tsum_nonneg fun t ↦ ?_
    split_ifs
    · positivity
    · exact le_rfl
  · exact le_rfl

lemma Qset_snoc (S : Finset (Fin (N + 1))) {t : ℕ} (h : ParallelHistory n N t)
    (s : Fin n → Bool) (x' : Fin n → Fin (N + 1)) :
    Qset S ((Fin.snoc (α := fun _ ↦ (Fin n → Fin (N + 1)) × (Fin n → Bool)) h.1 (h.2, s),
      x') : ParallelHistory n N (t + 1)) = Qset S h ∪ univ.filter (fun b ↦ h.2 b ∈ S) := by
  ext b
  simp only [Qset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Fin.exists_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]

lemma vT_integrable (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (I : Finset (Fin n)) (x : Fin n → Fin (N + 1)) (g : (Fin n → ℕ → Fin (N + 1)) → (Fin n → ℕ → Fin (N + 1)))
    (hg : Measurable g) :
    Integrable (fun ω ↦ vfun a m (Tsum S I (g ω))) (μpi P x) := by
  refine Integrable.of_bound (((measurable_of_countable (vfun a m)).comp
    ((measurable_Tsum S I).comp hg)).aestronglyMeasurable) (m / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (vfun_nonneg a ha0 ha1 m hm _)]
  exact vfun_le a ha0.le ha1 m _

lemma Gv_le (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (I : Finset (Fin n)) (x : Fin n → Fin (N + 1)) : Gv P a m S I x ≤ m / (1 - a) := by
  unfold Gv
  calc ∫ ω, vfun a m (Tsum S I ω) ∂μpi P x ≤ ∫ _ω, (m / (1 - a) : ℝ) ∂μpi P x :=
        integral_mono (vT_integrable P a ha0 ha1 m hm S I x id measurable_id) (integrable_const _)
          (fun ω ↦ vfun_le a ha0.le ha1 m _)
    _ = m / (1 - a) := by simp

lemma Λf_le (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (B : Finset (Fin n)) (t : ℕ) (h : ParallelHistory n N t) : Λf P a m S B t h ≤ m / (1 - a) := by
  unfold Λf
  have := Gv_le P a ha0 ha1 m hm S ((univ \ B) \ Qset S h) h.2
  have : 0 ≤ ∑ b ∈ Qset S h \ B, Wf P a S (h.2 b) :=
    Finset.sum_nonneg fun b _ ↦ Wf_nonneg P a ha0.le ha1 S _
  linarith

lemma one_step (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m M : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (B : Finset (Fin n)) (hBM : B.card + m ≤ M) (t : ℕ) (h : ParallelHistory n N t)
    (s : Fin n → Bool) (hs : selCount s = M) :
    Λf P a m S B t h ≤ cost P a S h.2 s + a * ∫ x', Λf P a m S B (t + 1)
      ((Fin.snoc (α := fun _ ↦ (Fin n → Fin (N + 1)) × (Fin n → Bool)) h.1 (h.2, s), x') :
        ParallelHistory n N (t + 1)) ∂(parallelMove P (h.2, s)) := by
  classical
  unfold Λf
  simp_rw [Qset_snoc]
  set x := h.2 with hx
  set Q := Qset S h with hQ
  set Q' := Q ∪ univ.filter (fun b ↦ x b ∈ S) with hQ'
  set I := (univ \ B) \ Q with hI
  set I' := I.filter (fun b ↦ x b ∉ S) with hI'
  have hI'eq : (univ \ B) \ Q' = I' := by
    ext b
    simp only [hQ', hI', hI, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  rw [hI'eq]
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
  simp_rw [move_coord P s x _ (Wf P a S)]
  have hG' : ∫ x', Gv P a m S I' x' ∂(parallelMove P (x, s)) =
      ∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b))) ∂μpi P x := by
    unfold Gv
    exact move_integral P s x (fun ω ↦ vfun a m (Tsum S I' ω))
      ((measurable_of_countable (vfun a m)).comp (measurable_Tsum S I')) (m / (1 - a))
      (fun ω ↦ by
        rw [abs_of_nonneg (vfun_nonneg a ha0 ha1 m hm _)]
        exact vfun_le a ha0.le ha1 m _)
  rw [hG']
  set p := ((Q' \ B).filter fun b ↦ s b = true).card with hp
  set e := (I'.filter fun b ↦ s b = true).card with he
  -- counting
  have hpe : m ≤ p + e := by
    have h1 : ((univ \ B).filter fun b ↦ s b = true).card = p + e := by
      rw [← Finset.card_filter_add_card_filter_not (p := fun b ↦ b ∈ Q')]
      congr 1
      · congr 1; ext b
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
      · rw [he, ← hI'eq]; congr 1; ext b
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
    have h2 : (univ.filter fun b ↦ s b = true) ⊆
        B ∪ ((univ \ B).filter fun b ↦ s b = true) := by
      intro b hb
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hb ⊢
      tauto
    have h3 := (Finset.card_le_card h2).trans (Finset.card_union_le _ _)
    unfold selCount at hs
    omega
  -- the G part
  have hGle : Gv P a m S I x ≤ p + a * ∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b))) ∂μpi P x := by
    unfold Gv
    have hcongr : ∫ ω, vfun a m (Tsum S I ω) ∂μpi P x =
        ∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b)) + e) ∂μpi P x :=
      integral_congr_ae ((ae_init P x).mono fun ω hω ↦ by
        simp only
        rw [Tsum_step S I s x ω hω])
    rw [hcongr]
    have hint := vT_integrable P a ha0 ha1 m hm S I' x _ (measurable_σ s)
    calc ∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b)) + e) ∂μpi P x
        ≤ ∫ ω, ((p : ℝ) + a * vfun a m (Tsum S I' (fun b ↦ σf s b (ω b)))) ∂μpi P x := by
          refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ vfun_nonneg a ha0 ha1 m hm _)
            ((integrable_const _).add (hint.const_mul a)) (ae_of_all _ fun ω ↦ ?_)
          exact vfun_bellman a ha0.le ha1 m hm p e hpe _
      _ = p + a * ∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b))) ∂μpi P x := by
          rw [integral_add (integrable_const _) (hint.const_mul a), integral_const_mul]
          simp
  -- the W part
  have hWeq : ∑ b ∈ Q \ B, Wf P a S (x b) = ∑ b ∈ Q' \ B, Wf P a S (x b) := by
    refine Finset.sum_subset (fun b hb ↦ ?_) (fun b hb hnb ↦ ?_)
    · simp only [hQ', Finset.mem_sdiff, Finset.mem_union] at hb ⊢
      exact ⟨Or.inl hb.1, hb.2⟩
    · simp only [hQ', Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb hnb
      have hxS : x b ∈ S := by tauto
      simp [Wf, hxS]
  have hcost : ∑ b ∈ Q' \ B, (if s b then conservationCoeff P a S (x b) else 0) ≤
      cost P a S x s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ ↦ by
      split_ifs
      · exact cc_nonneg P a ha0 S _
      · exact le_rfl)
  have hpsum : (p : ℝ) = ∑ b ∈ Q' \ B, (if s b then (1 : ℝ) else 0) := by
    rw [hp, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    split_ifs <;> simp
  have hterm : ∑ b ∈ Q' \ B, ((if s b then (1 : ℝ) else 0) - Wf P a S (x b)) ≤
      ∑ b ∈ Q' \ B, ((if s b then conservationCoeff P a S (x b) else 0) -
        a * (if s b then ∑ y, (P (x b)).real {y} * Wf P a S y else Wf P a S (x b))) := by
    refine Finset.sum_le_sum fun b _ ↦ ?_
    have hst := st_first P a ha0.le ha1 S (x b)
    have hW0 := Wf_nonneg P a ha0.le ha1 S (x b)
    by_cases hsb : s b = true
    · simp only [hsb, if_true]
      by_cases hxS : x b ∈ S
      · have e1 : conservationCoeff P a S (x b) =
            stoppedTime P a (hittingTime (↑S : Set (Fin (N + 1)))) (x b) := by
          simp [conservationCoeff, hxS]
        have e2 : Wf P a S (x b) = 0 := by simp [Wf, hxS]
        rw [e1, e2]; linarith
      · have e1 : conservationCoeff P a S (x b) = 0 := by simp [conservationCoeff, hxS]
        have e2 : Wf P a S (x b) =
            stoppedTime P a (hittingTime (↑S : Set (Fin (N + 1)))) (x b) := by
          simp [Wf, hxS]
        rw [e1, e2]; linarith
    · simp only [hsb, Bool.false_eq_true, if_false]
      nlinarith
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← hpsum, ← Finset.mul_sum] at hterm
  rw [hWeq]
  have : cost P a S x s + a * ((∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b))) ∂μpi P x) -
      ∑ b ∈ Q' \ B, (if s b then ∑ y, (P (x b)).real {y} * Wf P a S y else Wf P a S (x b))) =
      cost P a S x s + a * (∫ ω, vfun a m (Tsum S I' (fun b ↦ σf s b (ω b))) ∂μpi P x) -
      a * ∑ b ∈ Q' \ B, (if s b then ∑ y, (P (x b)).real {y} * Wf P a S y else Wf P a S (x b)) := by
    ring
  rw [this]
  linarith

end Pot

/-! ### iterating over the history law -/

section Iter

open AllocationIndices.Branching

variable {N n M : ℕ}

instance psk_markov (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (t : ℕ) : IsMarkovKernel (parallelStepKernel P π t) := by
  unfold parallelStepKernel; infer_instance

lemma pm_prob (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) :
    ∀ t, IsProbabilityMeasure (parallelMeasure P π k t)
  | 0 => by rw [parallelMeasure]; infer_instance
  | t + 1 => by
      haveI := pm_prob P π k t
      rw [parallelMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma pstep (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (t : ℕ)
    (f : ParallelHistory n N (t + 1) → ℝ) :
    ∫ h', f h' ∂parallelMeasure P π k (t + 1) =
      ∫ h, ∫ s, ∫ x', f ((Fin.snoc (α := fun _ ↦ (Fin n → Fin (N + 1)) × (Fin n → Bool)) h.1
        (h.2, s), x')) ∂(parallelMove P (h.2, s)) ∂(π.select t h) ∂parallelMeasure P π k t := by
  haveI := pm_prob P π k t
  rw [parallelMeasure, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    Measure.integral_compProd Integrable.of_finite]
  refine integral_congr_ae (ae_of_all _ fun h ↦ ?_)
  dsimp only
  rw [parallelStepKernel, ProbabilityTheory.integral_compProd Integrable.of_finite]
  simp only [Kernel.comap_apply]

lemma ae_sel (π : ParallelPolicy n N M) (t : ℕ) (h : ParallelHistory n N t) :
    ∀ᵐ s ∂(π.select t h), selCount s = M := by
  rw [ae_iff_measure_eq (Set.toFinite _).measurableSet.nullMeasurableSet, π.card_eq t h,
    measure_univ]

/-- the expected cost of period `u` -/
noncomputable def Cexp (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin (N + 1))) (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (u : ℕ) : ℝ :=
  ∫ h', cost P a S (h'.1 (Fin.last u)).1 (h'.1 (Fin.last u)).2 ∂parallelMeasure P π k (u + 1)

lemma iter_step (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (B : Finset (Fin n)) (hBM : B.card + m ≤ M) (π : ParallelPolicy n N M)
    (k : Fin n → Fin (N + 1)) (t : ℕ) :
    ∫ h, Λf P a m S B t h ∂parallelMeasure P π k t ≤
      Cexp P a S π k t + a * ∫ h, Λf P a m S B (t + 1) h ∂parallelMeasure P π k (t + 1) := by
  haveI := pm_prob P π k t
  haveI := pm_prob P π k (t + 1)
  have hsum : Cexp P a S π k t + a * ∫ h, Λf P a m S B (t + 1) h ∂parallelMeasure P π k (t + 1) =
      ∫ h', (cost P a S (h'.1 (Fin.last t)).1 (h'.1 (Fin.last t)).2 +
        a * Λf P a m S B (t + 1) h') ∂parallelMeasure P π k (t + 1) := by
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
    rfl
  rw [hsum, pstep]
  simp only [Fin.snoc_last]
  refine integral_mono Integrable.of_finite Integrable.of_finite (fun h ↦ ?_)
  calc Λf P a m S B t h = ∫ _s, Λf P a m S B t h ∂(π.select t h) := by simp
    _ ≤ _ := by
      refine integral_mono_ae Integrable.of_finite Integrable.of_finite
        ((ae_sel π t h).mono fun s hs ↦ ?_)
      dsimp only
      rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
      exact one_step P a ha0 ha1 m M hm S B hBM t h s hs

lemma iter (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (B : Finset (Fin n)) (hBM : B.card + m ≤ M) (π : ParallelPolicy n N M)
    (k : Fin n → Fin (N + 1)) (t : ℕ) :
    Λf P a m S B 0 (fun u ↦ u.elim0, k) ≤ ∑ u ∈ range t, a ^ u * Cexp P a S π k u +
      a ^ t * ∫ h, Λf P a m S B t h ∂parallelMeasure P π k t := by
  induction t with
  | zero =>
    simp only [range_zero, sum_empty, pow_zero, one_mul, zero_add]
    rw [parallelMeasure, integral_dirac]
  | succ t ih =>
    have h1 := iter_step P a ha0 ha1 m hm S B hBM π k t
    have hat : 0 ≤ a ^ t := pow_nonneg ha0.le t
    rw [sum_range_succ, pow_succ]
    have := mul_le_mul_of_nonneg_left h1 hat
    nlinarith

lemma cost_eq (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin (N + 1))) (x : Fin n → Fin (N + 1)) (s : Fin n → Bool) :
    cost P a S x s = ∑ i, conservationCoeff P a S i *
      ((univ.filter fun b ↦ s b = true ∧ x b = i).card : ℝ) := by
  unfold cost
  simp_rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hb : s b = true
  · simp [hb]
  · simp [hb]

lemma occ_le (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (i : Fin (N + 1)) (u : ℕ) :
    0 ≤ parallelOccupation P π k i u ∧ parallelOccupation P π k i u ≤ n := by
  haveI := pm_prob P π k (u + 1)
  unfold parallelOccupation
  refine ⟨integral_nonneg fun h ↦ Nat.cast_nonneg _, ?_⟩
  calc _ ≤ ∫ _h, (n : ℝ) ∂parallelMeasure P π k (u + 1) :=
        integral_mono Integrable.of_finite (integrable_const _) (fun h ↦ by
          have := Finset.card_le_univ (univ.filter fun b ↦ (h.1 (Fin.last u)).2 b = true ∧
            (h.1 (Fin.last u)).1 b = i)
          rw [Fintype.card_fin] at this
          exact Nat.cast_le.mpr this)
    _ = n := by simp

lemma partial_le (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (S : Finset (Fin (N + 1))) (π : ParallelPolicy n N M)
    (k : Fin n → Fin (N + 1)) (t : ℕ) :
    ∑ u ∈ range t, a ^ u * Cexp P a S π k u ≤ coeffSum P π a k S := by
  have hC : ∀ u, Cexp P a S π k u = ∑ i, conservationCoeff P a S i * parallelOccupation P π k i u := by
    intro u
    haveI := pm_prob P π k (u + 1)
    unfold Cexp parallelOccupation
    simp_rw [cost_eq]
    rw [integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
    simp_rw [integral_const_mul]
  simp_rw [hC, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold coeffSum parallelPerformance
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hA := cc_nonneg P a ha0 S i
  have hsumm : Summable fun u ↦ a ^ u * parallelOccupation P π k i u :=
    Summable.of_nonneg_of_le (fun u ↦ mul_nonneg (pow_nonneg ha0.le u) (occ_le P π k i u).1)
      (fun u ↦ by
        have := (occ_le P π k i u).2
        have h2 := pow_nonneg ha0.le u
        calc a ^ u * parallelOccupation P π k i u ≤ a ^ u * n := mul_le_mul_of_nonneg_left this h2
          _ = n * a ^ u := mul_comm _ _)
      ((summable_geometric_of_lt_one ha0.le ha1).mul_left (n : ℝ))
  calc ∑ u ∈ range t, a ^ u * (conservationCoeff P a S i * parallelOccupation P π k i u)
      = conservationCoeff P a S i * ∑ u ∈ range t, a ^ u * parallelOccupation P π k i u := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ ↦ ?_; ring
    _ ≤ conservationCoeff P a S i * ∑' u, a ^ u * parallelOccupation P π k i u :=
        mul_le_mul_of_nonneg_left (hsumm.sum_le_tsum _ (fun u _ ↦
          mul_nonneg (pow_nonneg ha0.le u) (occ_le P π k i u).1)) hA

lemma main_bound (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (S : Finset (Fin (N + 1)))
    (B : Finset (Fin n)) (hBM : B.card + m ≤ M) (π : ParallelPolicy n N M)
    (k : Fin n → Fin (N + 1)) :
    Λf P a m S B 0 (fun u ↦ u.elim0, k) ≤ coeffSum P π a k S := by
  set K : ℝ := m / (1 - a)
  have hb : ∀ t : ℕ, Λf P a m S B 0 (fun u ↦ u.elim0, k) ≤ coeffSum P π a k S + a ^ t * K := by
    intro t
    haveI := pm_prob P π k t
    have h1 := iter P a ha0 ha1 m hm S B hBM π k t
    have h2 := partial_le P a ha0 ha1 S π k t
    have h3 : ∫ h, Λf P a m S B t h ∂parallelMeasure P π k t ≤ K :=
      calc _ ≤ ∫ _h, K ∂parallelMeasure P π k t :=
            integral_mono Integrable.of_finite (integrable_const _)
              (fun h ↦ Λf_le P a ha0 ha1 m hm S B t h)
        _ = K := by simp
    have := mul_le_mul_of_nonneg_left h3 (pow_nonneg ha0.le t)
    linarith
  have hlim : Filter.Tendsto (fun t : ℕ ↦ coeffSum P π a k S + a ^ t * K) Filter.atTop
      (nhds (coeffSum P π a k S + 0 * K)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).mul_const K)
  have := ge_of_tendsto' hlim hb
  simpa using this

end Iter

/-! ### assembly -/

section Final

open AllocationIndices.Branching

variable {N n M : ℕ}

/-- A fixed selection of the first `M` arms gives a policy on `M` machines. -/
noncomputable def constPolicy (hMn : M ≤ n) : ParallelPolicy n N M where
  select _ := Kernel.const _ (Measure.dirac (fun b : Fin n ↦ decide ((b : ℕ) < M)))
  markov _ := inferInstance
  card_eq t h := by
    rw [Kernel.const_apply]
    refine Measure.dirac_apply_of_mem ?_
    show selCount (fun b : Fin n ↦ decide ((b : ℕ) < M)) = M
    unfold selCount
    have : (univ.filter fun b : Fin n ↦ decide ((b : ℕ) < M) = true) =
        univ.filter fun b : Fin n ↦ (b : ℕ) < M := by
      ext b; simp
    rw [this, Fin.card_filter_val_lt]
    omega

/-- `a^(T/m)`, `a^∞ = 0` -/
noncomputable def dfr (a : ℝ) (m : ℕ) (e : ℕ∞) : ℝ := match e with
  | (T : ℕ) => a ^ ((T : ℝ) / (m : ℝ))
  | ⊤ => 0

lemma dfr_coe (a : ℝ) (m T : ℕ) : dfr a m (T : ℕ∞) = a ^ ((T : ℝ) / (m : ℝ)) := rfl
lemma dfr_top (a : ℝ) (m : ℕ) : dfr a m ⊤ = 0 := rfl

lemma agg_le (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (arm : Fin (N + 1) → Fin n)
    (k : Fin n → Fin (N + 1)) (i : Fin (N + 1)) :
    (m : ℝ) / (1 - a) * aggregateEntryDiscount P a arm k i (m : ℝ) ≤
      Gv P a m (Iic i) (univ \ missedArms arm i) k := by
  have hA : aggregateEntryDiscount P a arm k i (m : ℝ) =
      ∫ ω, dfr a m (Tsum (Iic i) (univ \ missedArms arm i) ω) ∂μpi P k := by
    unfold aggregateEntryDiscount Tsum μpi
    rw [Finset.coe_Iic]
    rfl
  have hint : Integrable (fun ω ↦ dfr a m (Tsum (Iic i) (univ \ missedArms arm i) ω))
      (μpi P k) := by
    refine Integrable.of_bound (((measurable_of_countable (dfr a m)).comp
      (measurable_Tsum _ _)).aestronglyMeasurable) 1 (ae_of_all _ fun ω ↦ ?_)
    generalize Tsum (Iic i) (univ \ missedArms arm i) ω = e
    induction e using ENat.recTopCoe with
    | top => simp [dfr_top]
    | coe T =>
      rw [dfr_coe, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ha0.le _)]
      exact Real.rpow_le_one ha0.le ha1.le (by positivity)
  rw [hA, ← integral_const_mul]
  unfold Gv
  refine integral_mono (hint.const_mul _) (vT_integrable P a ha0 ha1 m hm _ _ k id measurable_id)
    (fun ω ↦ ?_)
  dsimp only [id]
  generalize Tsum (Iic i) (univ \ missedArms arm i) ω = e
  induction e using ENat.recTopCoe with
  | top => simp [dfr_top, vfun_top]
  | coe T =>
    rw [dfr_coe]
    exact vfun_lower a ha0 ha1 m hm T

end Final

end P2MCF

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices AllocationIndices.Branching in
theorem solution {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (i : Fin (N + 1))
    (hψ : psi arm i ≤ M - 1) :
    ((M : ℝ) - psi arm i) / (1 - a) *
        aggregateEntryDiscount P a arm k i ((M : ℝ) - psi arm i) ≤
      minCoeffSum P M a k (Iic i) := by
  have hpsiM : psi arm i ≤ M := by omega
  have hm : 0 < M - psi arm i := by omega
  have hcard : (missedArms arm i).card = psi arm i := rfl
  have hBM : (missedArms arm i).card + (M - psi arm i) ≤ M := by omega
  have hcast : ((M : ℝ) - psi arm i) = ((M - psi arm i : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpsiM]
  rw [hcast]
  have h0 := P2MCF.agg_le P a ha₀ ha₁ (M - psi arm i) hm arm k i
  have hΛ0 : P2MCF.Λf P a (M - psi arm i) (Iic i) (missedArms arm i) 0 (fun u ↦ u.elim0, k) =
      P2MCF.Gv P a (M - psi arm i) (Iic i) (univ \ missedArms arm i) k := by
    unfold P2MCF.Λf
    have : P2MCF.Qset (Iic i) ((fun u ↦ u.elim0, k) : ParallelHistory n N 0) = ∅ := by
      ext b
      simp [P2MCF.Qset]
    rw [this]
    simp
  haveI : Nonempty (ParallelPolicy n N M) := ⟨P2MCF.constPolicy hMn⟩
  refine h0.trans ?_
  rw [← hΛ0]
  exact le_ciInf fun π ↦ P2MCF.main_bound P a ha₀ ha₁ (M - psi arm i) hm (Iic i)
    (missedArms arm i) hBM π k
