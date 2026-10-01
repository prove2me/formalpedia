-- Prove2me | solution 1 for AllocationIndices.sfabp_conservation_laws
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T11:38:50.229407+00:00
-- url     : https://prove2.me/submissions/1d416e3a-0815-41e5-af43-eeea181b31b3

import Mathlib
import Definitions.Def_AllocationIndices_Achievable

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices

namespace P2MFC

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

/-! ### bandit measure -/

section Bandit

variable {n : ℕ}

lemma real_sum_one {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] : ∑ j, ν.real {j} = 1 := by
  have := integral_fintype (μ := ν) (f := fun _ ↦ (1 : ℝ)) Integrable.of_finite
  simpa using this.symm

lemma step_integral (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    (π : MarkovBanditPolicy n (Fin N)) (k : Fin n → Fin N) (t : ℕ)
    (f : MarkovBanditHistory n (Fin N) (t + 1) → ℝ) :
    ∫ h, f h ∂markovBanditMeasure P π k (t + 1) =
      ∫ h, ∑ j, (π.select t h).real {j} * ∑ y, (P (h.2 j)).real {y} *
        f (Fin.snoc (α := fun _ ↦ (Fin n → Fin N) × Fin n) h.1 (h.2, j),
          Function.update h.2 j y) ∂markovBanditMeasure P π k t := by
  rw [markovBanditMeasure, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    Measure.integral_compProd Integrable.of_finite]
  refine integral_congr_ae (ae_of_all _ fun h ↦ ?_)
  dsimp only
  rw [markovBanditStepKernel, ProbabilityTheory.integral_compProd Integrable.of_finite,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Kernel.comap_apply, integral_fintype Integrable.of_finite, smul_eq_mul]
  simp [smul_eq_mul]

/-- state of the arm continued in the last recorded round -/
def recState {t : ℕ} (h : MarkovBanditHistory n (Fin N) (t + 1)) : Fin N :=
  (h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)

lemma occ_sum (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    (π : MarkovBanditPolicy n (Fin N)) (k : Fin n → Fin N) (t : ℕ) (c : Fin N → ℝ) :
    ∑ i, c i * roundOccupation P π k i t =
      ∫ h, c (recState h) ∂markovBanditMeasure P π k (t + 1) := by
  rw [← integral_map (measurable_of_countable recState).aemeasurable
    (measurable_of_countable c).aestronglyMeasurable, integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul, mul_comm, map_measureReal_apply (measurable_of_countable _)
    (measurableSet_singleton i)]
  rfl

lemma occ_bounds (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    (π : MarkovBanditPolicy n (Fin N)) (k : Fin n → Fin N) (i : Fin N) (t : ℕ) :
    0 ≤ roundOccupation P π k i t ∧ roundOccupation P π k i t ≤ 1 := by
  unfold roundOccupation
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩

/-- g -/
noncomputable def gS (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  discountAtStop P a (hittingTime (↑S : Set (Fin N))) i

/-- φ -/
noncomputable def φS (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ S then 1 else gS P a S i

lemma base_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (S : Finset (Fin N))
    (x : Fin n → Fin N) :
    conservationBase P a x S = (1 - a)⁻¹ * ∏ l, φS P a S (x l) := by
  unfold conservationBase φS gS
  rw [Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  by_cases h : x l ∈ S <;> simp [h]

/-- slack -/
noncomputable def slack (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin N)) (x : Fin n → Fin N) (j : Fin n) : ℝ :=
  conservationCoeff P a S (x j) +
    a * ∑ y, (P (x j)).real {y} * conservationBase P a (Function.update x j y) S -
      conservationBase P a x S

lemma slack_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin N)) (x : Fin n → Fin N) (j : Fin n) :
    slack P a S x j = if x j ∈ S then
      (1 - a)⁻¹ * (1 - gS P a S (x j)) * (1 - ∏ l ∈ univ \ {j}, φS P a S (x l)) else 0 := by
  classical
  set R := ∏ l ∈ univ \ {j}, φS P a S (x l) with hR
  have hupd : ∀ y, ∏ l, φS P a S (Function.update x j y l) = φS P a S y * R := by
    intro y
    have : (fun l ↦ φS P a S (Function.update x j y l)) =
        Function.update (fun l ↦ φS P a S (x l)) j (φS P a S y) := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rw [show ∏ l, φS P a S (Function.update x j y l) =
      ∏ l, Function.update (fun l ↦ φS P a S (x l)) j (φS P a S y) l by rw [← this],
      Finset.prod_update_of_mem (mem_univ j)]
  have hself : ∏ l, φS P a S (x l) = φS P a S (x j) * R := by
    have := hupd (x j)
    rwa [Function.update_eq_self] at this
  have hfs : gS P a S (x j) = a * ∑ y, (P (x j)).real {y} * φS P a S y := by
    unfold gS φS
    exact first_step P a ha0 ha1.le S (x j)
  have hsum : a * ∑ y, (P (x j)).real {y} * conservationBase P a (Function.update x j y) S =
      (1 - a)⁻¹ * R * gS P a S (x j) := by
    simp_rw [base_eq, hupd]
    rw [hfs, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    ring
  unfold slack
  rw [hsum, base_eq, hself]
  unfold conservationCoeff
  by_cases hj : x j ∈ S
  · rw [if_pos hj, if_pos hj, stoppedTime_eq P a ha0 ha1]
    have : φS P a S (x j) = 1 := by simp [φS, hj]
    rw [this]
    unfold gS
    rw [div_eq_mul_inv]
    ring
  · rw [if_neg hj, if_neg hj]
    have : φS P a S (x j) = gS P a S (x j) := by simp [φS, hj]
    rw [this]
    ring

lemma φS_bounds (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (S : Finset (Fin N)) (i : Fin N) : 0 ≤ φS P a S i ∧ φS P a S i ≤ 1 := by
  unfold φS
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · have := g_bounds P a ha0 ha1 (↑S : Set (Fin N)) i
    exact ⟨this.1, this.2.trans ha1⟩

lemma slack_nonneg (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin N)) (x : Fin n → Fin N) (j : Fin n) :
    0 ≤ slack P a S x j := by
  rw [slack_eq P a ha0 ha1]
  split_ifs
  · have hg := g_bounds P a ha0 ha1.le (↑S : Set (Fin N)) (x j)
    have hR : ∏ l ∈ univ \ {j}, φS P a S (x l) ≤ 1 :=
      Finset.prod_le_one (fun l _ ↦ (φS_bounds P a ha0 ha1.le S (x l)).1)
        (fun l _ ↦ (φS_bounds P a ha0 ha1.le S (x l)).2)
    have h1 : 0 ≤ 1 - gS P a S (x j) := by unfold gS; linarith [hg.2]
    have h2 : 0 ≤ (1 - a)⁻¹ := inv_nonneg.2 (by linarith)
    exact mul_nonneg (mul_nonneg h2 h1) (by linarith)
  · exact le_rfl

lemma slack_zero_all (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin N)) (x : Fin n → Fin N) (hall : ∀ l, x l ∈ S) (j : Fin n) :
    slack P a S x j = 0 := by
  rw [slack_eq P a ha0 ha1]
  have : ∏ l ∈ univ \ {j}, φS P a S (x l) = 1 :=
    Finset.prod_eq_one (fun l _ ↦ by simp [φS, hall l])
  rw [this]
  simp

lemma slack_zero_out (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (S : Finset (Fin N)) (x : Fin n → Fin N) (j : Fin n) (hj : x j ∉ S) :
    slack P a S x j = 0 := by
  rw [slack_eq P a ha0 ha1, if_neg hj]

lemma key (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin N)) (π : MarkovBanditPolicy n (Fin N)) (k : Fin n → Fin N) (t : ℕ) :
    (∫ h, conservationCoeff P a S (recState h) ∂markovBanditMeasure P π k (t + 1)) +
      a * ∫ h, conservationBase P a h.2 S ∂markovBanditMeasure P π k (t + 1) =
    (∫ h, conservationBase P a h.2 S ∂markovBanditMeasure P π k t) +
      ∫ h, ∑ j, (π.select t h).real {j} * slack P a S h.2 j ∂markovBanditMeasure P π k t := by
  rw [← integral_const_mul, ← integral_add Integrable.of_finite Integrable.of_finite,
    step_integral, ← integral_add Integrable.of_finite Integrable.of_finite]
  refine integral_congr_ae (ae_of_all _ fun h ↦ ?_)
  dsimp only
  have hin : ∀ j, ∑ y, (P (h.2 j)).real {y} *
      (conservationCoeff P a S (recState ((Fin.snoc (α := fun _ ↦ (Fin n → Fin N) × Fin n)
        h.1 (h.2, j), Function.update h.2 j y) : MarkovBanditHistory n (Fin N) (t + 1))) +
        a * conservationBase P a (Function.update h.2 j y) S) =
      conservationBase P a h.2 S + slack P a S h.2 j := by
    intro j
    have hr : ∀ y, recState ((Fin.snoc (α := fun _ ↦ (Fin n → Fin N) × Fin n)
        h.1 (h.2, j), Function.update h.2 j y) : MarkovBanditHistory n (Fin N) (t + 1)) =
        h.2 j := by
      intro y
      simp [recState]
    simp_rw [hr]
    have e1 : ∑ y, (P (h.2 j)).real {y} * (conservationCoeff P a S (h.2 j) +
        a * conservationBase P a (Function.update h.2 j y) S) =
        conservationCoeff P a S (h.2 j) * ∑ y, (P (h.2 j)).real {y} +
        a * ∑ y, (P (h.2 j)).real {y} * conservationBase P a (Function.update h.2 j y) S := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ by ring
    rw [e1, real_sum_one]
    unfold slack
    ring
  simp_rw [hin]
  have e2 : ∑ j, (π.select t h).real {j} * (conservationBase P a h.2 S + slack P a S h.2 j) =
      conservationBase P a h.2 S * ∑ j, (π.select t h).real {j} +
        ∑ j, (π.select t h).real {j} * slack P a S h.2 j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by ring
  rw [e2, real_sum_one]
  ring

end Bandit

end P2MFC

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem solution {N n : ℕ} (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : Fin n → Fin N) (π : MarkovBanditPolicy n (Fin N))
    (S : Finset (Fin N)) :
    (∀ i ∈ S, 0 < conservationCoeff P a S i) ∧
    conservationBase P a k S ≤ ∑ i ∈ S, conservationCoeff P a S i * performance P π a k i ∧
    ∑ i, performance P π a k i = (1 - a)⁻¹ ∧
    (GivesPriority S π →
      ∑ i ∈ S, conservationCoeff P a S i * performance P π a k i = conservationBase P a k S) := by
  have h1a : 0 < 1 - a := by linarith
  have hcoeff : ∀ i, conservationCoeff P a S i =
      if i ∈ S then (1 - P2MFC.gS P a S i) / (1 - a) else 0 := by
    intro i
    unfold conservationCoeff P2MFC.gS
    split_ifs
    · exact P2MFC.stoppedTime_eq P a ha0.le ha1 _ i
    · rfl
  have hcb : ∀ i, 0 ≤ conservationCoeff P a S i ∧ conservationCoeff P a S i ≤ (1 - a)⁻¹ := by
    intro i
    rw [hcoeff]
    split_ifs
    · have hg := P2MFC.g_bounds P a ha0.le ha1.le (↑S : Set (Fin N)) i
      unfold P2MFC.gS
      refine ⟨div_nonneg (by linarith [hg.2]) h1a.le, ?_⟩
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.2 h1a.le) (by linarith [hg.1])
    · exact ⟨le_rfl, inv_nonneg.2 h1a.le⟩
  have hVb : ∀ x : Fin n → Fin N, 0 ≤ conservationBase P a x S ∧
      conservationBase P a x S ≤ (1 - a)⁻¹ := by
    intro x
    rw [P2MFC.base_eq]
    have h0 : 0 ≤ ∏ l, P2MFC.φS P a S (x l) :=
      Finset.prod_nonneg (fun l _ ↦ (P2MFC.φS_bounds P a ha0.le ha1.le S (x l)).1)
    have h1 : ∏ l, P2MFC.φS P a S (x l) ≤ 1 :=
      Finset.prod_le_one (fun l _ ↦ (P2MFC.φS_bounds P a ha0.le ha1.le S (x l)).1)
        (fun l _ ↦ (P2MFC.φS_bounds P a ha0.le ha1.le S (x l)).2)
    exact ⟨mul_nonneg (inv_nonneg.2 h1a.le) h0,
      mul_le_of_le_one_right (inv_nonneg.2 h1a.le) h1⟩
  -- the three sequences
  set E : ℕ → ℝ := fun t ↦ ∫ h, conservationBase P a h.2 S ∂markovBanditMeasure P π k t with hE
  set C : ℕ → ℝ := fun t ↦
    ∫ h, conservationCoeff P a S (P2MFC.recState h) ∂markovBanditMeasure P π k (t + 1) with hC
  set Sl : ℕ → ℝ := fun t ↦ ∫ h, ∑ j, (π.select t h).real {j} * P2MFC.slack P a S h.2 j
    ∂markovBanditMeasure P π k t with hSl
  have hkey : ∀ t, C t + a * E (t + 1) = E t + Sl t := fun t ↦ P2MFC.key P a S π k t
  have hE0 : E 0 = conservationBase P a k S := by
    simp only [hE]
    rw [markovBanditMeasure, integral_dirac]
  have hEb : ∀ t, 0 ≤ E t ∧ E t ≤ (1 - a)⁻¹ := by
    intro t
    refine ⟨integral_nonneg fun h ↦ (hVb h.2).1, ?_⟩
    calc E t ≤ ∫ _h, (1 - a)⁻¹ ∂markovBanditMeasure P π k t :=
          integral_mono Integrable.of_finite (integrable_const _) (fun h ↦ (hVb h.2).2)
      _ = (1 - a)⁻¹ := by simp
  have hCb : ∀ t, 0 ≤ C t ∧ C t ≤ (1 - a)⁻¹ := by
    intro t
    refine ⟨integral_nonneg fun h ↦ (hcb _).1, ?_⟩
    calc C t ≤ ∫ _h, (1 - a)⁻¹ ∂markovBanditMeasure P π k (t + 1) :=
          integral_mono Integrable.of_finite (integrable_const _) (fun h ↦ (hcb _).2)
      _ = (1 - a)⁻¹ := by simp
  have hSl0 : ∀ t, 0 ≤ Sl t := fun t ↦ integral_nonneg fun h ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg measureReal_nonneg
      (P2MFC.slack_nonneg P a ha0.le ha1 S h.2 j)
  have hgeo := summable_geometric_of_lt_one ha0.le ha1
  have hsb : ∀ X : ℕ → ℝ, (∀ t, 0 ≤ X t ∧ X t ≤ (1 - a)⁻¹) → Summable (fun t ↦ a ^ t * X t) := by
    intro X hX
    refine Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (hX t).1)
      (fun t ↦ ?_) (hgeo.mul_right (1 - a)⁻¹)
    exact mul_le_mul_of_nonneg_left (hX t).2 (pow_nonneg ha0.le t)
  have hu : Summable (fun t ↦ a ^ t * E t) := hsb E hEb
  have hu1 : Summable (fun t ↦ a ^ (t + 1) * E (t + 1)) :=
    (summable_nat_add_iff 1).2 hu
  have hCs : Summable (fun t ↦ a ^ t * C t) := hsb C hCb
  have hrel : ∀ t, a ^ t * C t =
      (a ^ t * E t - a ^ (t + 1) * E (t + 1)) + a ^ t * Sl t := by
    intro t
    have := hkey t
    rw [pow_succ]
    linear_combination (a ^ t) * this
  have hSls : Summable (fun t ↦ a ^ t * Sl t) := by
    have : (fun t ↦ a ^ t * Sl t) =
        fun t ↦ a ^ t * C t - (a ^ t * E t - a ^ (t + 1) * E (t + 1)) := by
      funext t; rw [hrel t]; ring
    rw [this]
    exact hCs.sub (hu.sub hu1)
  have htot : ∑' t, a ^ t * C t = conservationBase P a k S + ∑' t, a ^ t * Sl t := by
    rw [tsum_congr hrel, Summable.tsum_add (hu.sub hu1) hSls, Summable.tsum_sub hu hu1,
      hu.tsum_eq_zero_add, ← hE0]
    simp
  -- performance sums
  have hocc : ∀ i, Summable (fun t ↦ a ^ t * roundOccupation P π k i t) := by
    intro i
    refine Summable.of_nonneg_of_le
      (fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (P2MFC.occ_bounds P π k i t).1) (fun t ↦ ?_) hgeo
    exact mul_le_of_le_one_right (pow_nonneg ha0.le t) (P2MFC.occ_bounds P π k i t).2
  have hperf : ∑ i ∈ S, conservationCoeff P a S i * performance P π a k i =
      ∑' t, a ^ t * C t := by
    unfold performance
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun i _ ↦ (hocc i).mul_left _)]
    refine tsum_congr fun t ↦ ?_
    simp only [hC]
    rw [← P2MFC.occ_sum, Finset.mul_sum]
    rw [Finset.sum_subset (subset_univ S) (fun i _ hi ↦ by rw [hcoeff i, if_neg hi]; ring)]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  refine ⟨fun i hi ↦ ?_, ?_, ?_, fun hP ↦ ?_⟩
  · rw [hcoeff i, if_pos hi]
    have hg := P2MFC.g_bounds P a ha0.le ha1.le (↑S : Set (Fin N)) i
    unfold P2MFC.gS
    exact div_pos (by linarith [hg.2]) h1a
  · rw [hperf, htot]
    have : 0 ≤ ∑' t, a ^ t * Sl t :=
      tsum_nonneg fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (hSl0 t)
    linarith
  · unfold performance
    rw [← Summable.tsum_finsetSum (fun i _ ↦ hocc i)]
    have : ∀ t, ∑ i, a ^ t * roundOccupation P π k i t = a ^ t := by
      intro t
      rw [← Finset.mul_sum]
      have := P2MFC.occ_sum P π k t (fun _ ↦ 1)
      simp only [one_mul] at this
      rw [this]
      simp
    rw [tsum_congr this, tsum_geometric_of_lt_one ha0.le ha1]
  · rw [hperf, htot]
    have hz : ∀ t, Sl t = 0 := by
      intro t
      simp only [hSl]
      refine (integral_congr_ae (ae_of_all _ fun h ↦ ?_)).trans (integral_zero _ _)
      by_cases hall : ∀ l, h.2 l ∈ S
      · exact Finset.sum_eq_zero fun j _ ↦ by
          rw [P2MFC.slack_zero_all P a ha0.le ha1 S h.2 hall j, mul_zero]
      · push_neg at hall
        have h1 := hP t h hall
        have hc : (π.select t h) {j | h.2 j ∉ S}ᶜ = 0 :=
          (prob_compl_eq_zero_iff (Set.toFinite _).measurableSet).2 h1
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        by_cases hj : h.2 j ∈ S
        · have : (π.select t h) {j} = 0 :=
            measure_mono_null (fun z hz ↦ by
              rw [Set.mem_singleton_iff] at hz
              subst hz
              simpa using hj) hc
          rw [measureReal_def, this, ENNReal.toReal_zero, zero_mul]
        · rw [P2MFC.slack_zero_out P a ha0.le ha1 S h.2 j hj, mul_zero]
    simp [hz]
