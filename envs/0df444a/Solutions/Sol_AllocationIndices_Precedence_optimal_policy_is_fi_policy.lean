-- Prove2me | solution 1 for AllocationIndices.Precedence.optimal_policy_is_fi_policy
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:32:30.8178+00:00
-- url     : https://prove2.me/submissions/9f52839e-0148-44db-80dc-52aa0f4d617b

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

section OptimalIsFIHelpers

open AllocationIndices.Precedence

/-! ### Section 1: Discount parameters `φ_i`, `a_i`, `c_i` and almost-sure positivity -/

private noncomputable def phi {n : ℕ} (F : JobFamily n) (i : Fin n) : ℝ :=
  ∫ x, Real.exp (-F.γ * x) ∂(F.service i : Measure ℝ)

private noncomputable def jobA {n : ℕ} (F : JobFamily n) (i : Fin n) : ℝ :=
  F.reward i * phi F i

private noncomputable def jobC {n : ℕ} (F : JobFamily n) (i : Fin n) : ℝ :=
  F.γ⁻¹ * (1 - phi F i)

private lemma serviceLaw_isProb {n : ℕ} (F : JobFamily n) :
    IsProbabilityMeasure (serviceLaw F) := by
  unfold serviceLaw
  infer_instance

private lemma service_pos_ae {n : ℕ} (F : JobFamily n) (i : Fin n) :
    ∀ᵐ x ∂(F.service i : Measure ℝ), 0 < x := by
  have hset : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp [not_lt]
  rw [ae_iff, hset, F.service_pos i]

private lemma serviceLaw_pos_ae {n : ℕ} (F : JobFamily n) :
    ∀ᵐ ω ∂serviceLaw F, ∀ i : Fin n, 0 < ω i := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have hset : {ω : Fin n → ℝ | ¬ 0 < ω i} =
      Set.univ.pi (fun j => if j = i then Set.Iic (0 : ℝ) else Set.univ) := by
    ext ω
    simp [Set.mem_pi, not_lt]
  rw [hset, serviceLaw, Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [F.service_pos i]

private lemma integrable_exp_service {n : ℕ} (F : JobFamily n) (i : Fin n) :
    Integrable (fun x => Real.exp (-F.γ * x)) (F.service i : Measure ℝ) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards [service_pos_ae F i] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos])

private lemma phi_pos {n : ℕ} (F : JobFamily n) (i : Fin n) : 0 < phi F i := by
  unfold phi
  rw [integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun x => (Real.exp_pos _).le) (integrable_exp_service F i)]
  have hsup : Function.support (fun x => Real.exp (-F.γ * x)) = Set.univ := by
    ext x
    simp [(Real.exp_pos _).ne']
  rw [hsup, measure_univ]
  exact zero_lt_one

private lemma phi_lt_one {n : ℕ} (F : JobFamily n) (i : Fin n) : phi F i < 1 := by
  have hint : Integrable (fun x => 1 - Real.exp (-F.γ * x)) (F.service i : Measure ℝ) :=
    (integrable_const (1 : ℝ)).sub (integrable_exp_service F i)
  have hnn : 0 ≤ᵐ[(F.service i : Measure ℝ)] (fun x => 1 - Real.exp (-F.γ * x)) := by
    filter_upwards [service_pos_ae F i] with x hx
    have hle : Real.exp (-F.γ * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos])
    exact sub_nonneg.mpr hle
  have hpos : 0 < ∫ x, (1 - Real.exp (-F.γ * x)) ∂(F.service i : Measure ℝ) := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun x => 1 - Real.exp (-F.γ * x)) := by
      intro x hx
      have hx' : 0 < x := hx
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      have : Real.exp (-F.γ * x) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [F.γ_pos, hx'])
      linarith
    have hmeas : (F.service i : Measure ℝ) (Set.Ioi 0) = 1 := by
      have hcompl : Set.Ioi (0 : ℝ) = (Set.Iic 0)ᶜ := by ext x; simp
      rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
        F.service_pos i, tsub_zero]
    calc (0 : ENNReal) < 1 := zero_lt_one
      _ = (F.service i : Measure ℝ) (Set.Ioi 0) := hmeas.symm
      _ ≤ (F.service i : Measure ℝ) (Function.support (fun x => 1 - Real.exp (-F.γ * x))) :=
        measure_mono hsub
  rw [integral_sub (integrable_const 1) (integrable_exp_service F i), integral_const] at hpos
  simp only [probReal_univ, one_smul] at hpos
  unfold phi
  linarith

private lemma jobA_pos {n : ℕ} (F : JobFamily n) (i : Fin n) : 0 < jobA F i :=
  mul_pos (F.reward_pos i) (phi_pos F i)

private lemma jobC_pos {n : ℕ} (F : JobFamily n) (i : Fin n) : 0 < jobC F i :=
  mul_pos (inv_pos.mpr F.γ_pos) (sub_pos.mpr (phi_lt_one F i))

/-! ### Section 2: Coordinate independence / Fubini on `serviceLaw F` -/

private lemma integral_mul_exp_of_indep {n : ℕ} (F : JobFamily n) (j : Fin n)
    (f : (Fin n → ℝ) → ℝ)
    (hindep : ∀ ω x, f (Function.update ω j x) = f ω) :
    ∫ ω, f ω * Real.exp (-F.γ * ω j) ∂serviceLaw F =
      (∫ ω, f ω ∂serviceLaw F) * phi F j := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    let μ : Fin (m + 1) → Measure ℝ := fun i => (F.service i : Measure ℝ)
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j).symm
    have hmp := (measurePreserving_piFinSuccAbove μ j).symm
    have hupd : ∀ (x : ℝ) (y : Fin m → ℝ),
        f (e (x, y)) = f (e (0, y)) := by
      intro x y
      have heq : Function.update (e (x, y)) j 0 = e (0, y) := by
        ext k
        by_cases hkj : k = j
        · subst hkj
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hkj
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, hkj]
      rw [← hindep (e (x, y)) 0, heq]
    have h1 : ∫ ω, f ω * Real.exp (-F.γ * ω j) ∂serviceLaw F =
        (∫ x, Real.exp (-F.γ * x) ∂(μ j)) *
        (∫ y, f (e (0, y)) ∂(Measure.pi fun k => μ (j.succAbove k))) := by
      change ∫ ω, f ω * Real.exp (-F.γ * ω j) ∂(Measure.pi μ) = _
      rw [← hmp.integral_comp']
      have hfun : (fun p : ℝ × (Fin m → ℝ) => f (e p) * Real.exp (-F.γ * e p j)) =
          (fun p : ℝ × (Fin m → ℝ) => Real.exp (-F.γ * p.1) * f (e (0, p.2))) := by
        ext ⟨x, y⟩
        rw [hupd x y, mul_comm]
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rw [hfun]
      exact integral_prod_mul (fun x => Real.exp (-F.γ * x)) (fun y => f (e (0, y)))
    have h2 : ∫ ω, f ω ∂serviceLaw F =
        ∫ y, f (e (0, y)) ∂(Measure.pi fun k => μ (j.succAbove k)) := by
      change ∫ ω, f ω ∂(Measure.pi μ) = _
      rw [← hmp.integral_comp']
      have hfun : (fun p : ℝ × (Fin m → ℝ) => f (e p)) =
          (fun p : ℝ × (Fin m → ℝ) => (1 : ℝ) * f (e (0, p.2))) := by
        ext ⟨x, y⟩
        rw [one_mul, hupd x y]
      rw [hfun, integral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun y => f (e (0, y)))]
      simp [μ]
    rw [h1, h2, mul_comm]
    rfl

/-! ### Section 3: Policy history structure, measurability, and step-expectation reduction -/

private def histVec {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) : (k : ℕ) → Fin k → Fin n × ℝ
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (histVec π ω k) (π.job ω k, ω (π.job ω k))

private lemma ofFn_histVec {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    List.ofFn (histVec π ω k) = π.hist ω k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [histVec, List.ofFn_succ']
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    rw [List.concat_eq_append, ih]
    rfl

private lemma measurable_histVec {n : ℕ} (π : Policy n) :
    ∀ k : ℕ, Measurable fun ω : Fin n → ℝ => histVec π ω k
  | 0 => measurable_pi_lambda _ fun i => Fin.elim0 i
  | k + 1 => by
    have ih := measurable_histVec π k
    have hjob : Measurable fun ω : Fin n → ℝ => π.job ω k := by
      have h := (π.measurable_next k).comp ih
      convert h using 1
      ext ω
      simp only [Function.comp_apply, Policy.job, ofFn_histVec]
    have hval : Measurable fun ω : Fin n → ℝ => ω (π.job ω k) := by
      have heq : (fun ω : Fin n → ℝ => ω (π.job ω k)) =
          (fun ω => ∑ i : Fin n, if π.job ω k = i then ω i else 0) := by
        ext ω
        simp
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => ?_
      exact Measurable.ite (hjob (measurableSet_singleton i)) (measurable_pi_apply i) measurable_const
    refine measurable_pi_lambda _ fun i => ?_
    refine Fin.lastCases ?_ ?_ i
    · simp only [histVec, Fin.snoc_last]
      exact hjob.prodMk hval
    · intro j
      simp only [histVec, Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp ih

private lemma measurable_job {n : ℕ} (π : Policy n) (k : ℕ) :
    Measurable fun ω : Fin n → ℝ => π.job ω k := by
  have h := (π.measurable_next k).comp (measurable_histVec π k)
  convert h using 1
  ext ω
  simp only [Function.comp_apply, Policy.job, ofFn_histVec]

private lemma measurable_elapsed {n : ℕ} (π : Policy n) (k : ℕ) :
    Measurable fun ω : Fin n → ℝ => (π.hist ω k).elapsed := by
  have heq : (fun ω : Fin n → ℝ => (π.hist ω k).elapsed) =
      (fun ω => ∑ i : Fin k, (histVec π ω k i).2) := by
    ext ω
    rw [← ofFn_histVec π ω k, History.elapsed, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [heq]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_snd.comp ((measurable_pi_apply i).comp (measurable_histVec π k))

private lemma measurable_startTime {n : ℕ} (π : Policy n) (k : ℕ) :
    Measurable fun ω : Fin n → ℝ => π.startTime ω k :=
  measurable_elapsed π k

private lemma measurable_completionTime {n : ℕ} (π : Policy n) (k : ℕ) :
    Measurable fun ω : Fin n → ℝ => π.completionTime ω k :=
  measurable_elapsed π (k + 1)

private lemma measurable_of_finite_discrete {β α : Type*} [Finite β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [MeasurableSpace α] (g : β → α) : Measurable g := by
  intro s _
  rw [← Set.biUnion_of_singleton (g ⁻¹' s)]
  exact Set.Finite.measurableSet_biUnion (Set.toFinite _) fun x _ => measurableSet_singleton x

private lemma measurable_jobs_comp {n : ℕ} {α : Type*} [MeasurableSpace α]
    (π : Policy n) (k : ℕ) (g : Finset (Fin n) → α) :
    Measurable fun ω : Fin n → ℝ => g (π.hist ω k).jobs := by
  have h1 : Measurable fun ω : Fin n → ℝ => fun i : Fin k => (histVec π ω k i).1 :=
    measurable_pi_lambda _ fun i =>
      measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histVec π k))
  have heq : (fun ω : Fin n → ℝ => g (π.hist ω k).jobs) =
      (fun v : Fin k → Fin n => g (List.ofFn v).toFinset) ∘
        (fun ω : Fin n → ℝ => fun i : Fin k => (histVec π ω k i).1) := by
    ext ω
    simp only [Function.comp_apply, History.jobs, ← ofFn_histVec π ω k, List.map_ofFn]
    rfl
  rw [heq]
  exact (measurable_of_finite_discrete _).comp h1

private lemma measurableSet_inStage {n : ℕ} (B : Finset (Fin n)) (p : Stage n) (k : ℕ) :
    MeasurableSet {ω : Fin n → ℝ | p.InStage B ω k} := by
  unfold Stage.InStage
  rw [Set.ofPred_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  have heq : {ω : Fin n → ℝ | ∀ l ∈ Finset.Icc 1 k, p.stop (p.toPolicy.hist ω l) = false} =
      ⋂ l ∈ Finset.Icc 1 k, {ω | p.stop (p.toPolicy.hist ω l) = false} := by
    ext ω; simp
  rw [heq]
  refine Finset.measurableSet_biInter _ fun l _ => ?_
  have hstop : Measurable fun ω : Fin n → ℝ => p.stop (p.toPolicy.hist ω l) := by
    have h := (p.measurable_stop l).comp (measurable_histVec p.toPolicy l)
    convert h using 1
    ext ω
    simp only [Function.comp_apply, ofFn_histVec]
  exact hstop (measurableSet_singleton false)

private lemma hist_jobs_zero {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) :
    (π.hist ω 0).jobs = ∅ := rfl

private lemma hist_jobs_succ {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    (π.hist ω (k + 1)).jobs = insert (π.job ω k) (π.hist ω k).jobs := by
  simp [Policy.hist, Policy.job, History.jobs, Finset.union_comm]

private lemma hist_jobs_mono {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) {l k : ℕ} (h : l ≤ k) :
    (π.hist ω l).jobs ⊆ (π.hist ω k).jobs := by
  induction k with
  | zero =>
    obtain rfl : l = 0 := Nat.le_zero.mp h
    exact Finset.Subset.refl _
  | succ k ih =>
    rcases Nat.le_succ_iff.mp h with hlk | rfl
    · exact (ih hlk).trans (by rw [hist_jobs_succ]; exact Finset.subset_insert _ _)
    · exact Finset.Subset.refl _

private lemma job_mem_hist_jobs {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) {l k : ℕ} (h : l < k) :
    π.job ω l ∈ (π.hist ω k).jobs := by
  have h1 : π.job ω l ∈ (π.hist ω (l + 1)).jobs := by
    rw [hist_jobs_succ]; exact Finset.mem_insert_self _ _
  exact hist_jobs_mono π ω h h1

private lemma startTime_zero {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) :
    π.startTime ω 0 = 0 := rfl

private lemma completionTime_eq {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    π.completionTime ω k = π.startTime ω k + ω (π.job ω k) := by
  simp [Policy.completionTime, Policy.startTime, Policy.hist, Policy.job, History.elapsed]

private lemma startTime_nonneg_of_pos {n : ℕ} (π : Policy n) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (k : ℕ) : 0 ≤ π.startTime ω k := by
  induction k with
  | zero => simp [startTime_zero]
  | succ k ih =>
    change 0 ≤ π.completionTime ω k
    rw [completionTime_eq]
    linarith [hω (π.job ω k)]

private lemma completionTime_pos_of_pos {n : ℕ} (π : Policy n) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (k : ℕ) : 0 < π.completionTime ω k := by
  rw [completionTime_eq]
  linarith [startTime_nonneg_of_pos π ω hω k, hω (π.job ω k)]

private lemma hist_card_of_feasible {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)} {π : Policy n}
    (hπ : π.Feasible F B) (ω : Fin n → ℝ) {k : ℕ} (hk : k ≤ numRemaining B) :
    (B ∪ (π.hist ω k).jobs).card = B.card + k := by
  induction k with
  | zero => simp [hist_jobs_zero]
  | succ k ih =>
    have hk' : k < numRemaining B := Nat.lt_of_succ_le hk
    have hav := hπ ω k hk'
    have hnot : π.job ω k ∉ B ∪ (π.hist ω k).jobs := hav.1
    have hunion : B ∪ (π.hist ω (k + 1)).jobs = insert (π.job ω k) (B ∪ (π.hist ω k).jobs) := by
      rw [hist_jobs_succ, Finset.union_insert]
    rw [hunion, Finset.card_insert_of_notMem hnot, ih hk'.le]
    omega

private lemma hist_union_univ_of_feasible {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {π : Policy n} (hπ : π.Feasible F B) (ω : Fin n → ℝ) :
    B ∪ (π.hist ω (numRemaining B)).jobs = Finset.univ := by
  refine Finset.eq_univ_of_card _ ?_
  rw [hist_card_of_feasible hπ ω le_rfl, numRemaining, Fintype.card_fin]
  have : B.card ≤ n := by simpa using B.card_le_univ
  omega

private lemma hist_update_eq {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) {k : ℕ} {j : Fin n}
    (hj : j ∉ (π.hist ω k).jobs) (x : ℝ) :
    ∀ l ≤ k, π.hist (Function.update ω j x) l = π.hist ω l := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih =>
    intro hl
    have hlk : l < k := Nat.lt_of_succ_le hl
    have hprev := ih hlk.le
    have hne : π.next (π.hist ω l) ≠ j := fun heq => hj (heq ▸ job_mem_hist_jobs π ω hlk)
    simp only [Policy.hist, hprev]
    congr 2
    exact congrArg (Prod.mk _) (Function.update_of_ne hne x ω)

private lemma integrable_exp_start_mul_bound {n : ℕ} (F : JobFamily n) (π : Policy n) (k : ℕ)
    (g : (Fin n → ℝ) → ℝ) (hg_meas : AEStronglyMeasurable g (serviceLaw F))
    (C : ℝ) (hg_bound : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω => Real.exp (-F.γ * π.startTime ω k) * g ω) (serviceLaw F) := by
  have := serviceLaw_isProb F
  refine Integrable.mono' (integrable_const (max C 0)) ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      (measurable_startTime π k)).aestronglyMeasurable.mul hg_meas
  · filter_upwards [serviceLaw_pos_ae F] with ω hω
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-F.γ * π.startTime ω k) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos, startTime_nonneg_of_pos π ω hω k])
    calc Real.exp (-F.γ * π.startTime ω k) * ‖g ω‖
        ≤ 1 * C := mul_le_mul hexp (hg_bound ω) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
      _ ≤ max C 0 := le_max_left C 0

private lemma integrable_exp_comp_mul_bound {n : ℕ} (F : JobFamily n) (π : Policy n) (k : ℕ)
    (g : (Fin n → ℝ) → ℝ) (hg_meas : AEStronglyMeasurable g (serviceLaw F))
    (C : ℝ) (hg_bound : ∀ ω, ‖g ω‖ ≤ C) :
    Integrable (fun ω => Real.exp (-F.γ * π.completionTime ω k) * g ω) (serviceLaw F) :=
  integrable_exp_start_mul_bound F π (k + 1) g hg_meas C hg_bound

private lemma integral_step_exp {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (π : Policy n) (hπ : π.Feasible F B) (k : ℕ) (hk : k < numRemaining B)
    (E : (Fin n → ℝ) → Prop) [DecidablePred E]
    (hE_meas : MeasurableSet {ω | E ω})
    (hE_indep : ∀ ω j x, j ∉ (π.hist ω k).jobs → (E (Function.update ω j x) ↔ E ω))
    (val : Finset (Fin n) → Fin n → ℝ) :
    ∫ ω, (if E ω then Real.exp (-F.γ * π.completionTime ω k) *
          val (B ∪ (π.hist ω k).jobs) (π.job ω k) else 0) ∂serviceLaw F =
    ∫ ω, (if E ω then Real.exp (-F.γ * π.startTime ω k) *
          (phi F (π.job ω k) * val (B ∪ (π.hist ω k).jobs) (π.job ω k)) else 0) ∂serviceLaw F := by
  let C : ℝ := ∑ D : Finset (Fin n), ∑ j : Fin n, |val D j|
  have hval_bound : ∀ D j, |val D j| ≤ C := fun D j =>
    le_trans (Finset.single_le_sum (f := fun j => |val D j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun D => ∑ j : Fin n, |val D j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ D))
  have hL_eq : (fun ω => if E ω then Real.exp (-F.γ * π.completionTime ω k) *
      val (B ∪ (π.hist ω k).jobs) (π.job ω k) else 0) =
      (fun ω => ∑ j : Fin n,
        (if E ω ∧ π.job ω k = j then Real.exp (-F.γ * π.startTime ω k) *
          val (B ∪ (π.hist ω k).jobs) j else 0) * Real.exp (-F.γ * ω j)) := by
    ext ω
    rw [Finset.sum_eq_single (π.job ω k)]
    · by_cases hE : E ω
      · simp only [hE, true_and, ↓reduceIte, completionTime_eq]
        rw [mul_add, Real.exp_add]
        ring
      · simp [hE]
    · intro j _ hne
      simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR_eq : (fun ω => if E ω then Real.exp (-F.γ * π.startTime ω k) *
      (phi F (π.job ω k) * val (B ∪ (π.hist ω k).jobs) (π.job ω k)) else 0) =
      (fun ω => ∑ j : Fin n,
        (if E ω ∧ π.job ω k = j then Real.exp (-F.γ * π.startTime ω k) *
          val (B ∪ (π.hist ω k).jobs) j else 0) * phi F j) := by
    ext ω
    rw [Finset.sum_eq_single (π.job ω k)]
    · by_cases hE : E ω
      · simp only [hE, true_and, ↓reduceIte]
        ring
      · simp [hE]
    · intro j _ hne
      simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL_eq, hR_eq]
  have hintL : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun ω => (if E ω ∧ π.job ω k = j then Real.exp (-F.γ * π.startTime ω k) *
        val (B ∪ (π.hist ω k).jobs) j else 0) * Real.exp (-F.γ * ω j)) (serviceLaw F) := by
    intro j _
    have hfun : (fun ω => (if E ω ∧ π.job ω k = j then Real.exp (-F.γ * π.startTime ω k) *
        val (B ∪ (π.hist ω k).jobs) j else 0) * Real.exp (-F.γ * ω j)) =
        (fun ω => Real.exp (-F.γ * π.completionTime ω k) *
          (if E ω ∧ π.job ω k = j then val (B ∪ (π.hist ω k).jobs) j else 0)) := by
      ext ω
      by_cases h : E ω ∧ π.job ω k = j
      · simp only [h.1, h.2, and_self, ↓reduceIte, completionTime_eq]
        rw [mul_add, Real.exp_add]
        ring
      · simp [h]
    rw [hfun]
    refine integrable_exp_comp_mul_bound F π k _ ?_ C ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact Measurable.ite (hE_meas.inter ((measurable_job π k) (measurableSet_singleton j)))
        (measurable_jobs_comp π k fun D => val (B ∪ D) j) measurable_const
    · intro ω
      by_cases h : E ω ∧ π.job ω k = j
      · simp only [h.1, h.2, and_self, ↓reduceIte, Real.norm_eq_abs]; exact hval_bound _ _
      · simp only [h, ↓reduceIte, norm_zero]
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hintR : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun ω => (if E ω ∧ π.job ω k = j then Real.exp (-F.γ * π.startTime ω k) *
        val (B ∪ (π.hist ω k).jobs) j else 0) * phi F j) (serviceLaw F) := by
    intro j _
    have hfun : (fun ω => (if E ω ∧ π.job ω k = j then Real.exp (-F.γ * π.startTime ω k) *
        val (B ∪ (π.hist ω k).jobs) j else 0) * phi F j) =
        (fun ω => Real.exp (-F.γ * π.startTime ω k) *
          (if E ω ∧ π.job ω k = j then val (B ∪ (π.hist ω k).jobs) j * phi F j else 0)) := by
      ext ω
      by_cases h : E ω ∧ π.job ω k = j <;> simp [h, mul_assoc]
    rw [hfun]
    refine integrable_exp_start_mul_bound F π k _ ?_ (C * phi F j) ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact Measurable.ite (hE_meas.inter ((measurable_job π k) (measurableSet_singleton j)))
        ((measurable_jobs_comp π k fun D => val (B ∪ D) j).mul measurable_const) measurable_const
    · intro ω
      by_cases h : E ω ∧ π.job ω k = j
      · simp only [h.1, h.2, and_self, ↓reduceIte, norm_mul, Real.norm_eq_abs, abs_of_pos (phi_pos F j)]
        exact mul_le_mul_of_nonneg_right (hval_bound _ _) (phi_pos F j).le
      · simp only [h, ↓reduceIte, norm_zero]
        exact mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (phi_pos F j).le
  rw [integral_finsetSum _ hintL, integral_finsetSum _ hintR]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]
  refine integral_mul_exp_of_indep F j _ fun ω x => ?_
  by_cases h : π.job ω k = j
  · have hjnot : j ∉ (π.hist ω k).jobs := by
      have hav := (hπ ω k hk).1
      rw [h] at hav
      exact fun hm => hav (Finset.mem_union_right _ hm)
    have hhist : π.hist (Function.update ω j x) k = π.hist ω k :=
      hist_update_eq π ω hjnot x k le_rfl
    have hjob' : π.job (Function.update ω j x) k = j := by
      simp only [Policy.job, hhist]; exact h
    have hE' : E (Function.update ω j x) ↔ E ω := hE_indep ω j x hjnot
    simp only [h, hjob', hE', Policy.startTime, hhist]
  · have h' : π.job (Function.update ω j x) k ≠ j := by
      intro hupd
      have hjnot : j ∉ (π.hist (Function.update ω j x) k).jobs := by
        have hav := (hπ (Function.update ω j x) k hk).1
        rw [hupd] at hav
        exact fun hm => hav (Finset.mem_union_right _ hm)
      have hback := hist_update_eq π (Function.update ω j x) hjnot (ω j) k le_rfl
      rw [Function.update_idem, Function.update_eq_self] at hback
      apply h
      change π.next (π.hist ω k) = j
      rw [hback]
      exact hupd
    simp [h, h']

/-! ### Section 4: Acyclicity, `availSet`, `ListFeasible`, and static policies/stages -/

private lemma exists_available {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) : ∃ j : Fin n, IsAvailable F B j := by
  have hne : (Finset.univ \ B).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hB (Finset.eq_univ_of_forall fun i => hsub (Finset.mem_univ i))
  have : Std.Irrefl (Relation.TransGen F.prec) := ⟨F.prec_acyclic⟩
  have hwf : WellFounded (Relation.TransGen F.prec) :=
    Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen F.prec)
  obtain ⟨j, hj, hmin⟩ := hwf.has_min ((Finset.univ \ B : Finset (Fin n)) : Set (Fin n))
    (Finset.coe_nonempty.mpr hne)
  have hj' : j ∈ Finset.univ \ B := Finset.mem_coe.mp hj
  refine ⟨j, (Finset.mem_sdiff.mp hj').2, fun i hij => ?_⟩
  by_contra hiB
  exact hmin i (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiB⟩))
    (Relation.TransGen.single hij)

open Classical in
private noncomputable def availSet {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (IsAvailable F B)

private lemma mem_availSet {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) (j : Fin n) :
    j ∈ availSet F B ↔ IsAvailable F B j := by
  simp [availSet]

private lemma availSet_nonempty {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) : (availSet F B).Nonempty := by
  obtain ⟨j, hj⟩ := exists_available F B hB
  exact ⟨j, (mem_availSet F B j).mpr hj⟩

private lemma numRemaining_insert_lt {n : ℕ} {B : Finset (Fin n)} {j : Fin n} (hj : j ∉ B) :
    numRemaining (insert j B) < numRemaining B := by
  have hcard : B.card < n := by
    have : B ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr fun h => hj (h ▸ Finset.mem_univ j)
    simpa using Finset.card_lt_card this
  unfold numRemaining
  rw [Finset.card_insert_of_notMem hj]
  omega

private def ListFeasible {n : ℕ} (F : JobFamily n) : Finset (Fin n) → List (Fin n) → Prop
  | _, [] => True
  | B, j :: L => IsAvailable F B j ∧ ListFeasible F (insert j B) L

private lemma listFeasible_append {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L₁ L₂ : List (Fin n)) :
    ListFeasible F B (L₁ ++ L₂) ↔ ListFeasible F B L₁ ∧ ListFeasible F (B ∪ L₁.toFinset) L₂ := by
  induction L₁ generalizing B with
  | nil => simp [ListFeasible]
  | cons j L₁ ih =>
    simp only [List.cons_append, ListFeasible, List.toFinset_cons, Finset.union_insert]
    rw [ih (insert j B), Finset.insert_union, and_assoc]

private lemma listFeasible_disjoint {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L : List (Fin n)} (hL : ListFeasible F B L) : ∀ j ∈ L, j ∉ B := by
  induction L generalizing B with
  | nil => intro _ h; cases h
  | cons a L ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hjL
    · exact hL.1.1
    · exact fun hB => ih hL.2 j hjL (Finset.mem_insert_of_mem hB)

private lemma listFeasible_nodup {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L : List (Fin n)} (hL : ListFeasible F B L) : L.Nodup := by
  induction L generalizing B with
  | nil => exact List.nodup_nil
  | cons a L ih =>
    refine List.nodup_cons.mpr ⟨?_, ih hL.2⟩
    intro ha
    exact listFeasible_disjoint hL.2 a ha (Finset.mem_insert_self a B)

private lemma listFeasible_card_union {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L : List (Fin n)} (hL : ListFeasible F B L) :
    (B ∪ L.toFinset).card = B.card + L.length := by
  induction L generalizing B with
  | nil => simp
  | cons a L ih =>
    simp only [List.toFinset_cons, Finset.union_insert, List.length_cons]
    rw [← Finset.insert_union, ih hL.2, Finset.card_insert_of_notMem hL.1.1]
    omega

private lemma listFeasible_length_le {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L : List (Fin n)} (hL : ListFeasible F B L) : L.length ≤ numRemaining B := by
  have h1 := listFeasible_card_union hL
  have h2 : (B ∪ L.toFinset).card ≤ n := by simpa using (B ∪ L.toFinset).card_le_univ
  unfold numRemaining
  omega

private lemma listFeasible_union_univ {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L : List (Fin n)} (hL : ListFeasible F B L) (hlen : L.length = numRemaining B) :
    B ∪ L.toFinset = Finset.univ := by
  refine Finset.eq_univ_of_card _ ?_
  rw [listFeasible_card_union hL, hlen, numRemaining, Fintype.card_fin]
  have : B.card ≤ n := by simpa using B.card_le_univ
  omega

private lemma listFeasible_prefix {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L₁ L₂ : List (Fin n)} (hL : ListFeasible F B L₂) (hpre : L₁ <+: L₂) :
    ListFeasible F B L₁ := by
  obtain ⟨L₃, rfl⟩ := hpre
  exact ((listFeasible_append F B L₁ L₃).mp hL).1

private lemma listFeasible_pred_mem {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)}
    {L : List (Fin n)} (hL : ListFeasible F B L) :
    ∀ {y i : Fin n}, y ∈ L → F.prec i y → i ∈ B ∪ L.toFinset := by
  induction L generalizing B with
  | nil => intro _ _ h; cases h
  | cons a L ih =>
    intro y i hy hprec
    simp only [List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]
    rcases List.mem_cons.mp hy with rfl | hyL
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (hL.1.2 i hprec))
    · exact ih hL.2 hyL hprec

private lemma listFeasible_of_insert {n : ℕ} {F : JobFamily n} {B : Finset (Fin n)} {x : Fin n}
    {L : List (Fin n)} (hL : ListFeasible F (insert x B) L)
    (hprec : ∀ y ∈ L, ¬ F.prec x y) : ListFeasible F B L := by
  induction L generalizing B with
  | nil => trivial
  | cons y L ih =>
    refine ⟨⟨fun hyB => hL.1.1 (Finset.mem_insert_of_mem hyB), fun i hiy => ?_⟩, ?_⟩
    · have him := hL.1.2 i hiy
      rcases Finset.mem_insert.mp him with rfl | hiB
      · exact absurd hiy (hprec y (List.mem_cons_self))
      · exact hiB
    · have hL' : ListFeasible F (insert x (insert y B)) L := by
        rw [Finset.insert_comm]; exact hL.2
      exact ih hL' fun z hz => hprec z (List.mem_cons_of_mem y hz)

private lemma listFeasible_filter_downward {n : ℕ} {F : JobFamily n} {B S : Finset (Fin n)}
    {X : List (Fin n)} (hX : ListFeasible F B X)
    (hdown : ∀ y ∈ S, ∀ i, F.prec i y → i ∈ B ∪ S) :
    ListFeasible F B (X.filter fun i => decide (i ∈ S)) := by
  induction X generalizing B with
  | nil => trivial
  | cons x X ih =>
    have hdown' : ∀ y ∈ S, ∀ i, F.prec i y → i ∈ insert x B ∪ S := fun y hy i hi =>
      Finset.union_subset_union_left (Finset.subset_insert x B) (hdown y hy i hi)
    by_cases hxS : x ∈ S
    · simp only [List.filter_cons, decide_eq_true hxS, ↓reduceIte, ListFeasible]
      exact ⟨hX.1, ih hX.2 hdown'⟩
    · simp only [List.filter_cons, decide_eq_false hxS, Bool.false_eq_true, ↓reduceIte]
      refine listFeasible_of_insert (ih hX.2 hdown') fun y hy hxy => ?_
      have hyS : y ∈ S := by
        have := (List.mem_filter.mp hy).2
        simpa using this
      rcases Finset.mem_union.mp (hdown y hyS x hxy) with hxB | hxS'
      · exact hX.1.1 hxB
      · exact hxS hxS'

private lemma listFeasible_filter_compl {n : ℕ} {F : JobFamily n} {B S : Finset (Fin n)}
    {X : List (Fin n)} (hX : ListFeasible F B X) :
    ListFeasible F (B ∪ S) (X.filter fun i => !decide (i ∈ S)) := by
  induction X generalizing B with
  | nil => trivial
  | cons x X ih =>
    by_cases hxS : x ∈ S
    · simp only [List.filter_cons, decide_eq_true hxS, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hBS : insert x B ∪ S = B ∪ S := by
        ext i; simp only [Finset.mem_union, Finset.mem_insert]
        exact ⟨fun h => by rcases h with (rfl | hB) | hS; exact Or.inr hxS; exact Or.inl hB; exact Or.inr hS,
          fun h => by rcases h with hB | hS; exact Or.inl (Or.inr hB); exact Or.inr hS⟩
      rw [← hBS]
      exact ih hX.2
    · simp only [List.filter_cons, decide_eq_false hxS, Bool.not_false, ↓reduceIte, ListFeasible]
      refine ⟨⟨fun hx => ?_, fun i hi => Finset.mem_union_left _ (hX.1.2 i hi)⟩, ?_⟩
      · rcases Finset.mem_union.mp hx with hxB | hxS'
        · exact hX.1.1 hxB
        · exact hxS hxS'
      · have hBS : insert x (B ∪ S) = insert x B ∪ S := by rw [Finset.insert_union]
        rw [hBS]
        exact ih hX.2

private lemma measurable_of_history_jobs {n : ℕ} {α : Type*} [MeasurableSpace α]
    (g : List (Fin n) → α) (k : ℕ) :
    Measurable fun h : Fin k → Fin n × ℝ => g ((List.ofFn h).map Prod.fst) := by
  have heq : (fun h : Fin k → Fin n × ℝ => g ((List.ofFn h).map Prod.fst)) =
      (fun v : Fin k → Fin n => g (List.ofFn v)) ∘ (fun h : Fin k → Fin n × ℝ => fun i => (h i).1) := by
    ext h
    simp [List.map_ofFn, Function.comp_def]
  rw [heq]
  exact (measurable_of_finite_discrete _).comp
    (measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i))

private def markovPolicy {n : ℕ} (B : Finset (Fin n)) (choose : Finset (Fin n) → Fin n) :
    Policy n where
  next h := choose (B ∪ h.jobs)
  measurable_next k := measurable_of_history_jobs (fun l => choose (B ∪ l.toFinset)) k

private lemma markovPolicy_feasible {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (choose : Finset (Fin n) → Fin n)
    (hchoose : ∀ D : Finset (Fin n), D ≠ Finset.univ → IsAvailable F D (choose D)) :
    (markovPolicy B choose).Feasible F B := by
  intro ω k hk
  suffices ∀ m ≤ k, IsAvailable F (B ∪ ((markovPolicy B choose).hist ω m).jobs)
      ((markovPolicy B choose).job ω m) ∧
      (B ∪ ((markovPolicy B choose).hist ω m).jobs).card = B.card + m from (this k le_rfl).1
  intro m hm
  induction m with
  | zero =>
    have hcard : B.card < n := by unfold numRemaining at hk; omega
    have hne : B ≠ Finset.univ := fun h => by subst h; simp at hcard
    simpa [hist_jobs_zero, Policy.job, markovPolicy] using hchoose B hne
  | succ m ih =>
    have ⟨hav_m, hcard_m⟩ := ih (Nat.le_of_succ_le hm)
    have hcard_succ : (B ∪ ((markovPolicy B choose).hist ω (m + 1)).jobs).card =
        B.card + (m + 1) := by
      rw [hist_jobs_succ, Finset.union_insert, Finset.card_insert_of_notMem hav_m.1, hcard_m]
      omega
    have hlt : B.card + (m + 1) < n := by unfold numRemaining at hk; omega
    have hne : B ∪ ((markovPolicy B choose).hist ω (m + 1)).jobs ≠ Finset.univ := by
      intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hcard_succ; omega
    exact ⟨by simpa [Policy.job, markovPolicy] using hchoose _ hne, hcard_succ⟩

/-! ### Section 5: List functionals `listPhi`, `listReward`, `listTime`, `listNet`, and static stages -/

private noncomputable def listPhi {n : ℕ} (F : JobFamily n) : List (Fin n) → ℝ
  | [] => 1
  | j :: L => phi F j * listPhi F L

private noncomputable def listReward {n : ℕ} (F : JobFamily n) : List (Fin n) → ℝ
  | [] => 0
  | j :: L => jobA F j + phi F j * listReward F L

private noncomputable def listTime {n : ℕ} (F : JobFamily n) : List (Fin n) → ℝ
  | [] => 0
  | j :: L => jobC F j + phi F j * listTime F L

private noncomputable def listNet {n : ℕ} (F : JobFamily n) (lam : ℝ) : List (Fin n) → ℝ
  | [] => 0
  | j :: L => (jobA F j - lam * jobC F j) + phi F j * listNet F lam L

private lemma listPhi_pos {n : ℕ} (F : JobFamily n) (L : List (Fin n)) : 0 < listPhi F L := by
  induction L with
  | nil => exact zero_lt_one
  | cons j L ih => exact mul_pos (phi_pos F j) ih

private lemma listPhi_append {n : ℕ} (F : JobFamily n) (L₁ L₂ : List (Fin n)) :
    listPhi F (L₁ ++ L₂) = listPhi F L₁ * listPhi F L₂ := by
  induction L₁ with
  | nil => simp [listPhi]
  | cons j L₁ ih => simp [listPhi, ih, mul_assoc]

private lemma listPhi_perm {n : ℕ} (F : JobFamily n) {L₁ L₂ : List (Fin n)} (h : L₁.Perm L₂) :
    listPhi F L₁ = listPhi F L₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [listPhi, ih]
  | swap x y L => simp [listPhi]; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma listTime_eq {n : ℕ} (F : JobFamily n) (L : List (Fin n)) :
    listTime F L = F.γ⁻¹ * (1 - listPhi F L) := by
  induction L with
  | nil => simp [listTime, listPhi]
  | cons j L ih =>
    simp only [listTime, listPhi, jobC, ih]
    ring

private lemma listTime_pos {n : ℕ} (F : JobFamily n) {L : List (Fin n)} (hne : L ≠ []) :
    0 < listTime F L := by
  cases L with
  | nil => exact absurd rfl hne
  | cons j L =>
    simp only [listTime]
    have hnn : 0 ≤ listTime F L := by
      clear hne
      induction L with
      | nil => simp [listTime]
      | cons a L ih => exact add_nonneg (jobC_pos F a).le (mul_nonneg (phi_pos F a).le ih)
    linarith [jobC_pos F j, mul_nonneg (phi_pos F j).le hnn]

private lemma listNet_eq {n : ℕ} (F : JobFamily n) (lam : ℝ) (L : List (Fin n)) :
    listNet F lam L = listReward F L - lam * listTime F L := by
  induction L with
  | nil => simp [listNet, listReward, listTime]
  | cons j L ih =>
    simp only [listNet, listReward, listTime, ih]
    ring

private lemma listNet_append {n : ℕ} (F : JobFamily n) (lam : ℝ) (L₁ L₂ : List (Fin n)) :
    listNet F lam (L₁ ++ L₂) = listNet F lam L₁ + listPhi F L₁ * listNet F lam L₂ := by
  induction L₁ with
  | nil => simp [listNet, listPhi]
  | cons j L₁ ih =>
    simp only [List.cons_append, listNet, listPhi, ih]
    ring

private lemma listReward_append {n : ℕ} (F : JobFamily n) (L₁ L₂ : List (Fin n)) :
    listReward F (L₁ ++ L₂) = listReward F L₁ + listPhi F L₁ * listReward F L₂ := by
  induction L₁ with
  | nil => simp [listReward, listPhi]
  | cons j L₁ ih =>
    simp only [List.cons_append, listReward, listPhi, ih]
    ring

private lemma listTime_append {n : ℕ} (F : JobFamily n) (L₁ L₂ : List (Fin n)) :
    listTime F (L₁ ++ L₂) = listTime F L₁ + listPhi F L₁ * listTime F L₂ := by
  induction L₁ with
  | nil => simp [listTime, listPhi]
  | cons j L₁ ih =>
    simp only [List.cons_append, listTime, listPhi, ih]
    ring

private lemma listReward_sum {n : ℕ} (F : JobFamily n) (L : List (Fin n)) :
    listReward F L = ∑ k ∈ Finset.range L.length,
      if hk : k < L.length then listPhi F (L.take k) * jobA F L[k] else 0 := by
  induction L using List.reverseRecOn with
  | nil => simp [listReward]
  | append_singleton L x ih =>
    rw [listReward_append, ih,
      show Finset.range (L ++ [x]).length = Finset.range (L.length + 1) by simp,
      Finset.sum_range_succ]
    have hlt_last : L.length < (L ++ [x]).length := by simp
    simp only [listReward, mul_zero, add_zero, hlt_last, ↓reduceDIte,
      List.getElem_append_right (le_refl L.length), Nat.sub_self, List.getElem_cons_zero,
      List.take_left']
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < L.length := Finset.mem_range.mp hk
    have hk'' : k < (L ++ [x]).length := by simp; omega
    simp only [hk', hk'', ↓reduceDIte, List.take_append_of_le_length hk'.le,
      List.getElem_append_left hk']

private lemma listTime_sum {n : ℕ} (F : JobFamily n) (L : List (Fin n)) :
    listTime F L = ∑ k ∈ Finset.range L.length,
      if hk : k < L.length then listPhi F (L.take k) * jobC F L[k] else 0 := by
  induction L using List.reverseRecOn with
  | nil => simp [listTime]
  | append_singleton L x ih =>
    rw [listTime_append, ih,
      show Finset.range (L ++ [x]).length = Finset.range (L.length + 1) by simp,
      Finset.sum_range_succ]
    have hlt_last : L.length < (L ++ [x]).length := by simp
    simp only [listTime, mul_zero, add_zero, hlt_last, ↓reduceDIte,
      List.getElem_append_right (le_refl L.length), Nat.sub_self, List.getElem_cons_zero,
      List.take_left']
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < L.length := Finset.mem_range.mp hk
    have hk'' : k < (L ++ [x]).length := by simp; omega
    simp only [hk', hk'', ↓reduceDIte, List.take_append_of_le_length hk'.le,
      List.getElem_append_left hk']

open Classical in
private noncomputable def stageOfList {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hne : L ≠ []) : Stage n where
  next h :=
    if hk : h.length < L.length then L[h.length]
    else if hne' : (availSet F (B ∪ h.jobs)).Nonempty then hne'.choose
    else L.head hne
  measurable_next k := by
    let g : List (Fin n) → Fin n := fun l =>
      if hk : l.length < L.length then L[l.length]
      else if hne' : (availSet F (B ∪ l.toFinset)).Nonempty then hne'.choose
      else L.head hne
    have heq : (fun h : Fin k → Fin n × ℝ =>
        if hk : (List.ofFn h).length < L.length then L[(List.ofFn h).length]
        else if hne' : (availSet F (B ∪ History.jobs (List.ofFn h))).Nonempty then hne'.choose
        else L.head hne) =
      (fun h : Fin k → Fin n × ℝ => g ((List.ofFn h).map Prod.fst)) := by
      ext h
      simp [g, History.jobs]
    rw [heq]
    exact measurable_of_history_jobs g k
  stop h := decide (L.length ≤ h.length)
  measurable_stop k := by
    have : (fun h : Fin k → Fin n × ℝ => decide (L.length ≤ (List.ofFn h).length)) =
        fun _ => decide (L.length ≤ k) := by
      ext h; simp
    rw [this]
    exact measurable_const

private lemma stageOfList_next_nil {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hne : L ≠ []) :
    (stageOfList F B L hne).next [] = L.head hne := by
  have hpos : 0 < L.length := List.length_pos_iff.mpr hne
  simp [stageOfList, hpos, List.head_eq_getElem_zero]

private lemma stageOfList_hist_length {n : ℕ} (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    (π.hist ω k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Policy.hist, ih]

private lemma stageOfList_job {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hne : L ≠ []) (ω : Fin n → ℝ) {k : ℕ} (hk : k < L.length) :
    (stageOfList F B L hne).toPolicy.job ω k = L[k] := by
  have hlen := stageOfList_hist_length (stageOfList F B L hne).toPolicy ω k
  change (if h : ((stageOfList F B L hne).toPolicy.hist ω k).length < L.length then
    L[((stageOfList F B L hne).toPolicy.hist ω k).length] else _) = L[k]
  simp [hlen, hk]

private lemma stageOfList_hist_map {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hne : L ≠ []) (ω : Fin n → ℝ) :
    ∀ k ≤ L.length, ((stageOfList F B L hne).toPolicy.hist ω k).map Prod.fst = L.take k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hlt : k < L.length := Nat.lt_of_succ_le hk
    have hprev := ih hlt.le
    have hnext : (stageOfList F B L hne).toPolicy.next
        ((stageOfList F B L hne).toPolicy.hist ω k) = L[k] :=
      stageOfList_job F B L hne ω hlt
    simp only [Policy.hist, List.map_append, List.map_cons, List.map_nil, hprev, hnext]
    rw [List.take_succ_eq_append_getElem hlt]

private lemma stageOfList_inStage {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hL : ListFeasible F B L) (hne : L ≠ []) (ω : Fin n → ℝ) (k : ℕ) :
    (stageOfList F B L hne).InStage B ω k ↔ k < L.length := by
  unfold Stage.InStage
  have hle : L.length ≤ numRemaining B := listFeasible_length_le hL
  constructor
  · rintro ⟨_, hstop⟩
    by_contra hk
    push Not at hk
    have hmem : L.length ∈ Finset.Icc 1 k :=
      Finset.mem_Icc.mpr ⟨List.length_pos_iff.mpr hne, hk⟩
    have := hstop L.length hmem
    simp [stageOfList, stageOfList_hist_length] at this
  · intro hk
    refine ⟨lt_of_lt_of_le hk hle, fun l hl => ?_⟩
    have hlt : l < L.length := lt_of_le_of_lt (Finset.mem_Icc.mp hl).2 hk
    simp [stageOfList, stageOfList_hist_length, not_le.mpr hlt]

private lemma stageOfList_feasible {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hL : ListFeasible F B L) (hne : L ≠ []) :
    (stageOfList F B L hne).Feasible F B := by
  intro ω k hk
  suffices ∀ m ≤ k,
      IsAvailable F (B ∪ ((stageOfList F B L hne).toPolicy.hist ω m).jobs)
        ((stageOfList F B L hne).toPolicy.job ω m) ∧
      (B ∪ ((stageOfList F B L hne).toPolicy.hist ω m).jobs).card = B.card + m from
    (this k le_rfl).1
  intro m hm
  induction m with
  | zero =>
    have hpos : 0 < L.length := List.length_pos_iff.mpr hne
    have hjob : (stageOfList F B L hne).toPolicy.job ω 0 = L[0] :=
      stageOfList_job F B L hne ω hpos
    cases L with
    | nil => exact absurd rfl hne
    | cons j L' =>
      simpa [hist_jobs_zero, hjob] using hL.1
  | succ m ih =>
    have ⟨hav_m, hcard_m⟩ := ih (Nat.le_of_succ_le hm)
    have hcard_succ : (B ∪ ((stageOfList F B L hne).toPolicy.hist ω (m + 1)).jobs).card =
        B.card + (m + 1) := by
      rw [hist_jobs_succ, Finset.union_insert, Finset.card_insert_of_notMem hav_m.1, hcard_m]
      omega
    refine ⟨?_, hcard_succ⟩
    by_cases hml : m + 1 < L.length
    · have hmap := stageOfList_hist_map F B L hne ω (m + 1) hml.le
      have hjobs : ((stageOfList F B L hne).toPolicy.hist ω (m + 1)).jobs =
          (L.take (m + 1)).toFinset := by
        simp [History.jobs, hmap]
      rw [hjobs, stageOfList_job F B L hne ω hml]
      have hsplit : L = L.take (m + 1) ++ L[m + 1] :: L.drop (m + 2) := by
        rw [List.cons_getElem_drop_succ (h := hml), List.take_append_drop]
      have hL' := hL
      rw [hsplit, listFeasible_append] at hL'
      exact hL'.2.1
    · have hlen := stageOfList_hist_length (stageOfList F B L hne).toPolicy ω (m + 1)
      have hlt : B.card + (m + 1) < n := by unfold numRemaining at hk; omega
      have hne_univ : B ∪ ((stageOfList F B L hne).toPolicy.hist ω (m + 1)).jobs ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hcard_succ; omega
      have hne_av := availSet_nonempty F _ hne_univ
      have hjob : (stageOfList F B L hne).toPolicy.job ω (m + 1) = hne_av.choose := by
        change (if hk : ((stageOfList F B L hne).toPolicy.hist ω (m + 1)).length < L.length then _
          else if hne' : (availSet F (B ∪ ((stageOfList F B L hne).toPolicy.hist ω (m + 1)).jobs)).Nonempty
          then hne'.choose else _) = hne_av.choose
        simp [hlen, hml, hne_av]
      rw [hjob]
      exact (mem_availSet F _ _).mp hne_av.choose_spec

private lemma stageOfList_integral_exp_start {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hL : ListFeasible F B L) (hne : L ≠ []) :
    ∀ k ≤ L.length,
      ∫ ω, Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) ∂serviceLaw F =
        listPhi F (L.take k) := by
  have := serviceLaw_isProb F
  have hfeas := stageOfList_feasible F B L hL hne
  intro k
  induction k with
  | zero =>
    intro _
    simp [startTime_zero, listPhi]
  | succ k ih =>
    intro hk
    have hlt : k < L.length := Nat.lt_of_succ_le hk
    have hlt' : k < numRemaining B := lt_of_lt_of_le hlt (listFeasible_length_le hL)
    have hstep := integral_step_exp F B (stageOfList F B L hne).toPolicy hfeas k hlt'
      (fun _ => True) MeasurableSet.univ (fun _ _ _ _ => Iff.rfl) (fun _ _ => (1 : ℝ))
    simp only [↓reduceIte, mul_one] at hstep
    change ∫ ω, Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k) ∂serviceLaw F = _
    rw [hstep]
    have hfun : (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) *
        phi F ((stageOfList F B L hne).toPolicy.job ω k)) =
        (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) * phi F L[k]) := by
      ext ω; rw [stageOfList_job F B L hne ω hlt]
    rw [hfun, integral_mul_const, ih hlt.le, List.take_succ_eq_append_getElem hlt, listPhi_append]
    simp [listPhi]

private lemma stageOfList_reward {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hL : ListFeasible F B L) (hne : L ≠ []) :
    (stageOfList F B L hne).reward F B = listReward F L := by
  classical
  have hfeas := stageOfList_feasible F B L hL hne
  unfold Stage.reward
  have hint : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if (stageOfList F B L hne).InStage B ω k then
        F.reward ((stageOfList F B L hne).toPolicy.job ω k) *
          Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k)
      else 0) (serviceLaw F) := by
    intro k _
    have hfun : (fun ω => if (stageOfList F B L hne).InStage B ω k then
        F.reward ((stageOfList F B L hne).toPolicy.job ω k) *
          Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k)
      else 0) =
      (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k) *
        (if (stageOfList F B L hne).InStage B ω k then
          F.reward ((stageOfList F B L hne).toPolicy.job ω k) else 0)) := by
      ext ω; split_ifs <;> ring
    rw [hfun]
    refine integrable_exp_comp_mul_bound F _ k _ ?_ (∑ i : Fin n, F.reward i) ?_
    · exact (Measurable.ite (measurableSet_inStage B _ k)
        ((measurable_of_finite_discrete F.reward).comp (measurable_job _ k))
        measurable_const).aestronglyMeasurable
    · intro ω
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_pos (F.reward_pos _)]
        exact Finset.single_le_sum (f := F.reward) (fun i _ => (F.reward_pos i).le) (Finset.mem_univ _)
      · rw [norm_zero]; exact Finset.sum_nonneg fun i _ => (F.reward_pos i).le
  rw [integral_finsetSum _ hint]
  have hsub : Finset.range L.length ⊆ Finset.range (numRemaining B) :=
    Finset.range_mono (listFeasible_length_le hL)
  rw [← Finset.sum_subset hsub]
  · rw [listReward_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hlt : k < L.length := Finset.mem_range.mp hk
    have hlt' : k < numRemaining B := lt_of_lt_of_le hlt (listFeasible_length_le hL)
    simp only [hlt, ↓reduceDIte]
    have hstep := integral_step_exp F B (stageOfList F B L hne).toPolicy hfeas k hlt'
      (fun _ => True) MeasurableSet.univ (fun _ _ _ _ => Iff.rfl) (fun _ j => F.reward j)
    have hcongr : (fun ω => if (stageOfList F B L hne).InStage B ω k then
        F.reward ((stageOfList F B L hne).toPolicy.job ω k) *
          Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k) else 0) =
      (fun ω => if True then Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k) *
        F.reward ((stageOfList F B L hne).toPolicy.job ω k) else 0) := by
      ext ω
      simp only [stageOfList_inStage F B L hL hne ω k, hlt, ↓reduceIte, mul_comm]
    rw [hcongr, hstep]
    have hcongr2 : (fun ω => if True then
        Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) *
        (phi F ((stageOfList F B L hne).toPolicy.job ω k) *
          F.reward ((stageOfList F B L hne).toPolicy.job ω k)) else 0) =
      (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) * jobA F L[k]) := by
      ext ω
      simp only [↓reduceIte, stageOfList_job F B L hne ω hlt, jobA, mul_comm]
    rw [hcongr2, integral_mul_const, stageOfList_integral_exp_start F B L hL hne k hlt.le]
  · intro k _ hk
    have hnot : ¬ k < L.length := fun h => hk (Finset.mem_range.mpr h)
    simp [stageOfList_inStage F B L hL hne _ k, hnot]

private lemma stageOfList_time {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (L : List (Fin n)) (hL : ListFeasible F B L) (hne : L ≠ []) :
    (stageOfList F B L hne).time F B = listTime F L := by
  classical
  have hfeas := stageOfList_feasible F B L hL hne
  unfold Stage.time
  have hint : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if (stageOfList F B L hne).InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) -
          Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k))
      else 0) (serviceLaw F) := by
    intro k _
    have hfun : (fun ω => if (stageOfList F B L hne).InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) -
          Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k))
      else 0) =
      (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) *
        (if (stageOfList F B L hne).InStage B ω k then F.γ⁻¹ else 0) -
        Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k) *
        (if (stageOfList F B L hne).InStage B ω k then F.γ⁻¹ else 0)) := by
      ext ω; split_ifs <;> ring
    rw [hfun]
    refine Integrable.sub ?_ ?_
    · refine integrable_exp_start_mul_bound F _ k _ ?_ F.γ⁻¹ ?_
      · exact (Measurable.ite (measurableSet_inStage B _ k) measurable_const measurable_const).aestronglyMeasurable
      · intro ω; split_ifs
        · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
        · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
    · refine integrable_exp_comp_mul_bound F _ k _ ?_ F.γ⁻¹ ?_
      · exact (Measurable.ite (measurableSet_inStage B _ k) measurable_const measurable_const).aestronglyMeasurable
      · intro ω; split_ifs
        · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
        · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
  rw [integral_finsetSum _ hint]
  have hsub : Finset.range L.length ⊆ Finset.range (numRemaining B) :=
    Finset.range_mono (listFeasible_length_le hL)
  rw [← Finset.sum_subset hsub]
  · rw [listTime_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hlt : k < L.length := Finset.mem_range.mp hk
    have hlt' : k < numRemaining B := lt_of_lt_of_le hlt (listFeasible_length_le hL)
    simp only [hlt, ↓reduceDIte]
    have hcongr : (fun ω => if (stageOfList F B L hne).InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) -
          Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k)) else 0) =
      (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) * F.γ⁻¹ -
        Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.completionTime ω k) * F.γ⁻¹) := by
      ext ω
      simp only [stageOfList_inStage F B L hL hne ω k, hlt, ↓reduceIte]
      ring
    rw [hcongr, integral_sub
      (integrable_exp_start_mul_bound F _ k _ aestronglyMeasurable_const F.γ⁻¹ fun _ => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)])
      (integrable_exp_comp_mul_bound F _ k _ aestronglyMeasurable_const F.γ⁻¹ fun _ => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)])]
    have hstep := integral_step_exp F B (stageOfList F B L hne).toPolicy hfeas k hlt'
      (fun _ => True) MeasurableSet.univ (fun _ _ _ _ => Iff.rfl) (fun _ _ => F.γ⁻¹)
    simp only [↓reduceIte] at hstep
    rw [hstep]
    have hcongr2 : (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) *
        (phi F ((stageOfList F B L hne).toPolicy.job ω k) * F.γ⁻¹)) =
      (fun ω => Real.exp (-F.γ * (stageOfList F B L hne).toPolicy.startTime ω k) *
        (phi F L[k] * F.γ⁻¹)) := by
      ext ω; rw [stageOfList_job F B L hne ω hlt]
    rw [hcongr2, integral_mul_const, integral_mul_const,
      stageOfList_integral_exp_start F B L hL hne k hlt.le]
    unfold jobC
    ring
  · intro k _ hk
    have hnot : ¬ k < L.length := fun h => hk (Finset.mem_range.mpr h)
    simp [stageOfList_inStage F B L hL hne _ k, hnot]

/-! ### Section 6: The Interleaving Excess Identity (Combinatorial Core) -/

private noncomputable def interleaveExcess {n : ℕ} (F : JobFamily n) (lam : ℝ)
    (P : Fin n → Bool) (X : List (Fin n)) : ℝ :=
  listNet F lam X -
    listPhi F (X.filter fun i => !P i) * listNet F lam (X.filter P) -
    listPhi F (X.filter P) * listNet F lam (X.filter fun i => !P i)

private lemma listPhi_filter_mul {n : ℕ} (F : JobFamily n) (P : Fin n → Bool) (X : List (Fin n)) :
    listPhi F X = listPhi F (X.filter P) * listPhi F (X.filter fun i => !P i) := by
  induction X with
  | nil => simp [listPhi]
  | cons x X ih =>
    cases hx : P x <;> simp [hx, listPhi, ih] <;> ring

private lemma interleaveExcess_nil {n : ℕ} (F : JobFamily n) (lam : ℝ) (P : Fin n → Bool) :
    interleaveExcess F lam P [] = 0 := by
  simp [interleaveExcess, listNet, listPhi]

private lemma interleaveExcess_snoc_true {n : ℕ} (F : JobFamily n) (lam : ℝ) (P : Fin n → Bool)
    (X : List (Fin n)) (x : Fin n) (hx : P x = true) :
    interleaveExcess F lam P (X ++ [x]) =
      interleaveExcess F lam P X +
        (1 - phi F x) * listPhi F (X.filter P) * listNet F lam (X.filter fun i => !P i) := by
  unfold interleaveExcess
  simp only [List.filter_append, List.filter_cons, hx, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.append_nil]
  rw [listNet_append, listNet_append, listPhi_append, listPhi_filter_mul F P X]
  simp only [listNet, listPhi, mul_zero, add_zero, mul_one]
  ring

private lemma interleaveExcess_snoc_false {n : ℕ} (F : JobFamily n) (lam : ℝ) (P : Fin n → Bool)
    (X : List (Fin n)) (x : Fin n) (hx : P x = false) :
    interleaveExcess F lam P (X ++ [x]) =
      interleaveExcess F lam P X +
        (1 - phi F x) * listPhi F (X.filter fun i => !P i) * listNet F lam (X.filter P) := by
  unfold interleaveExcess
  simp only [List.filter_append, List.filter_cons, hx, Bool.not_false, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.append_nil]
  rw [listNet_append, listNet_append, listPhi_append, listPhi_filter_mul F P X]
  simp only [listNet, listPhi, mul_zero, add_zero, mul_one]
  ring

private lemma interleaveExcess_nonpos_and_eq {n : ℕ} (F : JobFamily n) (lam : ℝ)
    (P : Fin n → Bool) (X : List (Fin n))
    (hpreP : ∀ X_pre, X_pre <+: X → listNet F lam (X_pre.filter P) ≤ 0)
    (hpreN : ∀ X_pre, X_pre <+: X → listNet F lam (X_pre.filter fun i => !P i) ≤ 0) :
    interleaveExcess F lam P X ≤ 0 ∧
    (interleaveExcess F lam P X = 0 →
      ∀ X_pre x X_post, X = X_pre ++ x :: X_post → P x = true →
        listNet F lam (X_pre.filter fun i => !P i) = 0) := by
  induction X using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [interleaveExcess_nil], fun _ X_pre x X_post h => ?_⟩
    have := congrArg List.length h
    simp at this
  | append_singleton X y ih =>
    have hpreP' : ∀ X_pre, X_pre <+: X → listNet F lam (X_pre.filter P) ≤ 0 := fun X_pre h =>
      hpreP X_pre (h.trans (List.prefix_append X [y]))
    have hpreN' : ∀ X_pre, X_pre <+: X → listNet F lam (X_pre.filter fun i => !P i) ≤ 0 :=
      fun X_pre h => hpreN X_pre (h.trans (List.prefix_append X [y]))
    obtain ⟨ih_le, ih_eq⟩ := ih hpreP' hpreN'
    have h1my : 0 < 1 - phi F y := sub_pos.mpr (phi_lt_one F y)
    have hstep_le : interleaveExcess F lam P (X ++ [y]) ≤ interleaveExcess F lam P X := by
      cases hy : P y
      · rw [interleaveExcess_snoc_false F lam P X y hy]
        have hterm : (1 - phi F y) * listPhi F (X.filter fun i => !P i) *
            listNet F lam (X.filter P) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (mul_pos h1my (listPhi_pos F _)).le (hpreP' X List.prefix_rfl)
        linarith
      · rw [interleaveExcess_snoc_true F lam P X y hy]
        have hterm : (1 - phi F y) * listPhi F (X.filter P) *
            listNet F lam (X.filter fun i => !P i) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (mul_pos h1my (listPhi_pos F _)).le (hpreN' X List.prefix_rfl)
        linarith
    refine ⟨le_trans hstep_le ih_le, fun hzero X_pre x X_post hsplit hx => ?_⟩
    have hXzero : interleaveExcess F lam P X = 0 := le_antisymm ih_le (hzero ▸ hstep_le)
    cases X_post using List.reverseRecOn with
    | nil =>
      have hsplit' : X ++ [y] = X_pre ++ [x] := by simpa using hsplit
      have hlen : X.length = X_pre.length := by
        have := congrArg List.length hsplit'; simp at this; omega
      obtain ⟨hX, hyx⟩ := List.append_inj hsplit' hlen
      have hy : y = x := List.singleton_inj.mp hyx
      subst hy
      subst hX
      rw [interleaveExcess_snoc_true F lam P X y hx, hXzero, zero_add] at hzero
      have hpos : 0 < (1 - phi F y) * listPhi F (X.filter P) :=
        mul_pos (sub_pos.mpr (phi_lt_one F y)) (listPhi_pos F _)
      exact (mul_eq_zero.mp hzero).resolve_left hpos.ne'
    | append_singleton X_post' z =>
      have hsplit' : X ++ [y] = (X_pre ++ x :: X_post') ++ [z] := by
        simpa [List.append_assoc] using hsplit
      have hlen : X.length = (X_pre ++ x :: X_post').length := by
        have := congrArg List.length hsplit'
        simp only [List.length_append, List.length_singleton] at this ⊢
        omega
      obtain ⟨hXeq, _⟩ := List.append_inj hsplit' hlen
      exact ih_eq hXzero X_pre x X_post' hXeq hx

/-! ### Section 7: The two finite DPs `dpU` and `dpG` / `dpH` -/

private noncomputable def dpU {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) : ℝ :=
  if h : (availSet F B).Nonempty then
    (availSet F B).sup' h (fun j => jobA F j + phi F j * if hj : j ∉ B then dpU F (insert j B) else 0)
  else 0
termination_by numRemaining B
decreasing_by
  exact numRemaining_insert_lt hj

private lemma dpU_eq {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) :
    dpU F B = if h : (availSet F B).Nonempty then
      (availSet F B).sup' h (fun j => jobA F j + phi F j * dpU F (insert j B))
    else 0 := by
  rw [dpU]
  split_ifs with h
  · refine Finset.sup'_congr h rfl fun j hj => ?_
    simp [((mem_availSet F B j).mp hj).1]
  · rfl

private lemma dpU_univ {n : ℕ} (F : JobFamily n) : dpU F Finset.univ = 0 := by
  rw [dpU_eq]
  have h : ¬ (availSet F Finset.univ).Nonempty := by
    rintro ⟨j, hj⟩
    exact ((mem_availSet F Finset.univ j).mp hj).1 (Finset.mem_univ j)
  simp [h]

private lemma dpU_ge {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) (j : Fin n)
    (hj : IsAvailable F B j) :
    jobA F j + phi F j * dpU F (insert j B) ≤ dpU F B := by
  conv_rhs => rw [dpU_eq]
  have hmem : j ∈ availSet F B := (mem_availSet F B j).mpr hj
  have hne : (availSet F B).Nonempty := ⟨j, hmem⟩
  simp only [hne, ↓reduceDIte]
  exact Finset.le_sup' (fun i => jobA F i + phi F i * dpU F (insert i B)) hmem

private lemma dpU_exists_max {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) :
    ∃ j : Fin n, IsAvailable F B j ∧ dpU F B = jobA F j + phi F j * dpU F (insert j B) := by
  have hne := availSet_nonempty F B hB
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hne
    (fun i => jobA F i + phi F i * dpU F (insert i B))
  refine ⟨j, (mem_availSet F B j).mp hj, ?_⟩
  rw [dpU_eq]
  simp only [hne, ↓reduceDIte]
  exact hmax

private lemma listReward_le_dpU {n : ℕ} (F : JobFamily n) {B : Finset (Fin n)} {L : List (Fin n)}
    (hL : ListFeasible F B L) (hlen : L.length = numRemaining B) :
    listReward F L ≤ dpU F B := by
  induction L generalizing B with
  | nil =>
    have hB : B = Finset.univ := by
      have := listFeasible_union_univ hL hlen
      simpa using this
    subst hB
    simp [listReward, dpU_univ]
  | cons j L ih =>
    have hlen' : L.length = numRemaining (insert j B) := by
      unfold numRemaining at hlen ⊢
      rw [Finset.card_insert_of_notMem hL.1.1]
      simp only [List.length_cons] at hlen
      have : B.card < n := by
        have : B ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr fun h =>
          hL.1.1 (h ▸ Finset.mem_univ j)
        simpa using Finset.card_lt_card this
      omega
    calc listReward F (j :: L)
        = jobA F j + phi F j * listReward F L := rfl
      _ ≤ jobA F j + phi F j * dpU F (insert j B) := by
          gcongr
          · exact (phi_pos F j).le
          · exact ih hL.2 hlen'
      _ ≤ dpU F B := dpU_ge F B j hL.1

private lemma exists_complete_list_dpU {n : ℕ} (F : JobFamily n) :
    ∀ B : Finset (Fin n), ∃ L : List (Fin n),
      ListFeasible F B L ∧ L.length = numRemaining B ∧ listReward F L = dpU F B := by
  intro B
  induction hm : numRemaining B using Nat.strong_induction_on generalizing B with
  | h m ih =>
    by_cases hB : B = Finset.univ
    · subst hB
      refine ⟨[], trivial, ?_, ?_⟩
      · rw [← hm]; simp [numRemaining]
      · simp [listReward, dpU_univ]
    · obtain ⟨j, hj, hmax⟩ := dpU_exists_max F B hB
      have hlt : numRemaining (insert j B) < m := hm ▸ numRemaining_insert_lt hj.1
      obtain ⟨L, hL, hlen, hrew⟩ := ih (numRemaining (insert j B)) hlt (insert j B) rfl
      refine ⟨j :: L, ⟨hj, hL⟩, ?_, ?_⟩
      · rw [← hm]
        simp only [List.length_cons, hlen]
        unfold numRemaining
        rw [Finset.card_insert_of_notMem hj.1]
        have : B.card < n := by
          have : B ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr fun h =>
            hj.1 (h ▸ Finset.mem_univ j)
          simpa using Finset.card_lt_card this
        omega
      · simp only [listReward, hrew, hmax]

private lemma dpU_sub_payoff_eq {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (π : Policy n) (hπ : π.Feasible F A) :
    dpU F A - π.payoff F A =
      ∑ k ∈ Finset.range (numRemaining A),
        ∫ ω, Real.exp (-F.γ * π.startTime ω k) *
          (dpU F (A ∪ (π.hist ω k).jobs) -
            (jobA F (π.job ω k) +
              phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs))))
        ∂serviceLaw F := by
  have := serviceLaw_isProb F
  let M : ℝ := ∑ D : Finset (Fin n), |dpU F D|
  have hM : ∀ D, |dpU F D| ≤ M := fun D =>
    Finset.single_le_sum (f := fun D => |dpU F D|) (fun _ _ => abs_nonneg _) (Finset.mem_univ D)
  have hM_nn : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let T : ℕ → ℝ := fun k =>
    ∫ ω, Real.exp (-F.γ * π.startTime ω k) * dpU F (A ∪ (π.hist ω k).jobs) ∂serviceLaw F
  have hT0 : T 0 = dpU F A := by
    simp [T, startTime_zero, hist_jobs_zero]
  have hTm : T (numRemaining A) = 0 := by
    simp [T, hist_union_univ_of_feasible hπ, dpU_univ]
  have htele : dpU F A = ∑ k ∈ Finset.range (numRemaining A), (T k - T (k + 1)) := by
    rw [Finset.sum_range_sub' T (numRemaining A), hT0, hTm, sub_zero]
  have hint_payoff : ∀ k ∈ Finset.range (numRemaining A),
      Integrable (fun ω => F.reward (π.job ω k) * Real.exp (-F.γ * π.completionTime ω k))
        (serviceLaw F) := by
    intro k _
    have hfun : (fun ω => F.reward (π.job ω k) * Real.exp (-F.γ * π.completionTime ω k)) =
        (fun ω => Real.exp (-F.γ * π.completionTime ω k) * F.reward (π.job ω k)) := by
      ext ω; ring
    rw [hfun]
    refine integrable_exp_comp_mul_bound F π k _
      ((measurable_of_finite_discrete F.reward).comp (measurable_job π k)).aestronglyMeasurable
      (∑ i : Fin n, F.reward i) fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (F.reward_pos _)]
    exact Finset.single_le_sum (f := F.reward) (fun i _ => (F.reward_pos i).le) (Finset.mem_univ _)
  rw [htele, Policy.payoff, integral_finsetSum _ hint_payoff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < numRemaining A := Finset.mem_range.mp hk
  have hTk1 : T (k + 1) = ∫ ω, Real.exp (-F.γ * π.startTime ω k) *
      (phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs))) ∂serviceLaw F := by
    have hstep := integral_step_exp F A π hπ k hk' (fun _ => True) MeasurableSet.univ
      (fun _ _ _ _ => Iff.rfl) (fun D j => dpU F (insert j D))
    simp only [↓reduceIte] at hstep
    convert hstep using 2
    ext ω
    change Real.exp (-F.γ * π.completionTime ω k) * dpU F (A ∪ (π.hist ω (k + 1)).jobs) = _
    rw [hist_jobs_succ, Finset.union_insert]
  have hpayk : ∫ ω, F.reward (π.job ω k) * Real.exp (-F.γ * π.completionTime ω k) ∂serviceLaw F =
      ∫ ω, Real.exp (-F.γ * π.startTime ω k) * jobA F (π.job ω k) ∂serviceLaw F := by
    have hstep := integral_step_exp F A π hπ k hk' (fun _ => True) MeasurableSet.univ
      (fun _ _ _ _ => Iff.rfl) (fun _ j => F.reward j)
    simp only [↓reduceIte] at hstep
    have h1 : (fun ω => F.reward (π.job ω k) * Real.exp (-F.γ * π.completionTime ω k)) =
        (fun ω => Real.exp (-F.γ * π.completionTime ω k) * F.reward (π.job ω k)) := by
      ext ω; ring
    have h2 : (fun ω => Real.exp (-F.γ * π.startTime ω k) * (phi F (π.job ω k) * F.reward (π.job ω k))) =
        (fun ω => Real.exp (-F.γ * π.startTime ω k) * jobA F (π.job ω k)) := by
      ext ω; unfold jobA; ring
    rw [h1, hstep, h2]
  have hi1 : Integrable (fun ω => Real.exp (-F.γ * π.startTime ω k) *
      dpU F (A ∪ (π.hist ω k).jobs)) (serviceLaw F) :=
    integrable_exp_start_mul_bound F π k _
      (measurable_jobs_comp π k fun D => dpU F (A ∪ D)).aestronglyMeasurable M
      fun ω => by rw [Real.norm_eq_abs]; exact hM _
  have hi2 : Integrable (fun ω => Real.exp (-F.γ * π.startTime ω k) *
      (phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs)))) (serviceLaw F) := by
    refine integrable_exp_start_mul_bound F π k _ ?_ M fun ω => ?_
    · refine ((measurable_of_finite_discrete (phi F)).comp (measurable_job π k) |>.mul ?_).aestronglyMeasurable
      have h1 : Measurable fun ω => (π.job ω k, fun i : Fin k => (histVec π ω k i).1) :=
        (measurable_job π k).prodMk
          (measurable_pi_lambda _ fun i =>
            measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histVec π k)))
      have heq : (fun ω => dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs))) =
          (fun p : Fin n × (Fin k → Fin n) => dpU F (insert p.1 (A ∪ (List.ofFn p.2).toFinset))) ∘
            (fun ω => (π.job ω k, fun i : Fin k => (histVec π ω k i).1)) := by
        ext ω
        simp [Function.comp_def, History.jobs, ← ofFn_histVec π ω k, List.map_ofFn]
      rw [heq]
      exact (measurable_of_finite_discrete _).comp h1
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (phi_pos F _)]
      calc phi F (π.job ω k) * |dpU F _|
          ≤ 1 * M := mul_le_mul (phi_lt_one F _).le (hM _) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
  have hi3 : Integrable (fun ω => Real.exp (-F.γ * π.startTime ω k) *
      jobA F (π.job ω k)) (serviceLaw F) :=
    integrable_exp_start_mul_bound F π k _
      ((measurable_of_finite_discrete (jobA F)).comp (measurable_job π k)).aestronglyMeasurable
      (∑ i : Fin n, jobA F i) fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (jobA_pos F _)]
        exact Finset.single_le_sum (f := jobA F) (fun i _ => (jobA_pos F i).le) (Finset.mem_univ _)
  have hi12 : Integrable (fun ω => Real.exp (-F.γ * π.startTime ω k) *
      dpU F (A ∪ (π.hist ω k).jobs) -
      Real.exp (-F.γ * π.startTime ω k) *
        (phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs)))) (serviceLaw F) :=
    hi1.sub hi2
  change (T k - T (k + 1)) - _ = _
  rw [hTk1, hpayk, ← integral_sub hi1 hi2, ← integral_sub hi12 hi3]
  congr 1
  ext ω
  ring

private lemma exists_optimal_dpU_policy {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (hA : A ≠ Finset.univ) :
    ∃ g : Policy n, g.Feasible F A ∧ g.payoff F A = dpU F A := by
  classical
  obtain ⟨j_def, _⟩ := exists_available F A hA
  let choose : Finset (Fin n) → Fin n := fun D =>
    if hD : D ≠ Finset.univ then (dpU_exists_max F D hD).choose else j_def
  let g := markovPolicy A choose
  have hg_feas : g.Feasible F A := markovPolicy_feasible F A choose fun D hD => by
    dsimp only [choose]
    rw [dif_pos hD]
    exact (dpU_exists_max F D hD).choose_spec.1
  refine ⟨g, hg_feas, ?_⟩
  have hsub := dpU_sub_payoff_eq F A g hg_feas
  have hzero : ∑ k ∈ Finset.range (numRemaining A),
      ∫ ω, Real.exp (-F.γ * g.startTime ω k) *
        (dpU F (A ∪ (g.hist ω k).jobs) -
          (jobA F (g.job ω k) +
            phi F (g.job ω k) * dpU F (insert (g.job ω k) (A ∪ (g.hist ω k).jobs))))
      ∂serviceLaw F = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < numRemaining A := Finset.mem_range.mp hk
    have hfun : (fun ω => Real.exp (-F.γ * g.startTime ω k) *
        (dpU F (A ∪ (g.hist ω k).jobs) -
          (jobA F (g.job ω k) +
            phi F (g.job ω k) * dpU F (insert (g.job ω k) (A ∪ (g.hist ω k).jobs))))) =
        fun _ => 0 := by
      ext ω
      have hcard := hist_card_of_feasible hg_feas ω hk'.le
      have hne : A ∪ (g.hist ω k).jobs ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hcard
        unfold numRemaining at hk'; omega
      have hjob : g.job ω k = (dpU_exists_max F (A ∪ (g.hist ω k).jobs) hne).choose := by
        change choose (A ∪ (g.hist ω k).jobs) = _
        dsimp only [choose]
        rw [dif_pos hne]
      have hmax := (dpU_exists_max F (A ∪ (g.hist ω k).jobs) hne).choose_spec.2
      rw [hjob, ← hmax, sub_self, mul_zero]
    rw [hfun, integral_zero]
  linarith

private lemma optimal_u_greedy_ae {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (π : Policy n) (hπ : IsOptimalPolicy F A π) :
    ∀ᵐ ω ∂serviceLaw F, ∀ k < numRemaining A,
      dpU F (A ∪ (π.hist ω k).jobs) =
        jobA F (π.job ω k) +
          phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs)) := by
  by_cases hA : A = Finset.univ
  · subst hA
    filter_upwards with ω k hk
    simp [numRemaining] at hk
  · obtain ⟨g, hg_feas, hg_pay⟩ := exists_optimal_dpU_policy F A hA
    have hopt : dpU F A ≤ π.payoff F A := hg_pay ▸ hπ.2 g hg_feas
    have hsub := dpU_sub_payoff_eq F A π hπ.1
    let gap : ℕ → (Fin n → ℝ) → ℝ := fun k ω =>
      Real.exp (-F.γ * π.startTime ω k) *
        (dpU F (A ∪ (π.hist ω k).jobs) -
          (jobA F (π.job ω k) +
            phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs))))
    have hnn : ∀ k < numRemaining A, ∀ ω, 0 ≤ gap k ω := by
      intro k hk ω
      refine mul_nonneg (Real.exp_pos _).le ?_
      exact sub_nonneg.mpr (dpU_ge F _ _ (hπ.1 ω k hk))
    have hsum_nn : ∀ k ∈ Finset.range (numRemaining A), 0 ≤ ∫ ω, gap k ω ∂serviceLaw F := by
      intro k hk
      exact integral_nonneg (hnn k (Finset.mem_range.mp hk))
    have hsum_zero : ∑ k ∈ Finset.range (numRemaining A), ∫ ω, gap k ω ∂serviceLaw F = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hsum_nn)
    have hterm_zero : ∀ k ∈ Finset.range (numRemaining A), ∫ ω, gap k ω ∂serviceLaw F = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hsum_nn).mp hsum_zero
    have hae_k : ∀ k ∈ Finset.range (numRemaining A), ∀ᵐ ω ∂serviceLaw F, gap k ω = 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      let M : ℝ := ∑ D : Finset (Fin n), |dpU F D|
      have hM : ∀ D, |dpU F D| ≤ M := fun D =>
        Finset.single_le_sum (f := fun D => |dpU F D|) (fun _ _ => abs_nonneg _) (Finset.mem_univ D)
      have hint : Integrable (gap k) (serviceLaw F) := by
        refine integrable_exp_start_mul_bound F π k _ ?_
          (M + (∑ i : Fin n, jobA F i) + M) fun ω => ?_
        · have h1 : Measurable fun ω => (π.job ω k, fun i : Fin k => (histVec π ω k i).1) :=
            (measurable_job π k).prodMk
              (measurable_pi_lambda _ fun i =>
                measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histVec π k)))
          have heq : (fun ω => dpU F (A ∪ (π.hist ω k).jobs) -
              (jobA F (π.job ω k) +
                phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs)))) =
              (fun p : Fin n × (Fin k → Fin n) =>
                dpU F (A ∪ (List.ofFn p.2).toFinset) -
                  (jobA F p.1 + phi F p.1 * dpU F (insert p.1 (A ∪ (List.ofFn p.2).toFinset)))) ∘
                (fun ω => (π.job ω k, fun i : Fin k => (histVec π ω k i).1)) := by
            ext ω
            simp [Function.comp_def, History.jobs, ← ofFn_histVec π ω k, List.map_ofFn]
          rw [heq]
          exact ((measurable_of_finite_discrete _).comp h1).aestronglyMeasurable
        · rw [Real.norm_eq_abs]
          have h1 : |dpU F (A ∪ (π.hist ω k).jobs)| ≤ M := hM _
          have h2 : |jobA F (π.job ω k)| ≤ ∑ i : Fin n, jobA F i := by
            rw [abs_of_pos (jobA_pos F _)]
            exact Finset.single_le_sum (f := jobA F) (fun i _ => (jobA_pos F i).le) (Finset.mem_univ _)
          have h3 : |phi F (π.job ω k) * dpU F (insert (π.job ω k) (A ∪ (π.hist ω k).jobs))| ≤ M := by
            rw [abs_mul, abs_of_pos (phi_pos F _)]
            calc phi F (π.job ω k) * |dpU F _|
                ≤ 1 * M := mul_le_mul (phi_lt_one F _).le (hM _) (abs_nonneg _) zero_le_one
              _ = M := one_mul M
          calc |dpU F _ - (jobA F _ + phi F _ * dpU F _)|
              ≤ |dpU F _| + |jobA F _ + phi F _ * dpU F _| := abs_sub _ _
            _ ≤ |dpU F _| + (|jobA F _| + |phi F _ * dpU F _|) := by gcongr; exact abs_add_le _ _
            _ ≤ M + ((∑ i : Fin n, jobA F i) + M) := by linarith
            _ = M + (∑ i : Fin n, jobA F i) + M := by ring
      exact (integral_eq_zero_iff_of_nonneg (hnn k hk') hint).mp (hterm_zero k hk)
    have hae_all : ∀ᵐ ω ∂serviceLaw F, ∀ k ∈ Finset.range (numRemaining A), gap k ω = 0 :=
      (ae_ball_iff (Finset.countable_toSet _)).mpr hae_k
    filter_upwards [hae_all] with ω hω k hk
    have hg0 := hω k (Finset.mem_range.mpr hk)
    have hzero := (mul_eq_zero.mp hg0).resolve_left (Real.exp_pos _).ne'
    linarith

/-! ### Section 8: Stage DP `dpG` / `dpH` and identification of `familyIndex` -/

private noncomputable def dpG {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) : ℝ :=
  if h : (availSet F B).Nonempty then
    max 0 ((availSet F B).sup' h
      (fun j => jobA F j - lam * jobC F j + phi F j * if hj : j ∉ B then dpG F lam (insert j B) else 0))
  else 0
termination_by numRemaining B
decreasing_by
  exact numRemaining_insert_lt hj

private lemma dpG_eq {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) :
    dpG F lam B = if h : (availSet F B).Nonempty then
      max 0 ((availSet F B).sup' h
        (fun j => jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B)))
    else 0 := by
  rw [dpG]
  split_ifs with h
  · congr 1
    refine Finset.sup'_congr h rfl fun j hj => ?_
    simp [((mem_availSet F B j).mp hj).1]
  · rfl

private noncomputable def dpH {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) : ℝ :=
  if h : (availSet F B).Nonempty then
    (availSet F B).sup' h
      (fun j => jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B))
  else 0

private lemma dpG_nonneg {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) :
    0 ≤ dpG F lam B := by
  rw [dpG_eq]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

private lemma dpG_eq_max {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) :
    dpG F lam B = max 0 (dpH F lam B) := by
  rw [dpG_eq, dpH]
  split_ifs
  · rfl
  · simp

private lemma dpH_le_dpG {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) :
    dpH F lam B ≤ dpG F lam B := by
  rw [dpG_eq_max]; exact le_max_right _ _

private lemma dpH_ge {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n)) (j : Fin n)
    (hj : IsAvailable F B j) :
    jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B) ≤ dpH F lam B := by
  rw [dpH]
  have hmem : j ∈ availSet F B := (mem_availSet F B j).mpr hj
  have hne : (availSet F B).Nonempty := ⟨j, hmem⟩
  simp only [hne, ↓reduceDIte]
  exact Finset.le_sup' (fun i => jobA F i - lam * jobC F i + phi F i * dpG F lam (insert i B)) hmem

private lemma dpH_exists_max {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) :
    ∃ j : Fin n, IsAvailable F B j ∧
      dpH F lam B = jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B) := by
  have hne := availSet_nonempty F B hB
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hne
    (fun i => jobA F i - lam * jobC F i + phi F i * dpG F lam (insert i B))
  refine ⟨j, (mem_availSet F B j).mp hj, ?_⟩
  rw [dpH]
  simp only [hne, ↓reduceDIte]
  exact hmax

private lemma continuous_finset_sup' {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => s.sup' hs (fun i => f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a (Finset.mem_singleton_self a)
  | cons a t ha ht ih =>
    have heq : (fun x => (t.cons a ha).sup' ⟨a, Finset.mem_cons_self a t⟩ (fun i => f i x)) =
        (fun x => max (f a x) (t.sup' ht (fun i => f i x))) := by
      ext x; exact Finset.sup'_cons (H := ht) (f := fun i => f i x)
    rw [heq]
    exact (hf a (Finset.mem_cons_self a t)).max
      (ih fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))

private lemma dpG_continuous {n : ℕ} (F : JobFamily n) :
    ∀ B : Finset (Fin n), Continuous (fun lam => dpG F lam B) := by
  intro B
  induction hm : numRemaining B using Nat.strong_induction_on generalizing B with
  | h m ih =>
    have heq : (fun lam => dpG F lam B) =
        fun lam => if h : (availSet F B).Nonempty then
          max 0 ((availSet F B).sup' h
            (fun j => jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B)))
        else 0 := by
      ext lam; rw [dpG_eq]
    rw [heq]
    by_cases hne : (availSet F B).Nonempty
    · simp only [hne, ↓reduceDIte]
      refine continuous_const.max ?_
      refine continuous_finset_sup' hne
        (fun j lam => jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B)) fun j hj => ?_
      have hlt : numRemaining (insert j B) < m :=
        hm ▸ numRemaining_insert_lt ((mem_availSet F B j).mp hj).1
      exact (continuous_const.sub (continuous_id.mul continuous_const)).add
        (continuous_const.mul (ih _ hlt (insert j B) rfl))
    · simp only [hne, ↓reduceDIte]
      exact continuous_const

private lemma dpH_continuous {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) :
    Continuous (fun lam => dpH F lam B) := by
  unfold dpH
  by_cases hne : (availSet F B).Nonempty
  · simp only [hne, ↓reduceDIte]
    refine continuous_finset_sup' hne
      (fun j lam => jobA F j - lam * jobC F j + phi F j * dpG F lam (insert j B)) fun j _ => ?_
    exact (continuous_const.sub (continuous_id.mul continuous_const)).add
      (continuous_const.mul (dpG_continuous F (insert j B)))
  · simp only [hne, ↓reduceDIte]
    exact continuous_const

private lemma dpH_zero_pos {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) : 0 < dpH F 0 B := by
  obtain ⟨j, hj⟩ := exists_available F B hB
  have hge := dpH_ge F 0 B j hj
  simp only [zero_mul, sub_zero] at hge
  linarith [jobA_pos F j, mul_nonneg (phi_pos F j).le (dpG_nonneg F 0 (insert j B))]

private lemma dpG_zero_of_large {n : ℕ} (F : JobFamily n) (M : ℝ)
    (hM : ∀ i : Fin n, jobA F i ≤ M * jobC F i) :
    ∀ B : Finset (Fin n), dpH F M B ≤ 0 ∧ dpG F M B = 0 := by
  intro B
  induction hm : numRemaining B using Nat.strong_induction_on generalizing B with
  | h m ih =>
    by_cases hne : (availSet F B).Nonempty
    · have hH : dpH F M B ≤ 0 := by
        rw [dpH]
        simp only [hne, ↓reduceDIte]
        refine Finset.sup'_le hne _ fun j hj => ?_
        have hlt : numRemaining (insert j B) < m :=
          hm ▸ numRemaining_insert_lt ((mem_availSet F B j).mp hj).1
        rw [(ih _ hlt (insert j B) rfl).2, mul_zero, add_zero]
        linarith [hM j]
      refine ⟨hH, ?_⟩
      rw [dpG_eq_max]
      exact max_eq_left hH
    · have hH : dpH F M B = 0 := by rw [dpH]; simp [hne]
      refine ⟨hH.le, ?_⟩
      rw [dpG_eq_max, hH]
      simp

private lemma exists_dpH_root {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) : ∃ lam : ℝ, dpH F lam B = 0 := by
  obtain ⟨j0, _⟩ := exists_available F B hB
  let M : ℝ := ∑ i : Fin n, jobA F i / jobC F i
  have hM_nn : 0 ≤ M :=
    Finset.sum_nonneg fun i _ => (div_pos (jobA_pos F i) (jobC_pos F i)).le
  have hM : ∀ i : Fin n, jobA F i ≤ M * jobC F i := fun i => by
    have hle : jobA F i / jobC F i ≤ M :=
      Finset.single_le_sum (f := fun r => jobA F r / jobC F r)
        (fun r _ => (div_pos (jobA_pos F r) (jobC_pos F r)).le) (Finset.mem_univ i)
    exact (div_le_iff₀ (jobC_pos F i)).mp hle
  have h0 : 0 < dpH F 0 B := dpH_zero_pos F B hB
  have h1 : dpH F M B ≤ 0 := (dpG_zero_of_large F M hM B).1
  have hmem : (0 : ℝ) ∈ Set.Icc (dpH F M B) (dpH F 0 B) := ⟨h1, h0.le⟩
  obtain ⟨lam, _, hlam⟩ := intermediate_value_Icc' hM_nn (dpH_continuous F B).continuousOn hmem
  exact ⟨lam, hlam⟩

private lemma exists_list_dpH {n : ℕ} (F : JobFamily n) (lam : ℝ) :
    ∀ B : Finset (Fin n), B ≠ Finset.univ →
      ∃ L : List (Fin n), L ≠ [] ∧ ListFeasible F B L ∧ listNet F lam L = dpH F lam B := by
  intro B
  induction hm : numRemaining B using Nat.strong_induction_on generalizing B with
  | h m ih =>
    intro hB
    obtain ⟨j, hj, hmax⟩ := dpH_exists_max F lam B hB
    by_cases hG : dpG F lam (insert j B) = 0
    · refine ⟨[j], List.cons_ne_nil _ _, ⟨hj, trivial⟩, ?_⟩
      simp [listNet, hmax, hG]
    · have hGpos : 0 < dpG F lam (insert j B) :=
        lt_of_le_of_ne (dpG_nonneg F lam (insert j B)) (Ne.symm hG)
      have hne_ins : insert j B ≠ Finset.univ := by
        intro h
        rw [h, dpG_eq_max, dpH] at hGpos
        have hempty : ¬ (availSet F Finset.univ).Nonempty := by
          rintro ⟨i, hi⟩
          exact ((mem_availSet F Finset.univ i).mp hi).1 (Finset.mem_univ i)
        simp [hempty] at hGpos
      have hGeq : dpG F lam (insert j B) = dpH F lam (insert j B) := by
        rw [dpG_eq_max] at hGpos ⊢
        exact max_eq_right (by by_contra h; push Not at h; rw [max_eq_left h.le] at hGpos; exact lt_irrefl 0 hGpos)
      have hlt : numRemaining (insert j B) < m := hm ▸ numRemaining_insert_lt hj.1
      obtain ⟨L', _, hL', hnet'⟩ := ih _ hlt (insert j B) rfl hne_ins
      refine ⟨j :: L', List.cons_ne_nil _ _, ⟨hj, hL'⟩, ?_⟩
      simp [listNet, hnet', ← hGeq, hmax]

private lemma stage_time_pos {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) (p : Stage n) (hp : p.Feasible F B) :
    0 < p.time F B := by
  classical
  have hrem_pos : 0 < numRemaining B := by
    have : B ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hB
    have hlt : B.card < n := by simpa using Finset.card_lt_card this
    unfold numRemaining; omega
  unfold Stage.time
  have hint : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k))
      else 0) (serviceLaw F) := by
    intro k _
    have hfun : (fun ω => if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k))
      else 0) =
      (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (if p.InStage B ω k then F.γ⁻¹ else 0) -
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        (if p.InStage B ω k then F.γ⁻¹ else 0)) := by
      ext ω; split_ifs <;> ring
    rw [hfun]
    refine Integrable.sub ?_ ?_
    · refine integrable_exp_start_mul_bound F p.toPolicy k _
        (Measurable.ite (measurableSet_inStage B p k) measurable_const measurable_const).aestronglyMeasurable
        F.γ⁻¹ fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
          · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
    · refine integrable_exp_comp_mul_bound F p.toPolicy k _
        (Measurable.ite (measurableSet_inStage B p k) measurable_const measurable_const).aestronglyMeasurable
        F.γ⁻¹ fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
          · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
  rw [integral_finsetSum _ hint]
  have hterm_nn : ∀ k ∈ Finset.range (numRemaining B),
      0 ≤ ∫ ω, (if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k))
      else 0) ∂serviceLaw F := by
    intro k _
    refine integral_nonneg_of_ae ?_
    filter_upwards [serviceLaw_pos_ae F] with ω hω
    split_ifs
    · refine mul_nonneg (inv_pos.mpr F.γ_pos).le ?_
      rw [sub_nonneg, Real.exp_le_exp, completionTime_eq]
      nlinarith [F.γ_pos, hω (p.toPolicy.job ω k)]
    · exact le_rfl
  have h0_mem : 0 ∈ Finset.range (numRemaining B) := Finset.mem_range.mpr hrem_pos
  have h0_pos : 0 < ∫ ω, (if p.InStage B ω 0 then
      F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω 0) -
        Real.exp (-F.γ * p.toPolicy.completionTime ω 0))
    else 0) ∂serviceLaw F := by
    have := serviceLaw_isProb F
    have hfun : (fun ω => if p.InStage B ω 0 then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω 0) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω 0))
      else 0) =
      (fun ω => F.γ⁻¹ - Real.exp (-F.γ * p.toPolicy.completionTime ω 0) * F.γ⁻¹) := by
      ext ω
      have hin : p.InStage B ω 0 := ⟨hrem_pos, fun l hl => by
        have := Finset.mem_Icc.mp hl; omega⟩
      simp only [hin, ↓reduceIte, startTime_zero, mul_zero, Real.exp_zero]
      ring
    rw [hfun, integral_sub (integrable_const _)
      (integrable_exp_comp_mul_bound F p.toPolicy 0 _ aestronglyMeasurable_const F.γ⁻¹ fun _ => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)])]
    have hstep := integral_step_exp F B p.toPolicy hp 0 hrem_pos
      (fun _ => True) MeasurableSet.univ (fun _ _ _ _ => Iff.rfl) (fun _ _ => F.γ⁻¹)
    simp only [↓reduceIte, startTime_zero, mul_zero, Real.exp_zero, one_mul] at hstep
    rw [hstep]
    have hjob0 : ∀ ω, p.toPolicy.job ω 0 = p.next [] := fun _ => rfl
    simp only [hjob0, integral_const, probReal_univ, one_smul]
    have : F.γ⁻¹ - phi F (p.next []) * F.γ⁻¹ = jobC F (p.next []) := by unfold jobC; ring
    rw [this]
    exact jobC_pos F _
  exact lt_of_lt_of_le h0_pos (Finset.single_le_sum hterm_nn h0_mem)

private lemma stage_net_le_dpH {n : ℕ} (F : JobFamily n) (lam : ℝ) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) (p : Stage n) (hp : p.Feasible F B) :
    p.reward F B - lam * p.time F B ≤ dpH F lam B := by
  classical
  have := serviceLaw_isProb F
  have hrem_pos : 0 < numRemaining B := by
    have : B ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hB
    have hlt : B.card < n := by simpa using Finset.card_lt_card this
    unfold numRemaining; omega
  let M : ℝ := ∑ D : Finset (Fin n), |dpG F lam D|
  have hM : ∀ D, |dpG F lam D| ≤ M := fun D =>
    Finset.single_le_sum (f := fun D => |dpG F lam D|) (fun _ _ => abs_nonneg _) (Finset.mem_univ D)
  have hM_nn : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hInStage_indep : ∀ (k : ℕ) (ω : Fin n → ℝ) (j : Fin n) (x : ℝ),
      j ∉ (p.toPolicy.hist ω k).jobs →
      (p.InStage B (Function.update ω j x) k ↔ p.InStage B ω k) := by
    intro k ω j x hj
    unfold Stage.InStage
    refine and_congr Iff.rfl (forall₂_congr fun l hl => ?_)
    rw [hist_update_eq p.toPolicy ω hj x l (Finset.mem_Icc.mp hl).2]
  have hInStage_anti : ∀ ω k, p.InStage B ω (k + 1) → p.InStage B ω k := by
    intro ω k ⟨hlt, hstop⟩
    exact ⟨Nat.lt_of_succ_lt hlt, fun l hl =>
      hstop l (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hl).1,
        le_trans (Finset.mem_Icc.mp hl).2 (Nat.le_succ k)⟩)⟩
  -- Express `p.reward F B - lam * p.time F B` as sum over `k < numRemaining B`
  have hrew_sum : p.reward F B = ∑ k ∈ Finset.range (numRemaining B),
      ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k)
      else 0) ∂serviceLaw F := by
    unfold Stage.reward
    have hint : ∀ k ∈ Finset.range (numRemaining B),
        Integrable (fun ω => if p.InStage B ω k then
          F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k)
        else 0) (serviceLaw F) := by
      intro k _
      have hfun : (fun ω => if p.InStage B ω k then
          F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k)
        else 0) =
        (fun ω => Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          (if p.InStage B ω k then F.reward (p.toPolicy.job ω k) else 0)) := by
        ext ω; split_ifs <;> ring
      rw [hfun]
      refine integrable_exp_comp_mul_bound F p.toPolicy k _
        (Measurable.ite (measurableSet_inStage B p k)
          ((measurable_of_finite_discrete F.reward).comp (measurable_job p.toPolicy k))
          measurable_const).aestronglyMeasurable
        (∑ i : Fin n, F.reward i) fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs, abs_of_pos (F.reward_pos _)]
            exact Finset.single_le_sum (f := F.reward) (fun i _ => (F.reward_pos i).le) (Finset.mem_univ _)
          · rw [norm_zero]; exact Finset.sum_nonneg fun i _ => (F.reward_pos i).le
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hstep := integral_step_exp F B p.toPolicy hp k hk' (fun ω => p.InStage B ω k)
      (measurableSet_inStage B p k) (hInStage_indep k) (fun _ j => F.reward j)
    have hL : (fun ω => if p.InStage B ω k then
        F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k) else 0) =
      (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.reward (p.toPolicy.job ω k) else 0) := by
      ext ω; split_ifs <;> ring
    have hR : (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (phi F (p.toPolicy.job ω k) * F.reward (p.toPolicy.job ω k)) else 0) =
      (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k) else 0) := by
      ext ω; split_ifs <;> simp [jobA, mul_comm]
    rw [hL, hstep, hR]
  have htime_sum : p.time F B = ∑ k ∈ Finset.range (numRemaining B),
      ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobC F (p.toPolicy.job ω k)
      else 0) ∂serviceLaw F := by
    unfold Stage.time
    have hint : ∀ k ∈ Finset.range (numRemaining B),
        Integrable (fun ω => if p.InStage B ω k then
          F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
            Real.exp (-F.γ * p.toPolicy.completionTime ω k))
        else 0) (serviceLaw F) := by
      intro k _
      have hfun : (fun ω => if p.InStage B ω k then
          F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
            Real.exp (-F.γ * p.toPolicy.completionTime ω k))
        else 0) =
        (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (if p.InStage B ω k then F.γ⁻¹ else 0) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          (if p.InStage B ω k then F.γ⁻¹ else 0)) := by
        ext ω; split_ifs <;> ring
      rw [hfun]
      refine Integrable.sub ?_ ?_
      · refine integrable_exp_start_mul_bound F p.toPolicy k _
          (Measurable.ite (measurableSet_inStage B p k) measurable_const measurable_const).aestronglyMeasurable
          F.γ⁻¹ fun ω => by
            split_ifs
            · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
            · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
      · refine integrable_exp_comp_mul_bound F p.toPolicy k _
          (Measurable.ite (measurableSet_inStage B p k) measurable_const measurable_const).aestronglyMeasurable
          F.γ⁻¹ fun ω => by
            split_ifs
            · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
            · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hfun : (fun ω => if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) =
      (fun ω => (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * F.γ⁻¹ else 0) -
        (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.γ⁻¹ else 0)) := by
      ext ω; split_ifs <;> ring
    have hi1 : Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * F.γ⁻¹ else 0) (serviceLaw F) := by
      have : (fun ω => if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * F.γ⁻¹ else 0) =
        (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (if p.InStage B ω k then F.γ⁻¹ else 0)) := by ext ω; split_ifs <;> ring
      rw [this]
      refine integrable_exp_start_mul_bound F p.toPolicy k _
        (Measurable.ite (measurableSet_inStage B p k) measurable_const measurable_const).aestronglyMeasurable
        F.γ⁻¹ fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
          · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
    have hi2 : Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.γ⁻¹ else 0) (serviceLaw F) := by
      have : (fun ω => if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.γ⁻¹ else 0) =
        (fun ω => Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          (if p.InStage B ω k then F.γ⁻¹ else 0)) := by ext ω; split_ifs <;> ring
      rw [this]
      refine integrable_exp_comp_mul_bound F p.toPolicy k _
        (Measurable.ite (measurableSet_inStage B p k) measurable_const measurable_const).aestronglyMeasurable
        F.γ⁻¹ fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr F.γ_pos)]
          · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
    have hstep := integral_step_exp F B p.toPolicy hp k hk' (fun ω => p.InStage B ω k)
      (measurableSet_inStage B p k) (hInStage_indep k) (fun _ _ => F.γ⁻¹)
    have hi2' : Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * (phi F (p.toPolicy.job ω k) * F.γ⁻¹) else 0)
        (serviceLaw F) := by
      have : (fun ω => if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * (phi F (p.toPolicy.job ω k) * F.γ⁻¹) else 0) =
        (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (if p.InStage B ω k then phi F (p.toPolicy.job ω k) * F.γ⁻¹ else 0)) := by
        ext ω; split_ifs <;> ring
      rw [this]
      refine integrable_exp_start_mul_bound F p.toPolicy k _
        (Measurable.ite (measurableSet_inStage B p k)
          (((measurable_of_finite_discrete (phi F)).comp (measurable_job p.toPolicy k)).mul measurable_const)
          measurable_const).aestronglyMeasurable
        F.γ⁻¹ fun ω => by
          split_ifs
          · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (phi_pos F _), abs_of_pos (inv_pos.mpr F.γ_pos)]
            exact mul_le_of_le_one_left (inv_pos.mpr F.γ_pos).le (phi_lt_one F _).le
          · rw [norm_zero]; exact (inv_pos.mpr F.γ_pos).le
    rw [hfun, integral_sub hi1 hi2, hstep, ← integral_sub hi1 hi2']
    congr 1
    ext ω
    split_ifs <;> simp [jobC] <;> ring
  -- Now define the telescoping sequence `S k`
  let S : ℕ → ℝ := fun k =>
    if k = 0 then dpH F lam B
    else ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          dpG F lam (B ∪ (p.toPolicy.hist ω k).jobs)
      else 0) ∂serviceLaw F
  have hS0 : S 0 = dpH F lam B := by simp [S]
  have hSm : S (numRemaining B) = 0 := by
    have hne0 : numRemaining B ≠ 0 := hrem_pos.ne'
    simp only [S, hne0, ↓reduceIte]
    have hfalse : ∀ ω, ¬ p.InStage B ω (numRemaining B) := fun ω h => lt_irrefl _ h.1
    simp [hfalse]
  have htele : dpH F lam B = ∑ k ∈ Finset.range (numRemaining B), (S k - S (k + 1)) := by
    rw [Finset.sum_range_sub' S (numRemaining B), hS0, hSm, sub_zero]
  rw [hrew_sum, htime_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, htele]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k < numRemaining B := Finset.mem_range.mp hk
  -- Integrability helpers for step k
  have hiA : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k) else 0)
      (serviceLaw F) := by
    have : (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k) else 0) =
      (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (if p.InStage B ω k then jobA F (p.toPolicy.job ω k) else 0)) := by ext ω; split_ifs <;> ring
    rw [this]
    refine integrable_exp_start_mul_bound F p.toPolicy k _
      (Measurable.ite (measurableSet_inStage B p k)
        ((measurable_of_finite_discrete (jobA F)).comp (measurable_job p.toPolicy k))
        measurable_const).aestronglyMeasurable
      (∑ i : Fin n, jobA F i) fun ω => by
        split_ifs
        · rw [Real.norm_eq_abs, abs_of_pos (jobA_pos F _)]
          exact Finset.single_le_sum (f := jobA F) (fun i _ => (jobA_pos F i).le) (Finset.mem_univ _)
        · rw [norm_zero]; exact Finset.sum_nonneg fun i _ => (jobA_pos F i).le
  have hiC : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobC F (p.toPolicy.job ω k) else 0)
      (serviceLaw F) := by
    have : (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobC F (p.toPolicy.job ω k) else 0) =
      (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (if p.InStage B ω k then jobC F (p.toPolicy.job ω k) else 0)) := by ext ω; split_ifs <;> ring
    rw [this]
    refine integrable_exp_start_mul_bound F p.toPolicy k _
      (Measurable.ite (measurableSet_inStage B p k)
        ((measurable_of_finite_discrete (jobC F)).comp (measurable_job p.toPolicy k))
        measurable_const).aestronglyMeasurable
      (∑ i : Fin n, jobC F i) fun ω => by
        split_ifs
        · rw [Real.norm_eq_abs, abs_of_pos (jobC_pos F _)]
          exact Finset.single_le_sum (f := jobC F) (fun i _ => (jobC_pos F i).le) (Finset.mem_univ _)
        · rw [norm_zero]; exact Finset.sum_nonneg fun i _ => (jobC_pos F i).le
  have hiSk1 : Integrable (fun ω => if p.InStage B ω (k + 1) then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0) (serviceLaw F) := by
    have : (fun ω => if p.InStage B ω (k + 1) then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0) =
      (fun ω => Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        (if p.InStage B ω (k + 1) then dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0)) := by
      ext ω; split_ifs <;> ring
    rw [this]
    refine integrable_exp_comp_mul_bound F p.toPolicy k _
      (Measurable.ite (measurableSet_inStage B p (k + 1))
        (measurable_jobs_comp p.toPolicy (k + 1) fun D => dpG F lam (B ∪ D))
        measurable_const).aestronglyMeasurable M fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs]; exact hM _
          · rw [norm_zero]; exact hM_nn
  have hiCont : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0) (serviceLaw F) := by
    have : (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0) =
      (fun ω => Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        (if p.InStage B ω k then dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0)) := by
      ext ω; split_ifs <;> ring
    rw [this]
    refine integrable_exp_comp_mul_bound F p.toPolicy k _
      (Measurable.ite (measurableSet_inStage B p k)
        (measurable_jobs_comp p.toPolicy (k + 1) fun D => dpG F lam (B ∪ D))
        measurable_const).aestronglyMeasurable M fun ω => by
          split_ifs
          · rw [Real.norm_eq_abs]; exact hM _
          · rw [norm_zero]; exact hM_nn
  have hiCont' : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (phi F (p.toPolicy.job ω k) * dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0) (serviceLaw F) := by
    have : (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (phi F (p.toPolicy.job ω k) * dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
        else 0) =
      (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (if p.InStage B ω k then
          phi F (p.toPolicy.job ω k) * dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
        else 0)) := by ext ω; split_ifs <;> ring
    rw [this]
    refine integrable_exp_start_mul_bound F p.toPolicy k _ ?_ M fun ω => ?_
    · refine (Measurable.ite (measurableSet_inStage B p k) ?_ measurable_const).aestronglyMeasurable
      have h1 : Measurable fun ω => (p.toPolicy.job ω k, fun i : Fin k => (histVec p.toPolicy ω k i).1) :=
        (measurable_job p.toPolicy k).prodMk
          (measurable_pi_lambda _ fun i =>
            measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histVec p.toPolicy k)))
      have heq : (fun ω => phi F (p.toPolicy.job ω k) *
            dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))) =
          (fun q : Fin n × (Fin k → Fin n) =>
            phi F q.1 * dpG F lam (insert q.1 (B ∪ (List.ofFn q.2).toFinset))) ∘
            (fun ω => (p.toPolicy.job ω k, fun i : Fin k => (histVec p.toPolicy ω k i).1)) := by
        ext ω
        simp [Function.comp_def, History.jobs, ← ofFn_histVec p.toPolicy ω k, List.map_ofFn]
      rw [heq]
      exact (measurable_of_finite_discrete _).comp h1
    · split_ifs
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (phi_pos F _)]
        calc phi F (p.toPolicy.job ω k) * |dpG F lam _|
            ≤ 1 * M := mul_le_mul (phi_lt_one F _).le (hM _) (abs_nonneg _) zero_le_one
          _ = M := one_mul M
      · rw [norm_zero]; exact hM_nn
  -- Upper bound S (k + 1) by `hiCont'`
  have hSk1_le : S (k + 1) ≤ ∫ ω, (if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (phi F (p.toPolicy.job ω k) * dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0) ∂serviceLaw F := by
    have hstep := integral_step_exp F B p.toPolicy hp k hk' (fun ω => p.InStage B ω k)
      (measurableSet_inStage B p k) (hInStage_indep k) (fun D j => dpG F lam (insert j D))
    have hstep_eq : ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          dpG F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) else 0) ∂serviceLaw F =
        ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F (p.toPolicy.job ω k) *
              dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
          else 0) ∂serviceLaw F := by
      convert hstep using 2
      ext ω
      split_ifs <;> simp [hist_jobs_succ, Finset.union_insert]
    rw [← hstep_eq]
    simp only [S, Nat.succ_ne_zero, ↓reduceIte]
    refine integral_mono hiSk1 hiCont fun ω => ?_
    by_cases h1 : p.InStage B ω (k + 1)
    · have h0 := hInStage_anti ω k h1
      simp only [h1, h0, ↓reduceIte]
      exact le_rfl
    · simp only [h1, ↓reduceIte]
      split_ifs
      · exact mul_nonneg (Real.exp_pos _).le (dpG_nonneg F lam _)
      · exact le_rfl
  have hiAC : Integrable (fun ω =>
      (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k) else 0) -
      lam * (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobC F (p.toPolicy.job ω k) else 0))
      (serviceLaw F) := hiA.sub (hiC.const_mul lam)
  have hiComb : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (jobA F (p.toPolicy.job ω k) - lam * jobC F (p.toPolicy.job ω k) +
          phi F (p.toPolicy.job ω k) *
            dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0) (serviceLaw F) :=
    (hiAC.add hiCont').congr (ae_of_all _ fun ω => by simp only [Pi.add_apply]; split_ifs <;> ring)
  -- Now combine `A - lam * C + S (k + 1) ≤ S k`
  have hgoal : (∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k) else 0)
        ∂serviceLaw F) -
      lam * (∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobC F (p.toPolicy.job ω k) else 0)
        ∂serviceLaw F) + S (k + 1) ≤ S k := by
    calc _ ≤ (∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobA F (p.toPolicy.job ω k) else 0)
          ∂serviceLaw F) -
        (∫ ω, lam * (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobC F (p.toPolicy.job ω k) else 0)
          ∂serviceLaw F) +
        (∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F (p.toPolicy.job ω k) *
              dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
          else 0) ∂serviceLaw F) := by
            rw [← integral_const_mul]
            linarith
      _ = ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (jobA F (p.toPolicy.job ω k) - lam * jobC F (p.toPolicy.job ω k) +
              phi F (p.toPolicy.job ω k) *
                dpG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
          else 0) ∂serviceLaw F := by
            rw [← integral_sub hiA (hiC.const_mul lam), ← integral_add hiAC hiCont']
            congr 1; ext ω; split_ifs <;> ring
      _ ≤ S k := by
        cases k with
        | zero =>
          simp only [S, ↓reduceIte]
          have hconst : dpH F lam B = ∫ _ : Fin n → ℝ, dpH F lam B ∂serviceLaw F := by
            simp
          rw [hconst]
          refine integral_mono hiComb (integrable_const _) fun ω => ?_
          have hin : p.InStage B ω 0 := ⟨hrem_pos, fun l hl => by
            have := Finset.mem_Icc.mp hl; omega⟩
          simp only [hin, ↓reduceIte, startTime_zero, mul_zero, Real.exp_zero, one_mul,
            hist_jobs_zero, Finset.union_empty]
          exact dpH_ge F lam B (p.toPolicy.job ω 0) (by simpa [hist_jobs_zero] using hp ω 0 hrem_pos)
        | succ k' =>
          simp only [S, Nat.succ_ne_zero, ↓reduceIte]
          have hiSk : Integrable (fun ω => if p.InStage B ω (k' + 1) then
              Real.exp (-F.γ * p.toPolicy.startTime ω (k' + 1)) *
                dpG F lam (B ∪ (p.toPolicy.hist ω (k' + 1)).jobs) else 0) (serviceLaw F) := by
            have : (fun ω => if p.InStage B ω (k' + 1) then
                Real.exp (-F.γ * p.toPolicy.startTime ω (k' + 1)) *
                  dpG F lam (B ∪ (p.toPolicy.hist ω (k' + 1)).jobs) else 0) =
              (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω (k' + 1)) *
                (if p.InStage B ω (k' + 1) then
                  dpG F lam (B ∪ (p.toPolicy.hist ω (k' + 1)).jobs) else 0)) := by
              ext ω; split_ifs <;> ring
            rw [this]
            refine integrable_exp_start_mul_bound F p.toPolicy (k' + 1) _
              (Measurable.ite (measurableSet_inStage B p (k' + 1))
                (measurable_jobs_comp p.toPolicy (k' + 1) fun D => dpG F lam (B ∪ D))
                measurable_const).aestronglyMeasurable M fun ω => by
                  split_ifs
                  · rw [Real.norm_eq_abs]; exact hM _
                  · rw [norm_zero]; exact hM_nn
          refine integral_mono hiComb hiSk fun ω => ?_
          split_ifs
          · refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            exact le_trans (dpH_ge F lam _ _ (hp ω (k' + 1) hk')) (dpH_le_dpG F lam _)
          · exact le_rfl
  linarith

private lemma familyIndex_spec {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (hB : B ≠ Finset.univ) :
    dpH F (familyIndex F B) B = 0 ∧
    (∃ Y : List (Fin n), Y ≠ [] ∧ ListFeasible F B Y ∧ listNet F (familyIndex F B) Y = 0) ∧
    (∀ L : List (Fin n), ListFeasible F B L → listNet F (familyIndex F B) L ≤ 0) := by
  obtain ⟨ν, hν⟩ := exists_dpH_root F B hB
  obtain ⟨Y, hYne, hYfeas, hYnet⟩ := exists_list_dpH F ν B hB
  rw [hν] at hYnet
  let pY := stageOfList F B Y hYne
  have hpY_feas : pY.Feasible F B := stageOfList_feasible F B Y hYfeas hYne
  have hpY_ratio : pY.ratio F B = ν := by
    unfold Stage.ratio
    rw [stageOfList_reward F B Y hYfeas hYne, stageOfList_time F B Y hYfeas hYne]
    have htime := listTime_pos F hYne
    have hrew : listReward F Y = ν * listTime F Y := by
      rw [listNet_eq] at hYnet; linarith
    rw [hrew, mul_div_cancel_right₀ _ htime.ne']
  have hle : ∀ x ∈ {x : ℝ | ∃ p : Stage n, p.Feasible F B ∧ x = p.ratio F B}, x ≤ ν := by
    rintro x ⟨p, hp, rfl⟩
    have htime := stage_time_pos F B hB p hp
    have hnet := stage_net_le_dpH F ν B hB p hp
    rw [hν] at hnet
    unfold Stage.ratio
    rw [div_le_iff₀ htime]
    linarith
  have hmem : ν ∈ {x : ℝ | ∃ p : Stage n, p.Feasible F B ∧ x = p.ratio F B} :=
    ⟨pY, hpY_feas, hpY_ratio.symm⟩
  have hidx : familyIndex F B = ν :=
    le_antisymm (csSup_le ⟨ν, hmem⟩ hle) (le_csSup ⟨ν, hle⟩ hmem)
  rw [hidx]
  refine ⟨hν, ⟨Y, hYne, hYfeas, hYnet⟩, fun L hL => ?_⟩
  by_cases hLne : L = []
  · subst hLne; simp [listNet]
  · have hnet := stage_net_le_dpH F ν B hB (stageOfList F B L hLne)
      (stageOfList_feasible F B L hL hLne)
    rw [stageOfList_reward F B L hL hLne, stageOfList_time F B L hL hLne, hν, ← listNet_eq] at hnet
    exact hnet

/-! ### Section 9: Combinatorial Bridge (`exists_fiStarStage_of_u_optimal`) -/

private lemma perm_filter_append_filter_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p ++ l.filter fun a => !p a).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases ha : p a
    · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact List.perm_middle.trans (ih.cons a)
    · simp only [List.filter_cons, ha, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.cons_append]
      exact ih.cons a

private lemma mem_takeWhile_eq_true {α : Type*} {p : α → Bool} {l : List α} {a : α}
    (ha : a ∈ l.takeWhile p) : p a = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    cases hx : p x <;> simp [hx] at ha
    rcases ha with rfl | ha'
    · exact hx
    · exact ih ha'

private lemma dropWhile_cons_eq_false {α : Type*} {p : α → Bool} {l : List α} {y : α}
    {rest : List α} (h : l.dropWhile p = y :: rest) : p y = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases ha : p a <;> simp [ha] at h
    · exact h.1 ▸ ha
    · exact ih h

private lemma exists_fiStarStage_of_u_optimal {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (j₀ : Fin n) (hj₀ : IsAvailable F B j₀)
    (hopt : dpU F B = jobA F j₀ + phi F j₀ * dpU F (insert j₀ B)) :
    ∃ p : Stage n, IsFIStarStage F B p ∧ p.next [] = j₀ := by
  have hB : B ≠ Finset.univ := fun h => hj₀.1 (h ▸ Finset.mem_univ j₀)
  let ν := familyIndex F B
  obtain ⟨_, ⟨Y, hYne, hYfeas, hYnet⟩, hle_net⟩ := familyIndex_spec F B hB
  obtain ⟨X_tail, hXt_feas, hXt_len, hXt_rew⟩ := exists_complete_list_dpU F (insert j₀ B)
  let X : List (Fin n) := j₀ :: X_tail
  have hXfeas : ListFeasible F B X := ⟨hj₀, hXt_feas⟩
  have hXlen : X.length = numRemaining B := by
    simp only [X, List.length_cons, hXt_len]
    unfold numRemaining
    rw [Finset.card_insert_of_notMem hj₀.1]
    have : B.card < n := by
      have : B ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hB
      simpa using Finset.card_lt_card this
    omega
  have hXrew : listReward F X = dpU F B := by
    simp only [X, listReward, hXt_rew, hopt]
  let S_Y : Finset (Fin n) := Y.toFinset
  let P : Fin n → Bool := fun i => decide (i ∈ S_Y)
  let Y' : List (Fin n) := X.filter P
  let Z : List (Fin n) := X.filter fun i => !P i
  -- `Y'` is a permutation of `Y`
  have hXuniv : B ∪ X.toFinset = Finset.univ := listFeasible_union_univ hXfeas hXlen
  have hY'_perm : Y'.Perm Y := by
    refine (List.perm_ext_iff_of_nodup ((listFeasible_nodup hXfeas).filter _)
      (listFeasible_nodup hYfeas)).mpr fun i => ?_
    simp only [P, S_Y, List.mem_filter, decide_eq_true_eq, List.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro hiY
      refine ⟨?_, hiY⟩
      have hi_notB : i ∉ B := listFeasible_disjoint hYfeas i hiY
      have hi_u : i ∈ B ∪ X.toFinset := hXuniv.symm ▸ Finset.mem_univ i
      exact List.mem_toFinset.mp ((Finset.mem_union.mp hi_u).resolve_left hi_notB)
  have hY'ne : Y' ≠ [] := fun h => hYne (List.Perm.nil_eq (h ▸ hY'_perm)).symm
  have hPhiY' : listPhi F Y' = listPhi F Y := listPhi_perm F hY'_perm
  -- Feasibility of `Y'` and `Z`
  have hdown : ∀ y ∈ S_Y, ∀ i, F.prec i y → i ∈ B ∪ S_Y := fun y hy i hprec =>
    listFeasible_pred_mem hYfeas (List.mem_toFinset.mp hy) hprec
  have hY'feas : ListFeasible F B Y' := listFeasible_filter_downward hXfeas hdown
  have hZfeas : ListFeasible F (B ∪ S_Y) Z := listFeasible_filter_compl hXfeas
  have hYZ_feas : ListFeasible F B (Y ++ Z) :=
    (listFeasible_append F B Y Z).mpr ⟨hYfeas, hZfeas⟩
  have hYZ_perm : (Y ++ Z).Perm X := by
    have hsplit : (Y' ++ Z).Perm X := perm_filter_append_filter_not P X
    exact (hY'_perm.symm.append_right Z).trans hsplit
  have hYZ_len : (Y ++ Z).length = numRemaining B := by
    rw [hYZ_perm.length_eq, hXlen]
  have hYZ_time : listTime F (Y ++ Z) = listTime F X := by
    rw [listTime_eq, listTime_eq, listPhi_perm F hYZ_perm]
  have hYZ_net_le : listNet F ν (Y ++ Z) ≤ listNet F ν X := by
    rw [listNet_eq, listNet_eq, hYZ_time, hXrew]
    linarith [listReward_le_dpU F hYZ_feas hYZ_len]
  have hYZ_net_eq : listNet F ν (Y ++ Z) = listPhi F Y' * listNet F ν Z := by
    rw [listNet_append, hYnet, zero_add, hPhiY']
  -- Prefix bounds for `interleaveExcess_nonpos_and_eq`
  have hpreP : ∀ X_pre, X_pre <+: X → listNet F ν (X_pre.filter P) ≤ 0 := fun X_pre hpre =>
    hle_net _ (listFeasible_prefix hY'feas (hpre.filter P))
  have hpreN : ∀ X_pre, X_pre <+: X → listNet F ν (X_pre.filter fun i => !P i) ≤ 0 := by
    intro X_pre hpre
    have hZf : ListFeasible F (B ∪ S_Y) (X_pre.filter fun i => !P i) :=
      listFeasible_prefix hZfeas (hpre.filter _)
    have hYf : ListFeasible F B (Y ++ X_pre.filter fun i => !P i) :=
      (listFeasible_append F B Y _).mpr ⟨hYfeas, hZf⟩
    have hnet := hle_net _ hYf
    rw [listNet_append, hYnet, zero_add] at hnet
    exact nonpos_of_mul_nonpos_right hnet (listPhi_pos F Y)
  obtain ⟨hex_le, hex_eq⟩ := interleaveExcess_nonpos_and_eq F ν P X hpreP hpreN
  have hdecomp : listNet F ν X - listPhi F Y' * listNet F ν Z =
      listPhi F Z * listNet F ν Y' + interleaveExcess F ν P X := by
    unfold interleaveExcess
    ring
  have hY'net_le : listNet F ν Y' ≤ 0 := hle_net Y' hY'feas
  have hterm1_le : listPhi F Z * listNet F ν Y' ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (listPhi_pos F Z).le hY'net_le
  have hsum_nn : 0 ≤ listPhi F Z * listNet F ν Y' + interleaveExcess F ν P X := by
    linarith [hdecomp, hYZ_net_le, hYZ_net_eq]
  have hY'net_zero : listNet F ν Y' = 0 := by
    have : listPhi F Z * listNet F ν Y' = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (listPhi_pos F Z).ne'
  have hex_zero : interleaveExcess F ν P X = 0 := by linarith
  -- Construct the FI* stage starting with `j₀`
  have make_stage : ∀ L : List (Fin n), (hne : L ≠ []) → ListFeasible F B L →
      listNet F ν L = 0 → L.head hne = j₀ →
      ∃ p : Stage n, IsFIStarStage F B p ∧ p.next [] = j₀ := by
    intro L hne hLfeas hLnet hhead
    refine ⟨stageOfList F B L hne, ⟨stageOfList_feasible F B L hLfeas hne, ?_⟩, ?_⟩
    · unfold Stage.ratio
      rw [stageOfList_reward F B L hLfeas hne, stageOfList_time F B L hLfeas hne]
      have hrew : listReward F L = ν * listTime F L := by
        rw [listNet_eq] at hLnet; linarith
      rw [hrew, mul_div_cancel_right₀ _ (listTime_pos F hne).ne']
    · rw [stageOfList_next_nil, hhead]
  by_cases hjS : j₀ ∈ S_Y
  · have hPj0 : P j₀ = true := decide_eq_true hjS
    have hY'_eq : Y' = j₀ :: X_tail.filter P := by
      simp [Y', X, hPj0]
    exact make_stage Y' hY'ne hY'feas hY'net_zero (by simp [hY'_eq])
  · have hPj0 : P j₀ = false := decide_eq_false hjS
    let X_pre := X.takeWhile (fun i => !P i)
    let X_rest := X.dropWhile (fun i => !P i)
    have hX_split : X_pre ++ X_rest = X := List.takeWhile_append_dropWhile
    have hrest_ne : X_rest ≠ [] := by
      intro hnil
      have hXeq : X_pre = X := by simpa [hnil] using hX_split
      have hY'nil : Y' = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [← hXeq] at ha
        have hna := mem_takeWhile_eq_true (p := fun i => !P i) ha
        simp at hna
        simp [hna]
      exact hY'ne hY'nil
    cases hrest : X_rest with
    | nil => exact absurd hrest hrest_ne
    | cons y X_post =>
      have hPy : P y = true := by
        have h1 := dropWhile_cons_eq_false (p := fun i => !P i) (l := X) hrest
        simpa using h1
      have hX_eq : X = X_pre ++ y :: X_post := by rw [← hX_split, hrest]
      have hfilt_eq : X_pre.filter (fun i => !P i) = X_pre := by
        rw [List.filter_eq_self]
        intro a ha
        exact mem_takeWhile_eq_true (p := fun i => !P i) ha
      have hpre_net : listNet F ν X_pre = 0 := by
        rw [← hfilt_eq]
        exact hex_eq hex_zero X_pre y X_post hX_eq hPy
      have hpre_eq : X_pre = j₀ :: X_tail.takeWhile (fun i => !P i) := by
        simp [X_pre, X, hPj0]
      have hpre_ne : X_pre ≠ [] := by rw [hpre_eq]; exact List.cons_ne_nil _ _
      have hpre_feas : ListFeasible F B X_pre :=
        listFeasible_prefix hXfeas ⟨y :: X_post, hX_eq.symm⟩
      exact make_stage X_pre hpre_ne hpre_feas hpre_net (by simp [hpre_eq])

end OptimalIsFIHelpers

theorem solution {n : ℕ} (F : AllocationIndices.Precedence.JobFamily n) (A : Finset (Fin n))
    (π : AllocationIndices.Precedence.Policy n)
    (hπ : AllocationIndices.Precedence.IsOptimalPolicy F A π) :
    AllocationIndices.Precedence.IsFIPolicy F A π := by
  refine ⟨hπ.1, ?_⟩
  filter_upwards [optimal_u_greedy_ae F A π hπ] with ω hω k hk
  exact exists_fiStarStage_of_u_optimal F (A ∪ (π.hist ω k).jobs) (π.job ω k)
    (hπ.1 ω k hk) (hω k hk)
