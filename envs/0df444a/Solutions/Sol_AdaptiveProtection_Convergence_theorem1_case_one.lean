-- Prove2me | solution 1 for AdaptiveProtection.Convergence.theorem1_case_one
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:26:15.187505+00:00
-- url     : https://prove2.me/submissions/536b8faf-f461-4dc0-adbd-8195ad5faf71

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology ProbabilityTheory

namespace APDisproof

open AdaptiveProtection.Convergence

noncomputable def ν0 : ℕ → Measure ℝ := fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

instance inst_prob (i : ℕ) : IsProbabilityMeasure (ν0 i) :=
  ⟨by simp [ν0, Real.volume_Icc]⟩

noncomputable def f0 : ℕ → ℝ := fun i => if i ≤ 1 then 2 else 1

noncomputable def γ0 : ℕ → ℝ := stepSize (1 / 4) 0

noncomputable def θ0 : ℕ → ℝ := fun _ => 3 / 2

noncomputable def s (n : ℕ) (ω : ℕ → ℕ → ℝ) : ℝ := iterate f0 1 γ0 θ0 ω n 1

lemma ratio2 : ratio f0 2 = 1 / 2 := by simp [ratio, f0]

lemma fill_iff (θ x : ℕ → ℝ) : x ∈ fillEvent θ 1 ↔ θ 1 < x 1 := by
  simp [fillEvent, NestedSeatAlloc.ProbCond.nestEvent]

lemma s_zero (ω : ℕ → ℕ → ℝ) : s 0 ω = 3 / 2 := rfl

lemma s_succ (n : ℕ) (ω : ℕ → ℕ → ℝ) :
    s (n + 1) ω = s n ω - γ0 (n + 1) * (1 / 2 - if s n ω < ω n 1 then 1 else 0) := by
  show iterate f0 1 γ0 θ0 ω (n + 1) 1 = iterate f0 1 γ0 θ0 ω n 1 - γ0 (n + 1) *
    (1 / 2 - if iterate f0 1 γ0 θ0 ω n 1 < ω n 1 then 1 else 0)
  rw [iterate_succ]
  congr 2
  simp only [adj, le_refl, and_self, if_true]
  rw [ratio2]
  congr 1
  by_cases h : iterate f0 1 γ0 θ0 ω n 1 < ω n 1
  · rw [Set.indicator_of_mem ((fill_iff _ _).2 h)]
    rw [if_pos h]
  · rw [Set.indicator_of_notMem (fun hm => h ((fill_iff _ _).1 hm))]
    rw [if_neg h]

lemma γ0_nonneg (n : ℕ) : 0 ≤ γ0 n := by
  simp only [γ0, stepSize, add_zero]; positivity

lemma γ0_succ (n : ℕ) : γ0 (n + 1) = 1 / (4 * ((n : ℝ) + 1)) := by
  simp only [γ0, stepSize, add_zero]; push_cast; field_simp

lemma γ0_le (n : ℕ) : γ0 (n + 1) ≤ 1 / 4 := by
  rw [γ0_succ]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma s_meas (n : ℕ) : Measurable (s n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have : s (n + 1) = fun ω => s n ω - γ0 (n + 1) * (1 / 2 - if s n ω < ω n 1 then 1 else 0) :=
      funext (s_succ n)
    rw [this]
    have hU : Measurable (fun ω : ℕ → ℕ → ℝ => ω n 1) :=
      (measurable_pi_apply 1).comp (measurable_pi_apply n)
    refine ih.sub (measurable_const.mul (measurable_const.sub ?_))
    exact Measurable.ite (measurableSet_lt ih hU) measurable_const measurable_const

lemma s_bound (n : ℕ) (ω : ℕ → ℕ → ℝ) : |s n ω| ≤ 3 / 2 + n := by
  induction n with
  | zero => rw [s_zero]; norm_num [abs_of_pos]
  | succ n ih =>
    rw [s_succ]
    have h1 := γ0_le n
    have h0 := γ0_nonneg (n + 1)
    have hI : |(1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num [abs_of_pos, abs_of_neg]
    have : |γ0 (n + 1) * (1 / 2 - if s n ω < ω n 1 then 1 else 0)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg h0]
      nlinarith [abs_nonneg (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0)]
    push_cast
    calc _ ≤ |s n ω| + |γ0 (n + 1) * (1 / 2 - if s n ω < ω n 1 then 1 else 0)| := abs_sub _ _
      _ ≤ _ := by linarith

lemma s_dep (n : ℕ) (ω ω' : ℕ → ℕ → ℝ) (h : ∀ j < n, ω j = ω' j) : s n ω = s n ω' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun j hj => h j (by omega))
    rw [s_succ, s_succ, ih', h n (by omega)]


instance inst_flight : IsProbabilityMeasure (flightLaw ν0) := by
  unfold flightLaw; infer_instance

instance inst_path : IsProbabilityMeasure (pathLaw ν0) := by
  unfold pathLaw; infer_instance

lemma ν0_real (S : Set ℝ) (hS : MeasurableSet S) :
    (ν0 1).real S = volume.real (S ∩ Set.Icc 0 1) := by
  simp only [ν0]; rw [measureReal_restrict_apply hS]

lemma pU_upper (t : ℝ) (ht : 0 ≤ t) : (ν0 1).real (Set.Ioi t) ≤ max (1 - t) 0 := by
  rw [ν0_real _ measurableSet_Ioi, ← Real.volume_real_Ioc]
  apply measureReal_mono
  · intro x hx; exact ⟨hx.1, hx.2.2⟩
  · simp [Real.volume_Ioc]

lemma pU_lower (t : ℝ) (ht : t ≤ 1) : 1 - max t 0 ≤ (ν0 1).real (Set.Ioi t) := by
  rw [ν0_real _ measurableSet_Ioi]
  have h1 : 1 - max t 0 = volume.real (Set.Ioc (max t 0) 1) := by
    rw [Real.volume_real_Ioc_of_le (max_le ht zero_le_one)]
  rw [h1]
  apply measureReal_mono
  · intro x hx
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, (le_max_right t 0).trans hx.1.le, hx.2⟩
  · exact (measure_mono Set.inter_subset_right).trans_lt (by simp [Real.volume_Icc]) |>.ne

lemma pU_le_one (t : ℝ) : (ν0 1).real (Set.Ioi t) ≤ 1 := measureReal_le_one

lemma pIio_le (x y : ℝ) (hxy : y ≤ x) :
    (ν0 1).real (Set.Iio x) - (ν0 1).real (Set.Iio y) ≤ x - y := by
  have h1 : (ν0 1).real (Set.Iio x) ≤ (ν0 1).real (Set.Iio y) + (ν0 1).real (Set.Ico y x) := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro z hz
    by_cases h : z < y
    · exact Or.inl h
    · exact Or.inr ⟨not_lt.1 h, hz⟩
  have h2 : (ν0 1).real (Set.Ico y x) ≤ x - y := by
    rw [ν0_real _ measurableSet_Ico, ← Real.volume_real_Ico_of_le hxy]
    exact measureReal_mono Set.inter_subset_left (by simp [Real.volume_Ico])
  linarith

lemma pIio_mono (x y : ℝ) (hxy : y ≤ x) :
    (ν0 1).real (Set.Iio y) ≤ (ν0 1).real (Set.Iio x) :=
  measureReal_mono (Set.Iio_subset_Iio hxy)

lemma law1 (S : Set ℝ) (hS : MeasurableSet S) :
    (flightLaw ν0).real ((fun z : ℕ → ℝ => z 1) ⁻¹' S) = (ν0 1).real S :=
  (measurePreserving_eval_infinitePi ν0 1).measureReal_preimage hS.nullMeasurableSet

lemma map_U (n : ℕ) : (pathLaw ν0).map (fun ω : ℕ → ℕ → ℝ => ω n 1) = ν0 1 := by
  have : (fun ω : ℕ → ℕ → ℝ => ω n 1) = (fun z : ℕ → ℝ => z 1) ∘ (fun ω => ω n) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply 1) (measurable_pi_apply n)]
  simp only [pathLaw]
  rw [Measure.infinitePi_map_eval]
  simp only [flightLaw]
  rw [Measure.infinitePi_map_eval]


lemma hU_meas (n : ℕ) : Measurable (fun ω : ℕ → ℕ → ℝ => ω n 1) :=
  (measurable_pi_apply 1).comp (measurable_pi_apply n)

lemma indep (n : ℕ) : IndepFun (s n) (fun ω : ℕ → ℕ → ℝ => ω n 1) (pathLaw ν0) := by
  have hi : iIndepFun (fun j (ω : ℕ → ℕ → ℝ) => ω j) (pathLaw ν0) :=
    iIndepFun_infinitePi (P := fun _ => flightLaw ν0) (X := fun _ => id) (fun _ => measurable_id)
  have h2 := hi.indepFun_finset (Finset.range n) {n} (by simp) (fun j => measurable_pi_apply j)
  let ext : (Finset.range n → ℕ → ℝ) → (ℕ → ℕ → ℝ) :=
    fun y j => if h : j ∈ Finset.range n then y ⟨j, h⟩ else 0
  have hext : Measurable ext := by
    apply measurable_pi_lambda
    intro j
    by_cases h : j ∈ Finset.range n
    · simp only [ext, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext, dif_neg h]; exact measurable_const
  let u : (({n} : Finset ℕ) → ℕ → ℝ) → ℝ := fun y => y ⟨n, Finset.mem_singleton_self n⟩ 1
  have hu : Measurable u := (measurable_pi_apply 1).comp (measurable_pi_apply _)
  have h3 := h2.comp ((s_meas n).comp hext) hu
  have e1 : (s n ∘ ext) ∘ (fun (a : ℕ → ℕ → ℝ) (i : Finset.range n) => a i) = s n := by
    funext ω
    apply s_dep
    intro j hj
    simp only [Function.comp, ext, dif_pos (Finset.mem_range.2 hj)]
  have e2 : u ∘ (fun (a : ℕ → ℕ → ℝ) (i : ({n} : Finset ℕ)) => a i) = fun ω => ω n 1 := rfl
  rw [e1, e2] at h3
  exact h3

lemma intb {g : (ℕ → ℕ → ℝ) → ℝ} (hg : Measurable g) (M : ℝ) (h : ∀ ω, |g ω| ≤ M) :
    Integrable g (pathLaw ν0) :=
  Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs]; exact h ω))

lemma ind_bound (a b : ℝ) : |(1 / 2 - if a < b then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> norm_num [abs_of_pos, abs_of_neg]

lemma e_bound (n : ℕ) (ω : ℕ → ℕ → ℝ) : |s n ω - 1 / 2| ≤ 2 + n := by
  have := s_bound n ω
  calc |s n ω - 1 / 2| ≤ |s n ω| + |(1 / 2 : ℝ)| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith

lemma inner_le (x : ℝ) : (x - 1 / 2) * (1 / 2 - (ν0 1).real (Set.Ioi x)) ≤ (x - 1 / 2) ^ 2 := by
  have h1 := pU_le_one x
  have h0 : 0 ≤ (ν0 1).real (Set.Ioi x) := measureReal_nonneg
  rcases le_or_gt (1 / 2) x with hx | hx
  · -- need p ≥ 1 - x
    have hp : 1 - x ≤ (ν0 1).real (Set.Ioi x) := by
      rcases le_or_gt x 1 with hx1 | hx1
      · have := pU_lower x hx1
        rw [max_eq_left (by linarith)] at this; exact this
      · linarith
    nlinarith
  · have hp : (ν0 1).real (Set.Ioi x) ≤ 1 - x := by
      rcases le_or_gt 0 x with hx0 | hx0
      · have := pU_upper x hx0
        rw [max_eq_left (by linarith)] at this; exact this
      · linarith
    nlinarith

lemma inner_eq (x : ℝ) :
    ∫ u, (x - 1 / 2) * (1 / 2 - if x < u then (1 : ℝ) else 0) ∂(ν0 1)
      = (x - 1 / 2) * (1 / 2 - (ν0 1).real (Set.Ioi x)) := by
  have e : (fun u : ℝ => (x - 1 / 2) * (1 / 2 - if x < u then (1 : ℝ) else 0))
      = fun u => (x - 1 / 2) * (1 / 2 - (Set.Ioi x).indicator 1 u) := by
    funext u
    by_cases h : x < u
    · rw [if_pos h, Set.indicator_of_mem (Set.mem_Ioi.2 h)]; rfl
    · rw [if_neg h, Set.indicator_of_notMem (fun hm => h (Set.mem_Ioi.1 hm))]
  have hi : Integrable ((Set.Ioi x).indicator (1 : ℝ → ℝ)) (ν0 1) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  rw [e, integral_const_mul, integral_sub (integrable_const _) hi, integral_const,
    integral_indicator_one measurableSet_Ioi]
  simp

lemma cross (n : ℕ) :
    ∫ ω, (s n ω - 1 / 2) * (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0) ∂(pathLaw ν0)
      ≤ ∫ ω, (s n ω - 1 / 2) ^ 2 ∂(pathLaw ν0) := by
  set μ := pathLaw ν0
  have hX := s_meas n
  have hY := hU_meas n
  let G : ℝ × ℝ → ℝ := fun p => (p.1 - 1 / 2) * (1 / 2 - if p.1 < p.2 then (1 : ℝ) else 0)
  have hG : Measurable G := by
    refine (measurable_fst.sub measurable_const).mul (measurable_const.sub ?_)
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
      measurable_const
  have hXY : Measurable (fun ω => (s n ω, ω n 1)) := hX.prodMk hY
  have hmap : μ.map (fun ω => (s n ω, ω n 1)) = (μ.map (s n)).prod (ν0 1) := by
    rw [← map_U n]
    exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 (indep n)
  have hGint0 : Integrable (G ∘ fun ω => (s n ω, ω n 1)) μ := by
    apply intb (hG.comp hXY) (2 + n)
    intro ω
    simp only [Function.comp, G]
    rw [abs_mul]
    have := e_bound n ω
    have := ind_bound (s n ω) (ω n 1)
    nlinarith [abs_nonneg (s n ω - 1 / 2),
      abs_nonneg (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0)]
  have hGint : Integrable G ((μ.map (s n)).prod (ν0 1)) := by
    rw [← hmap]
    exact (integrable_map_measure hG.aestronglyMeasurable hXY.aemeasurable).2 hGint0
  have hsq : Integrable (fun x : ℝ => (x - 1 / 2) ^ 2) (μ.map (s n)) := by
    have hm : Measurable (fun x : ℝ => (x - 1 / 2) ^ 2) := by fun_prop
    refine (integrable_map_measure hm.aestronglyMeasurable hX.aemeasurable).2 ?_
    apply intb (hm.comp hX) ((2 + n) ^ 2)
    intro ω
    simp only [Function.comp]
    rw [abs_pow]
    have := e_bound n ω
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∫ ω, (s n ω - 1 / 2) * (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0) ∂μ
      = ∫ ω, G (s n ω, ω n 1) ∂μ := rfl
    _ = ∫ p, G p ∂(μ.map (fun ω => (s n ω, ω n 1))) :=
        (integral_map hXY.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ x, ∫ u, G (x, u) ∂(ν0 1) ∂(μ.map (s n)) := by rw [hmap, integral_prod G hGint]
    _ ≤ ∫ x, (x - 1 / 2) ^ 2 ∂(μ.map (s n)) := by
        apply integral_mono hGint.integral_prod_left hsq
        intro x
        simp only [G]
        rw [inner_eq]
        exact inner_le x
    _ = ∫ ω, (s n ω - 1 / 2) ^ 2 ∂μ := by
        rw [integral_map hX.aemeasurable (by fun_prop : Measurable (fun x : ℝ => (x - 1 / 2) ^ 2)).aestronglyMeasurable]


noncomputable def a (n : ℕ) : ℝ := ∫ ω, (s n ω - 1 / 2) ^ 2 ∂(pathLaw ν0)

lemma a_nonneg (n : ℕ) : 0 ≤ a n := integral_nonneg (fun _ => sq_nonneg _)

lemma a_zero : a 0 = 1 := by
  simp only [a, s_zero]; norm_num

lemma sq_int (n : ℕ) : Integrable (fun ω => (s n ω - 1 / 2) ^ 2) (pathLaw ν0) := by
  apply intb (((s_meas n).sub measurable_const).pow_const 2) ((2 + n) ^ 2)
  intro ω
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (e_bound n ω) 2

lemma step (n : ℕ) : (1 - 2 * γ0 (n + 1)) * a n ≤ a (n + 1) := by
  set γ := γ0 (n + 1)
  have hγ : 0 ≤ γ := γ0_nonneg _
  have hc_meas : Measurable (fun ω : ℕ → ℕ → ℝ => (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0)) :=
    measurable_const.sub (Measurable.ite (measurableSet_lt (s_meas n) (hU_meas n))
      measurable_const measurable_const)
  have hec : Integrable (fun ω => (s n ω - 1 / 2) * (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0))
      (pathLaw ν0) := by
    apply intb (((s_meas n).sub measurable_const).mul hc_meas) (2 + n)
    intro ω
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [abs_mul]
    have := e_bound n ω
    have := ind_bound (s n ω) (ω n 1)
    nlinarith [abs_nonneg (s n ω - 1 / 2),
      abs_nonneg (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0)]
  have hmono : ∫ ω, ((s n ω - 1 / 2) ^ 2
      - 2 * γ * ((s n ω - 1 / 2) * (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0))) ∂(pathLaw ν0)
      ≤ a (n + 1) := by
    apply integral_mono ((sq_int n).sub (hec.const_mul _)) (sq_int (n + 1))
    intro ω
    simp only [Pi.sub_apply]
    rw [s_succ]
    nlinarith [sq_nonneg (γ * (1 / 2 - if s n ω < ω n 1 then (1 : ℝ) else 0))]
  rw [integral_sub (sq_int n) (hec.const_mul _), integral_const_mul] at hmono
  have hcr := cross n
  change _ ≤ a n at hcr
  change a n - _ ≤ _ at hmono
  nlinarith

lemma lower (n : ℕ) (hn : 1 ≤ n) : 1 ≤ 4 * n * a n ^ 2 := by
  induction n with
  | zero => omega
  | succ m ih =>
    have hs := step m
    rw [γ0_succ] at hs
    have ha := a_nonneg m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [a_zero] at hs
      norm_num at hs ⊢
      nlinarith
    · have ih' := ih hm
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hcoef : 1 - 2 * (1 / (4 * ((m : ℝ) + 1))) = (2 * m + 1) / (2 * m + 2) := by
        field_simp; ring
      rw [hcoef] at hs
      have hq : 0 ≤ (2 * (m : ℝ) + 1) / (2 * m + 2) := by positivity
      have hq2 : ((2 * (m : ℝ) + 1) / (2 * m + 2) * a m) ^ 2 ≤ a (m + 1) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hq ha) hs 2
      have key : 1 ≤ 4 * ((m : ℝ) + 1) * ((2 * (m : ℝ) + 1) / (2 * m + 2) * a m) ^ 2 := by
        rw [mul_pow, div_pow]
        rw [show 4 * ((m : ℝ) + 1) * ((2 * m + 1) ^ 2 / (2 * m + 2) ^ 2 * a m ^ 2)
            = (2 * m + 1) ^ 2 / (4 * m * (m + 1)) * (4 * m * a m ^ 2) by field_simp; ring]
        have : 1 ≤ (2 * (m : ℝ) + 1) ^ 2 / (4 * m * (m + 1)) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        nlinarith
      push_cast
      nlinarith


noncomputable def θs : ℕ → ℝ := fun _ => 1 / 2

lemma hf0 : ∀ i, 1 ≤ i → i ≤ 1 → f0 (i + 1) < f0 i := by
  intro i h1 h2
  obtain rfl : i = 1 := by omega
  simp [f0]

lemma hfpos0 : 0 < f0 (1 + 1) := by simp [f0]

lemma hnonneg0 : ∀ i, 1 ≤ i → i ≤ 1 + 1 → ∀ᵐ t ∂(ν0 i), 0 ≤ t := by
  intro i _ _
  exact ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ht.1)

lemma hcont0 : ∀ i, 1 ≤ i → i ≤ 1 + 1 → NullSingletonClass (ν0 i) := by
  intro i _ _
  simp only [ν0]; infer_instance

lemma fill_pre (θ : ℕ → ℝ) : fillEvent θ 1 = (fun z : ℕ → ℝ => z 1) ⁻¹' Set.Ioi (θ 1) := by
  ext x; rw [fill_iff]; rfl

lemma pU_half : (ν0 1).real (Set.Ioi (1 / 2)) = 1 / 2 := by
  have h1 := pU_upper (1 / 2) (by norm_num)
  have h2 := pU_lower (1 / 2) (by norm_num)
  rw [max_eq_left (by norm_num)] at h1
  rw [max_eq_left (by norm_num)] at h2
  linarith

lemma hopt0 : ∀ i, 1 ≤ i → i ≤ 1 → (flightLaw ν0).real (fillEvent θs i) = ratio f0 (i + 1) := by
  intro i h1 h2
  obtain rfl : i = 1 := by omega
  rw [fill_pre, law1 _ measurableSet_Ioi, ratio2]
  exact pU_half

lemma hA1_0 : ∃ Cb : ℝ, ∀ i, 1 ≤ i → i ≤ 1 + 1 → ∀ᵐ t ∂(ν0 i), t < Cb :=
  ⟨2, fun i _ _ => ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => by linarith [ht.2])⟩

lemma meanAdj_eq (t : ℝ) :
    meanAdj f0 ν0 (Function.update θs 1 t) 1 = 1 / 2 - (ν0 1).real (Set.Ioi t) := by
  simp only [meanAdj]
  rw [fill_pre, law1 _ measurableSet_Ioi, ratio2, Function.update_self]

lemma hA2_0 : ∀ R > 0, ∃ δ > 0, ∀ i, 1 ≤ i → i ≤ 1 → ∀ t : ℝ, |t - θs i| ≤ R →
      δ * (t - θs i) ^ 2 ≤ (t - θs i) * meanAdj f0 ν0 (Function.update θs i t) i := by
  intro R hR
  refine ⟨min 1 (1 / (2 * R)), lt_min one_pos (by positivity), ?_⟩
  intro i h1 h2 t ht
  obtain rfl : i = 1 := by omega
  rw [meanAdj_eq]
  simp only [θs] at ht ⊢
  set δ := min 1 (1 / (2 * R))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδR : δ * R ≤ 1 / 2 := by
    calc δ * R ≤ 1 / (2 * R) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
      _ = 1 / 2 := by field_simp
  have hlo := abs_le.1 ht
  set p := (ν0 1).real (Set.Ioi t)
  rcases le_or_gt (1 / 2) t with htx | htx
  · have hp : p ≤ max (1 - t) 0 := pU_upper t (by linarith)
    have hgoal : δ * (t - 1 / 2) ≤ 1 / 2 - p := by
      rcases le_or_gt t 1 with ht1 | ht1
      · rw [max_eq_left (by linarith)] at hp; nlinarith
      · rw [max_eq_right (by linarith)] at hp; nlinarith
    nlinarith
  · have hp : 1 - max t 0 ≤ p := pU_lower t (by linarith)
    have hgoal : 1 / 2 - p ≤ δ * (t - 1 / 2) := by
      rcases le_or_gt 0 t with ht0 | ht0
      · rw [max_eq_left ht0] at hp; nlinarith
      · rw [max_eq_right ht0.le] at hp; nlinarith
    nlinarith

lemma hA3_0 : ∃ L : ℝ, ∀ i, 1 ≤ i → i ≤ 1 → ∀ x y : ℝ,
      |(flightLaw ν0).real {z | partialSum z i < x} - (flightLaw ν0).real {z | partialSum z i < y}|
        ≤ L * |x - y| := by
  refine ⟨1, fun i h1 h2 x y => ?_⟩
  obtain rfl : i = 1 := by omega
  have e : ∀ c : ℝ, {z : ℕ → ℝ | partialSum z 1 < c} = (fun z : ℕ → ℝ => z 1) ⁻¹' Set.Iio c := by
    intro c; ext z; simp [partialSum]
  rw [e, e, law1 _ measurableSet_Iio, law1 _ measurableSet_Iio, one_mul]
  rcases le_total y x with hxy | hxy
  · have := pIio_le x y hxy
    have := pIio_mono x y hxy
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · have := pIio_le y x hxy
    have := pIio_mono y x hxy
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- The rate conclusion fails for the instance. -/
lemma no_rate (β : ℕ) (hβ : 0 < β) (C : ℝ)
    (h : ∀ n : ℕ, a n ≤ C * γ0 (n + 1) ^ β) : False := by
  have hγ : ∀ n, γ0 (n + 1) ^ β ≤ γ0 (n + 1) := by
    intro n
    have h1 : γ0 (n + 1) ≤ 1 := (γ0_le n).trans (by norm_num)
    calc γ0 (n + 1) ^ β ≤ γ0 (n + 1) ^ 1 := pow_le_pow_of_le_one (γ0_nonneg _) h1 hβ
      _ = _ := pow_one _
  have hC : 0 < C := by
    have h0 := h 0
    rw [a_zero] at h0
    by_contra hc
    push Not at hc
    have : 0 ≤ γ0 (0 + 1) ^ β := pow_nonneg (γ0_nonneg _) _
    nlinarith
  set N : ℕ := ⌈C ^ 2⌉₊ + 1
  have hN1 : 1 ≤ N := by omega
  have hNr : C ^ 2 < (N : ℝ) := by
    have := Nat.le_ceil (C ^ 2)
    simp only [N]; push_cast; linarith
  have hlow := lower N hN1
  have hup : a N ≤ C * (1 / (4 * ((N : ℝ) + 1))) := by
    have := h N
    rw [← γ0_succ]
    exact this.trans (mul_le_mul_of_nonneg_left (hγ N) hC.le)
  have ha := a_nonneg N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsq : a N ^ 2 ≤ (C * (1 / (4 * ((N : ℝ) + 1)))) ^ 2 := pow_le_pow_left₀ ha hup 2
  have : 4 * (N : ℝ) * (C * (1 / (4 * ((N : ℝ) + 1)))) ^ 2 < 1 := by
    rw [show 4 * (N : ℝ) * (C * (1 / (4 * ((N : ℝ) + 1)))) ^ 2
        = C ^ 2 * N / (4 * (N + 1) ^ 2) by field_simp]
    rw [div_lt_one (by positivity)]
    nlinarith
  nlinarith

end APDisproof

open AdaptiveProtection.Convergence in
theorem solution : ¬ (∀ (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i)
    (hfpos : 0 < f (k + 1))
    (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hnonneg : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), 0 ≤ t)
    (hcont : ∀ i, 1 ≤ i → i ≤ k + 1 → NullSingletonClass (ν i))
    (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (θ₁ θstar : ℕ → ℝ)
    (hopt : ∀ i, 1 ≤ i → i ≤ k → (flightLaw ν).real (fillEvent θstar i) = ratio f (i + 1))
    (hA1 : ∃ Cb : ℝ, ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), t < Cb)
    (hA2 : ∀ R > 0, ∃ δ > 0, ∀ i, 1 ≤ i → i ≤ k → ∀ t : ℝ, |t - θstar i| ≤ R →
      δ * (t - θstar i) ^ 2 ≤ (t - θstar i) * meanAdj f ν (Function.update θstar i t) i)
    (hA3 : ∃ L : ℝ, ∀ i, 1 ≤ i → i ≤ k → ∀ x y : ℝ,
      |(flightLaw ν).real {z | partialSum z i < x} - (flightLaw ν).real {z | partialSum z i < y}|
        ≤ L * |x - y|),
    (∀ᵐ ω ∂(pathLaw ν),
        Tendsto (fun n => iterate f k (stepSize A B) θ₁ ω n 1) atTop (𝓝 (θstar 1))) ∧
    (∃ β > 0, ∃ C : ℝ, ∀ n : ℕ,
        Integrable (fun ω => (iterate f k (stepSize A B) θ₁ ω n 1 - θstar 1) ^ 2) (pathLaw ν) ∧
        ∫ ω, (iterate f k (stepSize A B) θ₁ ω n 1 - θstar 1) ^ 2 ∂(pathLaw ν)
          ≤ C * stepSize A B (n + 1) ^ β)) := by
  intro H
  have := @H 1 le_rfl APDisproof.f0 APDisproof.hf0 APDisproof.hfpos0 APDisproof.ν0
    APDisproof.inst_prob APDisproof.hnonneg0 APDisproof.hcont0 (1 / 4) 0 (by norm_num) le_rfl
    APDisproof.θ0 APDisproof.θs APDisproof.hopt0 APDisproof.hA1_0 APDisproof.hA2_0
    APDisproof.hA3_0
  obtain ⟨_, β, hβ, C, hC⟩ := this
  exact APDisproof.no_rate β hβ C (fun n => (hC n).2)
