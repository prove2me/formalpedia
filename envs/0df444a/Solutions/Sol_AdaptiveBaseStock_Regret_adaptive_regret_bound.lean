-- Prove2me | solution 1 for AdaptiveBaseStock.Regret.adaptive_regret_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:59:41.747875+00:00
-- url     : https://prove2.me/submissions/c3bfa254-8337-4800-a5a7-eb1ae90f3316
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm
import Theorems.Thm_AdaptiveBaseStock_Regret_level_regret_bound
import Theorems.Thm_AdaptiveBaseStock_Regret_transient_regret_bound
import Theorems.Thm_AdaptiveBaseStock_Regret_cycle_count_bounds


open MeasureTheory ProbabilityTheory AdaptiveBaseStock.Regret

namespace ABSAux

variable {τ : ℕ}

lemma extPipe_cont (i : ℕ) :
    Continuous (fun q : ℝ × (Fin (τ - 1) → ℝ) => extPipe (τ := τ) q.1 q.2 i) := by
  unfold extPipe
  split_ifs with h1 h2
  · fun_prop
  · exact (continuous_apply _).comp continuous_snd
  · fun_prop

lemma step_cont : Continuous (fun z : ℝ × ℝ × InvVec τ => step z.1 z.2.1 z.2.2) := by
  have hQ : Continuous (fun z : ℝ × ℝ × InvVec τ => orderQty z.1 z.2.2) := by
    unfold orderQty position; fun_prop
  unfold step
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi (fun i => ?_)
    exact (extPipe_cont (τ := τ) i.val).comp (hQ.prodMk (by fun_prop))
  · exact (by fun_prop : Continuous fun z : ℝ × ℝ × InvVec τ => max (z.2.2.2 - z.2.1) 0).add
      ((extPipe_cont (τ := τ) (τ - 1)).comp (hQ.prodMk (by fun_prop)))

lemma run_cont (t : ℕ) :
    Continuous (fun z : ℝ × InvVec τ × (ℕ → ℝ) => run (fun _ => z.1) z.2.1 z.2.2 t) := by
  induction t with
  | zero => simp only [run]; fun_prop
  | succ t ih =>
    simp only [run]
    exact step_cont.comp (continuous_fst.prodMk (((continuous_apply t).comp
      (continuous_snd.comp continuous_snd)).prodMk ih))

lemma cycleStates_cont (n₀ j : ℕ) :
    Continuous (fun z : ℝ × InvVec τ × (ℕ → ℝ) => cycleStates z.1 z.2.1 z.2.2 n₀ j) := by
  unfold cycleStates
  have hs : Continuous (fun z : ℝ × InvVec τ × (ℕ → ℝ) =>
      (z.1, z.2.1, fun j => z.2.2 (n₀ + j))) := by
    refine continuous_fst.prodMk (continuous_fst.comp continuous_snd |>.prodMk ?_)
    exact continuous_pi (fun j => (continuous_apply _).comp (continuous_snd.comp continuous_snd))
  exact (run_cont j).comp hs

lemma derivSeq_meas {δ : Type*} [MeasurableSpace δ] (I dem : δ → ℕ → ℝ)
    (hI : ∀ j, Measurable fun z => I z j) (hd : ∀ j, Measurable fun z => dem z j) (m : ℕ) :
    Measurable fun z => derivSeq τ (I z) (dem z) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : (fun z => derivSeq τ (I z) (dem z) m) = fun z => 1 - ∑ ℓ : Fin m,
        (if m ≤ ℓ.val + τ then derivSeq τ (I z) (dem z) ℓ.val *
          (if I z ℓ.val ≤ dem z ℓ.val then 1 else 0) else 0) := by
      funext z; rw [derivSeq]
    rw [e]
    refine measurable_const.sub (Finset.measurable_sum _ (fun ℓ _ => ?_))
    split_ifs with hm
    · exact (ih ℓ.val ℓ.isLt).mul
        (Measurable.ite (measurableSet_le (hI _) (hd _)) measurable_const measurable_const)
    · exact measurable_const

lemma gradEst_meas (p : AdaptiveParams τ) (k n₀ : ℕ) :
    Measurable (fun z : ℝ × InvVec τ × (ℕ → ℝ) => gradEst p k z.1 z.2.1 z.2.2 n₀) := by
  unfold gradEst
  have hI : ∀ j, Measurable fun z : ℝ × InvVec τ × (ℕ → ℝ) =>
      (cycleStates z.1 z.2.1 z.2.2 n₀ j).2 :=
    fun j => (continuous_snd.comp (cycleStates_cont n₀ j)).measurable
  have hd : ∀ j, Measurable fun z : ℝ × InvVec τ × (ℕ → ℝ) => z.2.2 (n₀ + j) :=
    fun j => (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
  refine Measurable.ite ?_ (Measurable.ite ?_ measurable_const measurable_const) measurable_const
  · exact measurableSet_eq_fun (derivSeq_meas (τ := τ) _ _ hI hd _) measurable_const
  · exact measurableSet_lt (hd _) (hI _)

lemma cycleState_meas (p : AdaptiveParams τ) (n : ℕ) :
    Measurable (fun d : ℕ → ℝ => cycleState p d n) := by
  induction n with
  | zero => simp only [cycleState]; exact measurable_const
  | succ n ih =>
    simp only [cycleState, cycleUpdate]
    have hz : Measurable (fun d : ℕ → ℝ => ((cycleState p d n).1, (cycleState p d n).2, d)) :=
      (measurable_fst.comp ih).prodMk ((measurable_snd.comp ih).prodMk measurable_id)
    refine Measurable.prodMk ?_ ?_
    · unfold proj
      have := (gradEst_meas p (n + 1) (periodsUpTo p.β n)).comp hz
      exact measurable_const.max (((measurable_fst.comp ih).sub
        (measurable_const.mul this)).min measurable_const)
    · exact (cycleStates_cont (τ := τ) _ _).measurable.comp hz

lemma onHand_meas (p : AdaptiveParams τ) (k j : ℕ) :
    Measurable (fun d : ℕ → ℝ => onHand p d k j) := by
  unfold onHand
  have ih := cycleState_meas p (k - 1)
  have hz : Measurable (fun d : ℕ → ℝ =>
      ((cycleState p d (k - 1)).1, (cycleState p d (k - 1)).2, d)) :=
    (measurable_fst.comp ih).prodMk ((measurable_snd.comp ih).prodMk measurable_id)
  exact (continuous_snd.comp (cycleStates_cont (τ := τ) _ j)).measurable.comp hz

lemma level_meas (p : AdaptiveParams τ) (k : ℕ) :
    Measurable (fun d : ℕ → ℝ => level p d k) :=
  measurable_fst.comp (cycleState_meas p (k - 1))


/-! ### periodCost -/

section PC
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D₀ : Ω → ℝ)

lemma neg_int [IsFiniteMeasure P] (hD : Integrable D₀ P) (y : ℝ) :
    Integrable (fun ω => max (D₀ ω - y) 0) P :=
  (hD.sub (integrable_const y)).pos_part

lemma mono1 [IsFiniteMeasure P] (hD : Integrable D₀ P) :
    Monotone (fun y => ∫ ω, max (y - D₀ ω) 0 ∂P) := by
  intro y y' hy
  exact integral_mono ((integrable_const y).sub hD).pos_part
    ((integrable_const y').sub hD).pos_part
    (fun ω => max_le_max (by linarith) le_rfl)

lemma anti2 [IsFiniteMeasure P] (hD : Integrable D₀ P) :
    Antitone (fun y => ∫ ω, max (D₀ ω - y) 0 ∂P) := by
  intro y y' hy
  exact integral_mono (hD.sub (integrable_const y')).pos_part
    (hD.sub (integrable_const y)).pos_part
    (fun ω => max_le_max (by linarith) le_rfl)

lemma periodCost_meas [IsFiniteMeasure P] (hD : Integrable D₀ P) (h b : ℝ) :
    Measurable (fun y => periodCost P D₀ h b y) := by
  unfold periodCost
  exact (measurable_const.mul (mono1 P D₀ hD).measurable).add
    (measurable_const.mul (anti2 P D₀ hD).measurable)

lemma periodCost_bounds [IsFiniteMeasure P] (hD : Integrable D₀ P) (h b : ℝ) (hh : 0 ≤ h)
    (hb : 0 ≤ b) (M y : ℝ) (hy0 : 0 ≤ y) (hyM : y ≤ M) :
    0 ≤ periodCost P D₀ h b y ∧
      periodCost P D₀ h b y ≤ h * ∫ ω, max (M - D₀ ω) 0 ∂P + b * ∫ ω, max (D₀ ω - 0) 0 ∂P := by
  unfold periodCost
  have i1 : 0 ≤ ∫ ω, max (y - D₀ ω) 0 ∂P := integral_nonneg (fun _ => le_max_right _ _)
  have i2 : 0 ≤ ∫ ω, max (D₀ ω - y) 0 ∂P := integral_nonneg (fun _ => le_max_right _ _)
  have m1 := mono1 P D₀ hD hyM
  have m2 := anti2 P D₀ hD hy0
  simp only at m1 m2
  constructor
  · positivity
  · exact add_le_add (mul_le_mul_of_nonneg_left m1 hh) (mul_le_mul_of_nonneg_left m2 hb)

end PC

/-! ### invariants -/

lemma pipe_sum (Q : ℝ) (p : Fin (τ - 1) → ℝ) :
    extPipe (τ := τ) Q p (τ - 1) + ∑ i : Fin (τ - 1), extPipe (τ := τ) Q p i.val
      = Q + ∑ i, p i := by
  set g : ℕ → ℝ := fun i => if h : i < τ - 1 then p ⟨i, h⟩ else 0 with hg
  have e1 : ∑ i, p i = ∑ i ∈ Finset.range (τ - 1), g i := by
    rw [← Fin.sum_univ_eq_sum_range g]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hg, i.isLt]
  have e2 : ∀ i, extPipe (τ := τ) Q p (i + 1) = g i := by
    intro i; simp [extPipe, hg]
  rw [Fin.sum_univ_eq_sum_range (fun i => extPipe (τ := τ) Q p i) (τ - 1), add_comm,
    ← Finset.sum_range_succ, Finset.sum_range_succ', e1]
  simp only [e2]
  have : extPipe (τ := τ) Q p 0 = Q := by simp [extPipe]
  rw [this, add_comm]

lemma extPipe_nonneg (Q : ℝ) (p : Fin (τ - 1) → ℝ) (hQ : 0 ≤ Q) (hp : ∀ i, 0 ≤ p i) (i : ℕ) :
    0 ≤ extPipe (τ := τ) Q p i := by
  unfold extPipe; split_ifs
  · exact hQ
  · exact hp _
  · exact le_rfl

lemma step_inv (S d : ℝ) (x : InvVec τ) (hx : IsNonneg x) (hd : 0 ≤ d) :
    IsNonneg (step S d x) ∧ position (step S d x) ≤ max S (position x) := by
  have hQ : 0 ≤ orderQty S x := le_max_right _ _
  constructor
  · refine ⟨fun i => extPipe_nonneg _ _ hQ hx.1 _, ?_⟩
    exact add_nonneg (le_max_right _ _) (extPipe_nonneg _ _ hQ hx.1 _)
  · have hpos : position (step S d x) = max (x.2 - d) 0 + (orderQty S x + ∑ i, x.1 i) := by
      unfold position step
      simp only
      linarith [pipe_sum (τ := τ) (orderQty S x) x.1]
    rw [hpos]
    have h1 : max (x.2 - d) 0 ≤ x.2 := max_le (by linarith) hx.2
    have h2 : orderQty S x + position x = max S (position x) := by
      unfold orderQty
      rcases le_total S (position x) with h | h
      · rw [max_eq_right (by linarith), max_eq_right h]; ring
      · rw [max_eq_left (by linarith), max_eq_left h]; ring
    unfold position at h2 ⊢
    linarith

lemma onHand_le_pos (x : InvVec τ) (hx : IsNonneg x) : x.2 ≤ position x := by
  unfold position
  have : 0 ≤ ∑ i, x.1 i := Finset.sum_nonneg (fun i _ => hx.1 i)
  linarith

lemma run_inv (S M : ℝ) (hS : S ≤ M) (x : InvVec τ) (hx : IsNonneg x) (hxM : position x ≤ M)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (t : ℕ) :
    IsNonneg (run (fun _ => S) x d t) ∧ position (run (fun _ => S) x d t) ≤ M := by
  induction t with
  | zero => exact ⟨hx, hxM⟩
  | succ t ih =>
    simp only [run]
    obtain ⟨h1, h2⟩ := step_inv S (d t) _ ih.1 (hd t)
    exact ⟨h1, h2.trans (max_le hS ih.2)⟩

lemma cycleState_inv (p : AdaptiveParams τ) (hle : p.Mlo ≤ p.Mhi)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    (cycleState p d n).1 ∈ Set.Icc p.Mlo p.Mhi ∧ IsNonneg (cycleState p d n).2 ∧
      position (cycleState p d n).2 ≤ p.Mhi := by
  induction n with
  | zero => exact ⟨hS₁, hx₁, hx₁M⟩
  | succ n ih =>
    simp only [cycleState, cycleUpdate]
    refine ⟨⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩, ?_⟩
    exact run_inv _ _ ih.1.2 _ ih.2.1 ih.2.2 (fun i => d (periodsUpTo p.β n + i))
      (fun i => hd _) _

lemma onHand_bounds (p : AdaptiveParams τ) (hle : p.Mlo ≤ p.Mhi)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (k j : ℕ) :
    0 ≤ onHand p d k j ∧ onHand p d k j ≤ p.Mhi := by
  have ih := cycleState_inv p hle hS₁ hx₁ hx₁M d hd (k - 1)
  have := run_inv _ _ ih.1.2 _ ih.2.1 ih.2.2 (fun i => d (periodsUpTo p.β (k - 1) + i))
    (fun i => hd _) j
  unfold onHand cycleStates
  exact ⟨this.1.2, (onHand_le_pos _ this.1).trans this.2⟩

/-! ### baseStockCost -/

section BSC
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ → Ω → ℝ)

lemma bsc_meas (hD : IsDemandModel P D) (h b : ℝ) :
    Measurable (fun S => baseStockCost P D τ h b S) := by
  unfold baseStockCost
  refine Measurable.limsup (f := fun T S => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
    ∫ ω, periodCost P (D 0) h b (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P) ?_
  intro T
  refine measurable_const.mul (Finset.measurable_sum _ (fun t _ => ?_))
  have hm : Measurable (fun q : ℝ × Ω => ((q.1, (0 : InvVec τ), fun n => D n q.2) :
      ℝ × InvVec τ × (ℕ → ℝ))) :=
    measurable_fst.prodMk (measurable_const.prodMk
      (measurable_pi_lambda _ (fun n => (hD.measurable n).comp measurable_snd)))
  have hf : StronglyMeasurable (fun q : ℝ × Ω =>
      periodCost P (D 0) h b (run (τ := τ) (fun _ => q.1) 0 (fun n => D n q.2) t).2) :=
    ((periodCost_meas P (D 0) hD.integrable h b).comp
      (measurable_snd.comp ((run_cont (τ := τ) t).measurable.comp hm))).stronglyMeasurable
  exact hf.integral_prod_right'.measurable

lemma bsc_bounds (hD : IsDemandModel P D) (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (M S : ℝ)
    (hS0 : 0 ≤ S) (hSM : S ≤ M) :
    0 ≤ baseStockCost P D τ h b S ∧
      baseStockCost P D τ h b S ≤
        h * ∫ ω, max (M - D 0 ω) 0 ∂P + b * ∫ ω, max (D 0 ω - 0) 0 ∂P := by
  set Cb := h * ∫ ω, max (M - D 0 ω) 0 ∂P + b * ∫ ω, max (D 0 ω - 0) 0 ∂P
  have hpc : ∀ ω t, 0 ≤ periodCost P (D 0) h b (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2
      ∧ periodCost P (D 0) h b (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ≤ Cb := by
    intro ω t
    have h0 : IsNonneg (0 : InvVec τ) := ⟨fun _ => le_rfl, le_rfl⟩
    have hp0 : position (0 : InvVec τ) ≤ S := by simp [position]; exact hS0
    have := run_inv S S le_rfl 0 h0 hp0 (fun n => D n ω) (fun n => hD.nonneg n ω) t
    exact periodCost_bounds P (D 0) hD.integrable h b hh hb M _ this.1.2
      ((onHand_le_pos _ this.1).trans (this.2.trans hSM))
  have hCb : 0 ≤ Cb := by
    have i1 : 0 ≤ ∫ ω, max (M - D 0 ω) 0 ∂P := integral_nonneg (fun _ => le_max_right _ _)
    have i2 : 0 ≤ ∫ ω, max (D 0 ω - 0) 0 ∂P := integral_nonneg (fun _ => le_max_right _ _)
    positivity
  have hint : ∀ t, 0 ≤ ∫ ω, periodCost P (D 0) h b
        (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P ∧
      ∫ ω, periodCost P (D 0) h b (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P ≤ Cb := by
    intro t
    refine ⟨integral_nonneg (fun ω => (hpc ω t).1), ?_⟩
    calc _ ≤ ∫ _ω, Cb ∂P := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => (hpc ω t).1))
            (integrable_const Cb) (Filter.Eventually.of_forall (fun ω => (hpc ω t).2))
      _ = Cb := by simp
  set u : ℕ → ℝ := fun T => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
    ∫ ω, periodCost P (D 0) h b (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P with hu
  have hub : ∀ T, 0 ≤ u T ∧ u T ≤ Cb := by
    intro T
    have hs0 : 0 ≤ ∑ t ∈ Finset.range T, ∫ ω, periodCost P (D 0) h b
        (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P :=
      Finset.sum_nonneg (fun t _ => (hint t).1)
    have hs1 : ∑ t ∈ Finset.range T, ∫ ω, periodCost P (D 0) h b
        (run (τ := τ) (fun _ => S) 0 (fun n => D n ω) t).2 ∂P ≤ T * Cb := by
      calc _ ≤ ∑ t ∈ Finset.range T, Cb := Finset.sum_le_sum (fun t _ => (hint t).2)
        _ = T * Cb := by simp
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos T with hT | hT
    · simp [hu, hT, hCb]
    · have hTr : (0 : ℝ) < T := by exact_mod_cast hT
      simp only [hu]
      rw [inv_mul_le_iff₀ hTr]; exact hs1
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of ⟨Cb, fun T => (hub T).2⟩
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop (fun T => (hub T).1)
  unfold baseStockCost
  refine ⟨Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall (fun T => (hub T).1)) hbdd,
    Filter.limsup_le_of_le hcob (Filter.Eventually.of_forall (fun T => (hub T).2))⟩

end BSC

/-! ### decomposition `Λ = Λ₁ + Λ₂` -/

theorem regret_decomp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (p : AdaptiveParams τ) (hh : 0 < p.h)
    (hb : 0 < p.b) (Sstar : ℝ) (hMlo : 0 ≤ p.Mlo) (hle : p.Mlo ≤ p.Mhi)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (L : ℕ) :
    regret P D p Sstar L = regretLevel P D p Sstar L + regretTransient P D p L := by
  have hdm : Measurable (fun ω => fun n => D n ω) := measurable_pi_lambda _ hD.measurable
  have hdn : ∀ ω n, 0 ≤ D n ω := fun ω n => hD.nonneg n ω
  set Cb := p.h * ∫ ω, max (p.Mhi - D 0 ω) 0 ∂P + p.b * ∫ ω, max (D 0 ω - 0) 0 ∂P
  have ha : ∀ k j, Integrable
      (fun ω => periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j)) P := by
    intro k j
    refine Integrable.of_bound (((periodCost_meas P (D 0) hD.integrable _ _).comp
      ((onHand_meas p k j).comp hdm)).aestronglyMeasurable) Cb
      (Filter.Eventually.of_forall (fun ω => ?_))
    obtain ⟨h0, h1⟩ := onHand_bounds p hle hS₁ hx₁ hx₁M _ (hdn ω) k j
    obtain ⟨c0, c1⟩ := periodCost_bounds P (D 0) hD.integrable p.h p.b hh.le hb.le p.Mhi _ h0 h1
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hB : ∀ k, Integrable
      (fun ω => baseStockCost P D τ p.h p.b (level p (fun n => D n ω) k)) P := by
    intro k
    refine Integrable.of_bound (((bsc_meas P D hD _ _).comp
      ((level_meas p k).comp hdm)).aestronglyMeasurable) Cb
      (Filter.Eventually.of_forall (fun ω => ?_))
    obtain ⟨h0, h1⟩ := (cycleState_inv p hle hS₁ hx₁ hx₁M _ (hdn ω) (k - 1)).1
    obtain ⟨c0, c1⟩ := bsc_bounds P D hD p.h p.b hh.le hb.le p.Mhi
      (level p (fun n => D n ω) k) (hMlo.trans h0) h1
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hab : ∀ k j, Integrable (fun ω => periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j)
        - baseStockCost P D τ p.h p.b (level p (fun n => D n ω) k)) P :=
    fun k j => (ha k j).sub (hB k)
  have hk : ∀ k, ∫ ω, ∑ j ∈ Finset.range (cycleLen p.β k),
      (periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j)
        - baseStockCost P D τ p.h p.b (level p (fun n => D n ω) k)) ∂P
      = ∑ j ∈ Finset.range (cycleLen p.β k),
          ∫ ω, periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j) ∂P
        - (cycleLen p.β k : ℝ) * ∫ ω, baseStockCost P D τ p.h p.b (level p (fun n => D n ω) k) ∂P := by
    intro k
    rw [integral_finsetSum _ (fun j _ => hab k j)]
    rw [Finset.sum_congr rfl (fun j _ => integral_sub (ha k j) (hB k)), Finset.sum_sub_distrib]
    simp
  have hk2 : ∫ ω, ∑ k ∈ Finset.Icc 1 L, ∑ j ∈ Finset.range (cycleLen p.β k),
      periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j) ∂P
      = ∑ k ∈ Finset.Icc 1 L, ∑ j ∈ Finset.range (cycleLen p.β k),
          ∫ ω, periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j) ∂P := by
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => ha k j))]
    exact Finset.sum_congr rfl (fun k _ => integral_finsetSum _ (fun j _ => ha k j))
  unfold regret regretLevel regretTransient
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => hab k j)),
    Finset.sum_congr rfl (fun k _ => hk k), hk2]
  have hN : (periodsUpTo p.β L : ℝ) = ∑ k ∈ Finset.Icc 1 L, (cycleLen p.β k : ℝ) := by
    unfold periodsUpTo; push_cast; rfl
  rw [hN, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  have : ∀ k ∈ Finset.Icc 1 L, baseStockCost P D τ p.h p.b Sstar * (cycleLen p.β k : ℝ)
      = (cycleLen p.β k : ℝ) * baseStockCost P D τ p.h p.b Sstar := fun _ _ => mul_comm _ _
  rw [Finset.sum_congr rfl this]
  ring

end ABSAux


namespace ABSAux

lemma pow_scale (β N e : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hN : 1 ≤ N) (_he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ((β + 1) * N) ^ e ≤ 2 * N ^ e := by
  rw [Real.mul_rpow (by linarith) (by linarith)]
  have h1 : (β + 1) ^ e ≤ β + 1 := Real.rpow_le_self_of_one_le (by linarith) he1
  have h2 : 0 ≤ N ^ e := Real.rpow_nonneg (by linarith) e
  nlinarith

lemma div_N (N e : ℝ) (hN : 1 ≤ N) : N ^ e / N = 1 / N ^ (1 - e) := by
  have hN0 : 0 < N := by linarith
  rw [Real.rpow_sub hN0, Real.rpow_one]
  have : 0 < N ^ e := Real.rpow_pos_of_pos hN0 e
  field_simp

/-- `L^a ≤ X^{a/(β+1)}` from `L ≤ X^{1/(β+1)}`. -/
lemma L_pow (L X β a : ℝ) (hL0 : 0 ≤ L) (hX : 0 ≤ X) (_hβ : 0 < β) (ha : 0 ≤ a)
    (hL : L ≤ X ^ (1 / (β + 1))) : L ^ a ≤ X ^ (a / (β + 1)) := by
  calc L ^ a ≤ (X ^ (1 / (β + 1))) ^ a := Real.rpow_le_rpow hL0 hL ha
    _ = X ^ (a / (β + 1)) := by rw [← Real.rpow_mul hX]; ring_nf

end ABSAux

open ABSAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (τ : ℕ) (hτ : 1 ≤ τ) (p : AdaptiveParams τ) (hh : 0 < p.h) (hb : 0 < p.b)
    (hα0 : 0 < p.α) (hα1 : p.α < 1) (hβ0 : 0 < p.β) (hβ1 : p.β < 1)
    (Sstar : ℝ) (hMlo : 0 ≤ p.Mlo) (hlo : p.Mlo ≤ Sstar) (hhi : Sstar ≤ p.Mhi)
    (hγ : 0 < gammaLevel P (D 0) τ p.Mlo)
    (hopt : IsMinOn (baseStockCost P D τ p.h p.b) (Set.Ici 0) Sstar)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (L : ℕ) (hL : 1 ≤ L) :
    regret P D p Sstar L / (periodsUpTo p.β L : ℝ)
      ≤ (p.b + p.h) *
          ((p.Mhi - p.Mlo) *
              (4 / (periodsUpTo p.β L : ℝ) ^ ((1 - p.α) / (1 + p.β))
                + 4 / (1 - p.α) / (periodsUpTo p.β L : ℝ) ^ (p.α / (1 + p.β))
                + 12 * (4 * (τ : ℝ)) ^ (1 / p.β) * Real.Gamma (1 / p.β) * (1 / p.β)
                    / (Real.log (1 / nu P (D 0) τ p.Mlo p.Mhi)) ^ (1 / p.β)
                    / (periodsUpTo p.β L : ℝ) ^ (1 / (1 + p.β)))
            + p.Mhi * (24 * (τ : ℝ) / Real.log (1 / nu P (D 0) τ p.Mlo p.Mhi))
                / (periodsUpTo p.β L : ℝ) ^ (p.β / (1 + p.β))) := by
  have hdec : regret P D p Sstar L = regretLevel P D p Sstar L + regretTransient P D p L :=
    regret_decomp P D hD p hh hb Sstar hMlo (hlo.trans hhi) hS₁ hx₁ hx₁M L
  have h14 := level_regret_bound P D hD hinf τ hτ p hh hb hα0 hα1 hβ0 hβ1 Sstar hMlo hlo hhi hγ
    hopt hS₁ hx₁ hx₁M L hL
  have h15 := transient_regret_bound P D hD hinf τ hτ p hh hb hα0 hα1 hβ0 hβ1 Sstar hMlo hlo hhi hγ
    hopt hS₁ hx₁ hx₁M L hL
  obtain ⟨hi, -, hiii, -⟩ := cycle_count_bounds p.β hβ0 hβ1 L hL
  set α := p.α
  set β := p.β
  set N : ℝ := (periodsUpTo β L : ℝ) with hNdef
  set T : ℝ := (cycleLen β L : ℝ) with hTdef
  set ν := nu P (D 0) τ p.Mlo p.Mhi with hνdef
  set ℓ := Real.log (1 / ν) with hℓdef
  set K := (4 * (τ : ℝ)) ^ (1 / β) * Real.Gamma (1 / β) * (1 / β) / ℓ ^ (1 / β) with hKdef
  -- basic facts
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]; norm_cast
    unfold cycleLen
    apply Nat.one_le_iff_ne_zero.mpr
    intro h0
    rw [Nat.ceil_eq_zero] at h0
    have : (0:ℝ) < (L:ℝ) ^ β := Real.rpow_pos_of_pos (by exact_mod_cast hL) β
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]
    have : cycleLen β L ≤ periodsUpTo β L := by
      unfold periodsUpTo
      exact Finset.single_le_sum (f := fun k => cycleLen β k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨hL, le_rfl⟩)
    have : (cycleLen β L : ℝ) ≤ (periodsUpTo β L : ℝ) := by exact_mod_cast this
    linarith
  have hN0 : 0 < N := by linarith
  have hνpos : 0 < ν := lt_of_lt_of_le (Real.exp_pos (-1))
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hνle : ν ≤ 1 := by
    apply max_le
    · have : 0 ≤ gammaLevel P (D 0) τ p.Mlo ^ (2 * τ) := pow_nonneg hγ.le _
      linarith
    · apply max_le (hinf p.Mhi).le
      rw [Real.exp_le_one_iff]; norm_num
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hνpos]; linarith)
  have hK0 : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos (one_div_pos.mpr hβ0)
    have h4 : 0 ≤ (4 * (τ : ℝ)) ^ (1 / β) := Real.rpow_nonneg (by positivity) _
    have h5 : 0 ≤ ℓ ^ (1 / β) := Real.rpow_nonneg hℓ0 _
    have h6 : 0 ≤ 1 / β := by positivity
    positivity
  have hMhi0 : 0 ≤ p.Mhi := by linarith
  have hdM : 0 ≤ p.Mhi - p.Mlo := by linarith
  have hbh : 0 < p.b + p.h := by linarith
  set X : ℝ := (β + 1) * N with hXdef
  have hX0 : 0 < X := by positivity
  have hLr0 : (0 : ℝ) ≤ L := by positivity
  have hβ1' : 0 < β + 1 := by linarith
  -- bound on T
  have hT4 : T ≤ 4 * N ^ (β / (β + 1)) := by
    have := pow_scale β N (β / (β + 1)) hβ0 hβ1 hN1 (by positivity)
      ((div_le_one hβ1').mpr (by linarith))
    linarith
  -- term 1
  have hA1 : T * (L : ℝ) ^ α / 2 / N ≤ 4 / N ^ ((1 - α) / (1 + β)) := by
    have hLa := L_pow L X β α hLr0 hX0.le hβ0 hα0.le hi
    have hcomb : T * (L : ℝ) ^ α ≤ 2 * X ^ ((β + α) / (β + 1)) := by
      have : X ^ ((β + α) / (β + 1)) = X ^ (β / (β + 1)) * X ^ (α / (β + 1)) := by
        rw [← Real.rpow_add hX0]; ring_nf
      rw [this]
      have : 0 ≤ (L : ℝ) ^ α := Real.rpow_nonneg hLr0 _
      have : 0 ≤ X ^ (β / (β + 1)) := Real.rpow_nonneg hX0.le _
      calc T * (L : ℝ) ^ α ≤ (2 * X ^ (β / (β + 1))) * X ^ (α / (β + 1)) :=
            mul_le_mul hiii hLa (by assumption) (by positivity)
        _ = _ := by ring
    have hsc := pow_scale β N ((β + α) / (β + 1)) hβ0 hβ1 hN1 (by positivity)
      ((div_le_one hβ1').mpr (by linarith))
    have hdiv := div_N N ((β + α) / (β + 1)) hN1
    have hexp : 1 - (β + α) / (β + 1) = (1 - α) / (1 + β) := by field_simp; ring
    rw [hexp] at hdiv
    have hpos : 0 < N ^ ((1 - α) / (1 + β)) := Real.rpow_pos_of_pos hN0 _
    calc T * (L : ℝ) ^ α / 2 / N ≤ (2 * N ^ ((β + α) / (β + 1))) / N := by
          apply div_le_div_of_nonneg_right _ hN0.le; linarith
      _ = 2 * (1 / N ^ ((1 - α) / (1 + β))) := by rw [mul_div_assoc, hdiv]
      _ ≤ 4 / N ^ ((1 - α) / (1 + β)) := by
          rw [mul_one_div]; apply div_le_div_of_nonneg_right (by norm_num) hpos.le
  -- term 2
  have hA2 : T * ((L : ℝ) ^ (1 - α) / (2 * (1 - α))) / N ≤ 4 / (1 - α) / N ^ (α / (1 + β)) := by
    have hLa := L_pow L X β (1 - α) hLr0 hX0.le hβ0 (by linarith) hi
    have hcomb : T * (L : ℝ) ^ (1 - α) ≤ 2 * X ^ ((β + 1 - α) / (β + 1)) := by
      have : X ^ ((β + 1 - α) / (β + 1)) = X ^ (β / (β + 1)) * X ^ ((1 - α) / (β + 1)) := by
        rw [← Real.rpow_add hX0]; ring_nf
      rw [this]
      have : 0 ≤ (L : ℝ) ^ (1 - α) := Real.rpow_nonneg hLr0 _
      have : 0 ≤ X ^ (β / (β + 1)) := Real.rpow_nonneg hX0.le _
      calc T * (L : ℝ) ^ (1 - α) ≤ (2 * X ^ (β / (β + 1))) * X ^ ((1 - α) / (β + 1)) :=
            mul_le_mul hiii hLa (by assumption) (by positivity)
        _ = _ := by ring
    have hsc := pow_scale β N ((β + 1 - α) / (β + 1)) hβ0 hβ1 hN1
      (div_nonneg (by linarith) hβ1'.le) ((div_le_one hβ1').mpr (by linarith))
    have hdiv := div_N N ((β + 1 - α) / (β + 1)) hN1
    have hexp : 1 - (β + 1 - α) / (β + 1) = α / (1 + β) := by field_simp; ring
    rw [hexp] at hdiv
    have hpos : 0 < N ^ (α / (1 + β)) := Real.rpow_pos_of_pos hN0 _
    have h1a : 0 < 1 - α := by linarith
    calc T * ((L : ℝ) ^ (1 - α) / (2 * (1 - α))) / N
        = (T * (L : ℝ) ^ (1 - α)) / N / (2 * (1 - α)) := by ring
      _ ≤ (4 * N ^ ((β + 1 - α) / (β + 1))) / N / (2 * (1 - α)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_right _ hN0.le; linarith
      _ = 2 / (1 - α) * (1 / N ^ (α / (1 + β))) := by
          rw [mul_div_assoc, hdiv]; field_simp; ring
      _ ≤ 4 / (1 - α) / N ^ (α / (1 + β)) := by
          rw [mul_one_div]; apply div_le_div_of_nonneg_right _ hpos.le
          apply div_le_div_of_nonneg_right (by norm_num) h1a.le
  -- term 3
  have hA3 : T * (3 * K) / N ≤ 12 * K / N ^ (1 / (1 + β)) := by
    have hdiv := div_N N (β / (β + 1)) hN1
    have hexp : 1 - β / (β + 1) = 1 / (1 + β) := by field_simp; ring
    rw [hexp] at hdiv
    calc T * (3 * K) / N ≤ (4 * N ^ (β / (β + 1))) * (3 * K) / N := by
          apply div_le_div_of_nonneg_right _ hN0.le
          exact mul_le_mul_of_nonneg_right hT4 (by positivity)
      _ = 12 * K * (N ^ (β / (β + 1)) / N) := by ring
      _ = 12 * K / N ^ (1 / (1 + β)) := by rw [hdiv]; ring
  -- term 4
  have hA4 : (L : ℝ) * (12 * τ + 1) / N ≤ 24 * τ / N ^ (β / (1 + β)) := by
    have hb1 : (β + 1) ^ (1 / (β + 1)) ≤ 1 + 1 / (β + 1) * β := by
      have := rpow_one_add_le_one_add_mul_self (s := β) (by linarith) (p := 1 / (β + 1))
        (by positivity) ((div_le_one hβ1').mpr (by linarith))
      rw [add_comm] at this; linarith
    have hb2 : 1 / (β + 1) * β ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hβ1']; linarith
    have hLb : (L : ℝ) ≤ 3 / 2 * N ^ (1 / (β + 1)) := by
      have := hi
      rw [Real.mul_rpow hβ1'.le hN0.le] at this
      have : 0 ≤ N ^ (1 / (β + 1)) := Real.rpow_nonneg hN0.le _
      nlinarith
    have hdiv := div_N N (1 / (β + 1)) hN1
    have hexp : 1 - 1 / (β + 1) = β / (1 + β) := by field_simp; ring
    rw [hexp] at hdiv
    have hτr : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
    calc (L : ℝ) * (12 * τ + 1) / N ≤ (3 / 2 * N ^ (1 / (β + 1))) * (12 * τ + 1) / N := by
          apply div_le_div_of_nonneg_right _ hN0.le
          exact mul_le_mul_of_nonneg_right hLb (by positivity)
      _ = (3 / 2 * (12 * τ + 1)) * (N ^ (1 / (β + 1)) / N) := by ring
      _ = (3 / 2 * (12 * τ + 1)) / N ^ (β / (1 + β)) := by rw [hdiv]; ring
      _ ≤ 24 * τ / N ^ (β / (1 + β)) := by
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hN0.le _); linarith
  -- combine
  rw [hdec, add_div]
  have e1 : regretLevel P D p Sstar L / N ≤ (p.Mhi - p.Mlo) * (p.b + p.h) *
      (T * (L : ℝ) ^ α / 2 / N + T * ((L : ℝ) ^ (1 - α) / (2 * (1 - α))) / N
        + T * (3 * K) / N) := by
    calc regretLevel P D p Sstar L / N ≤ ((p.Mhi - p.Mlo) * (p.b + p.h) * T *
          ((L : ℝ) ^ α / 2 + (L : ℝ) ^ (1 - α) / (2 * (1 - α)) + 3 * K)) / N := by
          apply div_le_div_of_nonneg_right _ hN0.le
          exact le_of_le_of_eq h14 (by rw [hKdef]; ring)
      _ = _ := by ring
  have e2 : regretTransient P D p L / N ≤ (p.b + p.h) * p.Mhi / ℓ *
      ((L : ℝ) * (12 * τ + 1) / N) := by
    calc regretTransient P D p L / N ≤ ((p.b + p.h) * p.Mhi * (L : ℝ) * (12 * (τ : ℝ) + 1) / ℓ) / N :=
          div_le_div_of_nonneg_right h15 hN0.le
      _ = _ := by ring
  have c0 : 0 ≤ (p.Mhi - p.Mlo) * (p.b + p.h) := by positivity
  have c1 : 0 ≤ (p.b + p.h) * p.Mhi / ℓ := by positivity
  have f1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA1 hA2) hA3) c0
  have f2 := mul_le_mul_of_nonneg_left hA4 c1
  calc _ ≤ _ := add_le_add (e1.trans f1) (e2.trans f2)
    _ = _ := by rw [hKdef]; ring
