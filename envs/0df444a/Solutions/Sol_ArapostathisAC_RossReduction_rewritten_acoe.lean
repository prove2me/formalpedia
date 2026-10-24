-- Prove2me | solution 1 for ArapostathisAC.RossReduction.rewritten_acoe
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T22:39:49.383249+00:00
-- url     : https://prove2.me/submissions/6c09b496-0809-434e-864f-fc9eb43d04ae

import Init
import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

open MeasureTheory ProbabilityTheory Set Function Preorder MeasurableSpace
open scoped ENNReal
noncomputable section
namespace RossPath
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

instance init_probability {M : CMP A} (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (initMeasure π i) := by
  unfold initMeasure
  exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable

instance path_probability (M : CMP A) (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (pathMeasure M π i) := by
  unfold pathMeasure
  infer_instance

def good (M : CMP A) : Set (ℕ × A) := {p | p.2 ∈ M.U p.1}

theorem good_measurable (M : CMP A) : MeasurableSet (good M) := by
  have he : good M = ⋃ i : ℕ, ({i} : Set ℕ) ×ˢ M.U i := by
    ext p
    simp [good]
  rw [he]
  exact MeasurableSet.iUnion fun i => (measurableSet_singleton i).prod (M.U_compact i).isClosed.measurableSet

theorem initial_good (M : CMP A) (π : Policy M) (i : ℕ) :
    ∀ᵐ p ∂initMeasure π i, p ∈ good M := by
  apply ae_iff.mpr
  change initMeasure π i (good M)ᶜ = 0
  rw [initMeasure,Measure.map_apply (show Measurable (fun a : A => (i,a)) from
    measurable_const.prodMk measurable_id) (good_measurable M).compl]
  exact π.adm 0 (fun j => j.elim0,i)

theorem step_good (M : CMP A) (π : Policy M) (t : ℕ)
    (hist : Π _ : Finset.Iic t, ℕ × A) :
    ∀ᵐ p ∂stepKernel M π t hist, p ∈ good M := by
  apply Kernel.ae_compProd_of_ae_ae (good_measurable M)
  apply Filter.Eventually.of_forall
  intro j
  apply ae_iff.mpr
  exact π.adm (t+1) (ArapostathisAC.VanishingDiscount.histFin t hist,j)

theorem initial_marginal (M : CMP A) (π : Policy M) (i : ℕ) :
    (pathMeasure M π i).map (fun ω => ω 0) = initMeasure π i := by
  let κ := stepKernel M π
  have he : (Kernel.traj (X := fun _ => ℕ × A) κ 0).map (fun ω => ω 0) =
      Kernel.deterministic (fun h : Π _ : Finset.Iic 0, ℕ × A => h ⟨0,by simp⟩)
        (measurable_pi_apply _) := by
    have hf : (fun ω : ℕ → ℕ × A => ω 0) =
        (fun h : Π _ : Finset.Iic 0, ℕ × A => h ⟨0,by simp⟩) ∘ frestrictLe 0 := rfl
    rw [hf,Kernel.map_comp_right _ (measurable_frestrictLe 0) (by fun_prop),
      Kernel.traj_map_frestrictLe_of_le (le_refl 0),Kernel.deterministic_map _ (measurable_pi_apply _)]
    rfl
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop),he,Measure.deterministic_comp_eq_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  convert (Measure.map_id (μ := initMeasure π i)) using 1
  ext a
  rfl

#print axioms initial_marginal
#print axioms step_good
end RossPath

open MeasureTheory ProbabilityTheory Set Function Preorder MeasurableSpace
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RossPath
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

theorem admissible_time (M : CMP A) (π : Policy M) (i t : ℕ) :
    ∀ᵐ ω ∂pathMeasure M π i, (ω t).2 ∈ M.U (ω t).1 := by
  cases t with
  | zero =>
      have h := initial_good M π i
      rw [← initial_marginal M π i] at h
      exact (ae_map_iff (μ := pathMeasure M π i) (f := fun ω : ℕ → ℕ × A => ω 0) (p := fun p : ℕ × A => p ∈ good M) (measurable_pi_apply 0).aemeasurable (good_measurable M)).mp h
  | succ t =>
      have h : ∀ᵐ p ∂((pathMeasure M π i).map (frestrictLe t) ⊗ₘ stepKernel M π t),
          p.2 ∈ good M := by
        apply Measure.ae_compProd_of_ae_ae (measurable_snd (good_measurable M))
        exact Filter.Eventually.of_forall fun hist => step_good M π t hist
      have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => ℕ × A) (μ₀ := initMeasure π i) (κ := stepKernel M π) (a := t)
      change (pathMeasure M π i).map (frestrictLe t) ⊗ₘ stepKernel M π t = _ at he
      rw [he] at h
      exact (ae_map_iff (μ := pathMeasure M π i) (f := fun ω : ℕ → ℕ × A => (frestrictLe t ω,ω (t+1))) (p := fun p : (Π _ : Finset.Iic t, ℕ × A) × (ℕ × A) => p.2 ∈ good M) ((measurable_frestrictLe t).prodMk (measurable_pi_apply (t+1))).aemeasurable (measurable_snd (good_measurable M))).mp h

theorem admissible_path (M : CMP A) (π : Policy M) (i : ℕ) :
    ∀ᵐ ω ∂pathMeasure M π i, ∀ t, (ω t).2 ∈ M.U (ω t).1 :=
  ae_all_iff.mpr (admissible_time M π i)

theorem step_state_lintegral (M : CMP A) (π : Policy M) (t : ℕ)
    (hist : Π _ : Finset.Iic t, ℕ × A) (g : ℕ → ℝ≥0∞) :
    ∫⁻ p, g p.1 ∂stepKernel M π t hist =
      ∫⁻ j,g j ∂M.P (ArapostathisAC.VanishingDiscount.lastPair t hist) := by
  rw [stepKernel,Kernel.lintegral_compProd _ _ _ (f := fun p : ℕ × A => g p.1) ((measurable_of_countable g).comp measurable_fst)]
  simp only [Kernel.comap_apply,lintegral_const,measure_univ,mul_one]

#print axioms admissible_path
#print axioms step_state_lintegral
end RossPath

open MeasureTheory ProbabilityTheory Set Function Preorder MeasurableSpace
open scoped ENNReal
noncomputable section
namespace RossPath
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

theorem cost_bound_nonneg (M : CMP A) (C : ℝ)
    (hc : ∀ i a, a ∈ M.U i → M.c i a ≤ C) : 0 ≤ C := by
  obtain ⟨a,ha⟩ := M.U_nonempty 0
  exact (M.c_nonneg 0 a ha).trans (hc 0 a ha)

theorem discCost_bound (M : CMP A) (π : Policy M) (β C : ℝ)
    (hb : 0 ≤ β) (hb1 : β < 1) (hc : ∀ i a, a ∈ M.U i → M.c i a ≤ C) (i : ℕ) :
    discCost M π β i ≤ ENNReal.ofReal (C / (1-β)) := by
  have hC := cost_bound_nonneg M C hc
  have hs : (∑' t : ℕ, ENNReal.ofReal (β^t*C)) = ENNReal.ofReal (C/(1-β)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (pow_nonneg hb t) hC)
      ((summable_geometric_of_lt_one hb hb1).mul_right C),tsum_mul_right,
      tsum_geometric_of_lt_one hb hb1]
    congr 1
    rw [div_eq_mul_inv,mul_comm]
  unfold discCost
  apply lintegral_le_const
  filter_upwards [admissible_path M π i] with ω hω
  rw [← hs]
  exact ENNReal.tsum_le_tsum fun t => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (hc _ _ (hω t)) (pow_nonneg hb t))

theorem discValue_bound (M : CMP A) (β C : ℝ)
    (hb : 0 ≤ β) (hb1 : β < 1) (hc : ∀ i a, a ∈ M.U i → M.c i a ≤ C) (i : ℕ) :
    discValue M β i ≤ ENNReal.ofReal (C / (1-β)) := by
  classical
  let f : StationaryPolicy M := ⟨fun i => (M.U_nonempty i).choose, fun i => (M.U_nonempty i).choose_spec⟩
  exact (iInf_le _ f.toPolicy).trans (discCost_bound M f.toPolicy β C hb hb1 hc i)

theorem discValue_finite_bounded (M : CMP A) (β C : ℝ)
    (hb : 0 ≤ β) (hb1 : β < 1) (hc : ∀ i a, a ∈ M.U i → M.c i a ≤ C) :
    (∀ i, discValue M β i ≠ ⊤) ∧
      ∀ i, |(discValue M β i).toReal| ≤ C / (1-β) := by
  constructor
  · intro i
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (discValue_bound M β C hb hb1 hc i)
  · intro i
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (discValue_bound M β C hb hb1 hc i)).trans_eq
      (ENNReal.toReal_ofReal (div_nonneg (cost_bound_nonneg M C hc) (sub_pos.mpr hb1).le))

#print axioms discValue_finite_bounded
end RossPath

open MeasureTheory ProbabilityTheory Set Function Preorder MeasurableSpace
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RossPath
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

theorem state_transition (M : CMP A) (π : Policy M) (i t : ℕ) (g : ℕ → ℝ≥0∞) :
    ∫⁻ ω, g (ω (t+1)).1 ∂pathMeasure M π i =
      ∫⁻ ω, ∫⁻ j,g j ∂M.P (ω t) ∂pathMeasure M π i := by
  have hgm : Measurable (fun p : (Π _ : Finset.Iic t, ℕ × A) × (ℕ × A) => g p.2.1) :=
    (measurable_of_countable g).comp (measurable_fst.comp measurable_snd)
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => ℕ × A) (μ₀ := initMeasure π i) (κ := stepKernel M π) (a := t)
  change (pathMeasure M π i).map (frestrictLe t) ⊗ₘ stepKernel M π t = _ at he
  have hi := congrArg (fun μ => ∫⁻ p,g p.2.1 ∂μ) he
  rw [lintegral_map hgm ((measurable_frestrictLe t).prodMk (measurable_pi_apply (t+1))),
    Measure.lintegral_compProd hgm] at hi
  simp only [step_state_lintegral] at hi
  have hm : Measurable (fun hist : Π _ : Finset.Iic t, ℕ × A =>
      ∫⁻ j,g j ∂M.P (ArapostathisAC.VanishingDiscount.lastPair t hist)) :=
    ((measurable_of_countable g).lintegral_kernel (κ := M.P)).comp (measurable_pi_apply _)
  rw [lintegral_map hm (measurable_frestrictLe t)] at hi
  exact hi.symm

#print axioms state_transition
end RossPath

open MeasureTheory ProbabilityTheory Set Function Preorder MeasurableSpace
open scoped ENNReal
noncomputable section
namespace RossPath
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

theorem initial_state_lintegral (M : CMP A) (π : Policy M) (i : ℕ) (g : ℕ → ℝ≥0∞) :
    ∫⁻ ω, g (ω 0).1 ∂pathMeasure M π i = g i := by
  have hm : Measurable (fun p : ℕ × A => g p.1) := (measurable_of_countable g).comp measurable_fst
  rw [← lintegral_map hm (measurable_pi_apply 0),initial_marginal,initMeasure,
    lintegral_map hm (show Measurable (fun a : A => (i,a)) from measurable_const.prodMk measurable_id)]
  simp

theorem discounted_sum (M : CMP A) (π : Policy M) (β : ℝ) (i : ℕ) :
    discCost M π β i =
      ∑' t : ℕ, ∫⁻ ω, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) ∂pathMeasure M π i := by
  apply lintegral_tsum
  intro t
  exact (Measurable.ennreal_ofReal (measurable_const.mul (M.c_meas.comp (measurable_pi_apply t)))).aemeasurable

theorem transformed_value_bounds (M M' : CMP A) (α C : ℝ) (ha : 0 < α) (ha1 : α < 1)
    (hm : ModifiedLaw M M' α) (hc : ∀ i a, a ∈ M.U i → M.c i a ≤ C) :
    (∀ i, discValue M' (1-α) i ≠ ⊤) ∧
      ∀ i, |(discValue M' (1-α) i).toReal| ≤ C / α := by
  have hc' : ∀ i a, a ∈ M'.U i → M'.c i a ≤ C := by
    intro i a ha
    rw [hm.1] at ha
    rw [hm.2.1 i a ha]
    exact hc i a ha
  simpa using discValue_finite_bounded M' (1-α) C (sub_pos.mpr ha1).le (by linarith) hc'

#print axioms initial_state_lintegral
#print axioms discounted_sum
#print axioms transformed_value_bounds
end RossPath

open Filter Topology
open scoped ENNReal
namespace RossVerification

lemma finite_lower (b : ℝ≥0∞) (u c : ℕ → ℝ≥0∞)
    (h : ∀ t, u t ≤ c t + b*u (t+1)) (N : ℕ) :
    u 0 ≤ (∑ t ∈ Finset.range N, b^t*c t) + b^N*u N := by
  induction N with
  | zero => simpa
  | succ N ih =>
    calc
      _ ≤ (∑ t ∈ Finset.range N, b^t*c t) + b^N*u N := ih
      _ ≤ (∑ t ∈ Finset.range N, b^t*c t) + b^N*(c N+b*u (N+1)) :=
        add_le_add le_rfl (by gcongr; exact h N)
      _ = _ := by rw [Finset.sum_range_succ,pow_succ]; ring

lemma finite_identity (b : ℝ≥0∞) (u c : ℕ → ℝ≥0∞)
    (h : ∀ t, u t = c t + b*u (t+1)) (N : ℕ) :
    u 0 = (∑ t ∈ Finset.range N, b^t*c t) + b^N*u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      _ = (∑ t ∈ Finset.range N, b^t*c t) + b^N*u N := ih
      _ = (∑ t ∈ Finset.range N, b^t*c t) + b^N*(c N+b*u (N+1)) := by rw [h N]
      _ = _ := by rw [Finset.sum_range_succ,pow_succ]; ring

lemma infinite_lower (b B : ℝ≥0∞) (hb : b < 1) (hB : B ≠ ⊤)
    (u c : ℕ → ℝ≥0∞) (hu : ∀ t, u t ≤ B)
    (h : ∀ t, u t ≤ c t + b*u (t+1)) : u 0 ≤ ∑' t, b^t*c t := by
  have hfin (N : ℕ) : u 0 ≤ (∑' t, b^t*c t) + b^N*B := by
    apply (finite_lower b u c h N).trans
    exact add_le_add (ENNReal.sum_le_tsum (Finset.range N)) (by gcongr; exact hu N)
  have ht : Tendsto (fun N : ℕ => (∑' t, b^t*c t) + b^N*B) atTop
      (𝓝 ((∑' t, b^t*c t) + 0)) :=
    by simpa using tendsto_const_nhds.add (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb) (Or.inr hB))
  simpa using ge_of_tendsto' ht hfin

lemma infinite_upper (b : ℝ≥0∞) (u c : ℕ → ℝ≥0∞)
    (h : ∀ t, u t = c t + b*u (t+1)) : (∑' t, b^t*c t) ≤ u 0 := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  exact le_self_add.trans (finite_identity b u c h N).symm.le
end RossVerification

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace RossVerification
open ArapostathisAC.RossReduction RossPath
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

def potential (M : CMP A) (π : Policy M) (i : ℕ) (v : ℕ → ℝ≥0∞) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, v (ω t).1 ∂pathMeasure M π i

def stage (M : CMP A) (π : Policy M) (i t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2) ∂pathMeasure M π i

lemma potential_initial (M : CMP A) (π : Policy M) (i : ℕ) (v : ℕ → ℝ≥0∞) :
    potential M π i v 0 = v i := initial_state_lintegral M π i v

lemma potential_bound (M : CMP A) (π : Policy M) (i : ℕ) (v : ℕ → ℝ≥0∞)
    (B : ℝ≥0∞) (hv : ∀ j, v j ≤ B) (t : ℕ) : potential M π i v t ≤ B := by
  apply lintegral_le_const
  exact Filter.Eventually.of_forall fun ω => hv (ω t).1

lemma expected_lower (M : CMP A) (π : Policy M) (i : ℕ) (v : ℕ → ℝ≥0∞)
    (b : ℝ≥0∞) (hbell : ∀ j a, a ∈ M.U j →
      v j ≤ ENNReal.ofReal (M.c j a) + b * ∫⁻ k, v k ∂M.P (j,a)) (t : ℕ) :
    potential M π i v t ≤ stage M π i t + b * potential M π i v (t+1) := by
  have hc : Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
    (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal
  have hv : Measurable (fun ω : ℕ → ℕ × A => ∫⁻ k, v k ∂M.P (ω t)) :=
    ((measurable_of_countable v).lintegral_kernel (κ := M.P)).comp (measurable_pi_apply t)
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2) + b * ∫⁻ k, v k ∂M.P (ω t)
        ∂pathMeasure M π i := by
      apply lintegral_mono_ae
      filter_upwards [admissible_time M π i t] with ω hω
      exact hbell _ _ hω
    _ = _ := by
      rw [lintegral_add_left hc,lintegral_const_mul b hv,← state_transition M π i t v]
      rfl

lemma discounted_stage_sum (M : CMP A) (π : Policy M) (β : ℝ) (hb : 0 ≤ β) (i : ℕ) :
    discCost M π β i = ∑' t, (ENNReal.ofReal β)^t * stage M π i t := by
  rw [discounted_sum]
  apply tsum_congr
  intro t
  simp_rw [ENNReal.ofReal_mul (pow_nonneg hb t), ENNReal.ofReal_pow hb]
  exact lintegral_const_mul _ ((M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal)
end RossVerification

open MeasureTheory ProbabilityTheory Set Function Preorder MeasurableSpace
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RossVerification
open ArapostathisAC.RossReduction RossPath
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

def follows {M : CMP A} (f : StationaryPolicy M) : Set (ℕ × A) := {p | p.2 = f.1 p.1}

lemma follows_measurable {M : CMP A} (f : StationaryPolicy M) : MeasurableSet (follows f) := by
  have he : follows f = ⋃ j : ℕ, ({j} : Set ℕ) ×ˢ {f.1 j} := by
    ext p
    simp only [follows, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨p.1, rfl, h⟩
    · rintro ⟨j, hj, ha⟩
      simpa only [hj] using ha
  rw [he]
  exact MeasurableSet.iUnion fun j => (measurableSet_singleton j).prod (measurableSet_singleton (f.1 j))

lemma initial_follows {M : CMP A} (f : StationaryPolicy M) (i : ℕ) :
    ∀ᵐ p ∂initMeasure f.toPolicy i, p ∈ follows f := by
  apply ae_iff.mpr
  change initMeasure f.toPolicy i (follows f)ᶜ = 0
  rw [initMeasure,Measure.map_apply (show Measurable (fun a : A => (i,a)) from
    measurable_const.prodMk measurable_id) (follows_measurable f).compl]
  simp [StationaryPolicy.toPolicy,Kernel.deterministic_apply,Measure.dirac_apply,follows]

lemma step_follows {M : CMP A} (f : StationaryPolicy M) (t : ℕ)
    (hist : Π _ : Finset.Iic t, ℕ × A) :
    ∀ᵐ p ∂stepKernel M f.toPolicy t hist, p ∈ follows f := by
  apply Kernel.ae_compProd_of_ae_ae (follows_measurable f)
  apply Filter.Eventually.of_forall
  intro j
  change ∀ᵐ a ∂Measure.dirac (f.1 j), a = f.1 j
  simp

lemma stationary_action {M : CMP A} (f : StationaryPolicy M) (i t : ℕ) :
    ∀ᵐ ω ∂pathMeasure M f.toPolicy i, (ω t).2 = f.1 (ω t).1 := by
  cases t with
  | zero =>
      have h := initial_follows f i
      rw [← initial_marginal M f.toPolicy i] at h
      exact (ae_map_iff (μ := pathMeasure M f.toPolicy i) (f := fun ω : ℕ → ℕ × A => ω 0)
        (p := fun p : ℕ × A => p ∈ follows f) (measurable_pi_apply 0).aemeasurable
        (follows_measurable f)).mp h
  | succ t =>
      have h : ∀ᵐ p ∂((pathMeasure M f.toPolicy i).map (frestrictLe t) ⊗ₘ stepKernel M f.toPolicy t),
          p.2 ∈ follows f := by
        apply Measure.ae_compProd_of_ae_ae (measurable_snd (follows_measurable f))
        exact Filter.Eventually.of_forall fun hist => step_follows f t hist
      have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => ℕ × A) (μ₀ := initMeasure f.toPolicy i) (κ := stepKernel M f.toPolicy) (a := t)
      change (pathMeasure M f.toPolicy i).map (frestrictLe t) ⊗ₘ stepKernel M f.toPolicy t = _ at he
      rw [he] at h
      exact (ae_map_iff (μ := pathMeasure M f.toPolicy i)
        (f := fun ω : ℕ → ℕ × A => (frestrictLe t ω,ω (t+1)))
        (p := fun p : (Π _ : Finset.Iic t, ℕ × A) × (ℕ × A) => p.2 ∈ follows f)
        ((measurable_frestrictLe t).prodMk (measurable_pi_apply (t+1))).aemeasurable
        (measurable_snd (follows_measurable f))).mp h
end RossVerification

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace RossVerification
open ArapostathisAC.RossReduction RossPath
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

lemma expected_identity (M : CMP A) (f : StationaryPolicy M) (i : ℕ) (v : ℕ → ℝ≥0∞)
    (b : ℝ≥0∞) (hbell : ∀ j,
      v j = ENNReal.ofReal (M.c j (f.1 j)) + b * ∫⁻ k, v k ∂M.P (j,f.1 j)) (t : ℕ) :
    potential M f.toPolicy i v t = stage M f.toPolicy i t + b * potential M f.toPolicy i v (t+1) := by
  have hc : Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
    (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal
  have hv : Measurable (fun ω : ℕ → ℕ × A => ∫⁻ k, v k ∂M.P (ω t)) :=
    ((measurable_of_countable v).lintegral_kernel (κ := M.P)).comp (measurable_pi_apply t)
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2) + b * ∫⁻ k, v k ∂M.P (ω t)
        ∂pathMeasure M f.toPolicy i := by
      apply lintegral_congr_ae
      filter_upwards [stationary_action f i t] with ω hω
      have he : ω t = ((ω t).1,f.1 (ω t).1) := Prod.ext rfl hω
      rw [he]
      exact hbell _
    _ = _ := by
      rw [lintegral_add_left hc,lintegral_const_mul b hv,← state_transition M f.toPolicy i t v]
      rfl

lemma stationary_finite_identity (M : CMP A) (f : StationaryPolicy M) (i : ℕ)
    (v : ℕ → ℝ≥0∞) (b : ℝ≥0∞)
    (hbell : ∀ j, v j = ENNReal.ofReal (M.c j (f.1 j)) + b * ∫⁻ k, v k ∂M.P (j,f.1 j)) (N : ℕ) :
    v i = (∑ t ∈ Finset.range N, b^t * stage M f.toPolicy i t) +
      b^N * potential M f.toPolicy i v N := by
  simpa only [potential_initial] using finite_identity b (potential M f.toPolicy i v)
    (stage M f.toPolicy i) (expected_identity M f i v b hbell) N

lemma subsolution_lower_bound (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (v : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (hB : B ≠ ⊤) (hv : ∀ j, v j ≤ B)
    (hbell : ∀ j a, a ∈ M.U j → v j ≤ ENNReal.ofReal (M.c j a) +
      ENNReal.ofReal β * ∫⁻ k, v k ∂M.P (j,a)) (π : Policy M) (i : ℕ) :
    v i ≤ discCost M π β i := by
  rw [discounted_stage_sum M π β hb i]
  simpa only [potential_initial] using infinite_lower (ENNReal.ofReal β) B
    (ENNReal.ofReal_lt_one.mpr hb1) hB (potential M π i v) (stage M π i)
    (potential_bound M π i v B hv) (expected_lower M π i v (ENNReal.ofReal β) hbell)

lemma attaining_policy_upper_bound (M : CMP A) (β : ℝ) (hb : 0 ≤ β)
    (v : ℕ → ℝ≥0∞) (f : StationaryPolicy M)
    (hbell : ∀ j, v j = ENNReal.ofReal (M.c j (f.1 j)) +
      ENNReal.ofReal β * ∫⁻ k, v k ∂M.P (j,f.1 j)) (i : ℕ) :
    discCost M f.toPolicy β i ≤ v i := by
  rw [discounted_stage_sum M f.toPolicy β hb i]
  simpa only [potential_initial] using infinite_upper (ENNReal.ofReal β)
    (potential M f.toPolicy i v) (stage M f.toPolicy i)
    (expected_identity M f i v (ENNReal.ofReal β) hbell)

theorem bounded_bellman_verification (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (v : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (hB : B ≠ ⊤) (hv : ∀ j, v j ≤ B)
    (hsub : ∀ j a, a ∈ M.U j → v j ≤ ENNReal.ofReal (M.c j a) +
      ENNReal.ofReal β * ∫⁻ k, v k ∂M.P (j,a))
    (f : StationaryPolicy M)
    (heq : ∀ j, v j = ENNReal.ofReal (M.c j (f.1 j)) +
      ENNReal.ofReal β * ∫⁻ k, v k ∂M.P (j,f.1 j)) :
    (∀ π : Policy M, ∀ i, v i ≤ discCost M π β i) ∧
      (∀ i, discValue M β i = v i) ∧ DiscountOptimal M β f := by
  have hl := subsolution_lower_bound M β hb hb1 v B hB hv hsub
  have hu := attaining_policy_upper_bound M β hb v f heq
  have hvalue (i : ℕ) : discValue M β i = v i := by
    apply le_antisymm
    · exact (iInf_le _ f.toPolicy).trans (hu i)
    · exact le_iInf fun π => hl π i
  refine ⟨hl,hvalue,?_⟩
  intro i
  rw [hvalue i]
  exact le_antisymm (hu i) (hl f.toPolicy i)

#print axioms bounded_bellman_verification
end RossVerification

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace RossBellman
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
lemma bounded_summable (M : CMP A) (h : ℕ → ℝ) (B : ℝ) (hb : ∀ j, |h j| ≤ B)
    (i : ℕ) (a : A) : Summable (fun j => prob M i a j * h j) := by
  have hs : Summable (fun j : ℕ => prob M i a j) :=
    summable_measure_toReal (fun j => measurableSet_singleton j) (by
      intro j k hjk
      exact disjoint_singleton.mpr hjk)
  apply Summable.of_norm_bounded (hs.mul_right B)
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ prob M i a j from ENNReal.toReal_nonneg)]
  exact mul_le_mul_of_nonneg_left (hb j) ENNReal.toReal_nonneg

lemma expectation (M M' : CMP A) (α : ℝ) (ha : α < 1)
    (hm : ModifiedLaw M M' α) (h : ℕ → ℝ) (B : ℝ) (hb : ∀ j, |h j| ≤ B)
    (i : ℕ) (a : A) (hadm : a ∈ M.U i) :
    (1-α) * (∑' j, prob M' i a j * h j) =
      (∑' j, prob M i a j * h j) - α * h 0 := by
  have heq : (fun j => (1-α) * (prob M' i a j * h j)) =
      (fun j => prob M i a j * h j - if j = 0 then α * h 0 else 0) := by
    funext j
    rw [hm.2.2 i a hadm j]
    by_cases hj : j = 0
    · subst j; simp only [if_true]; field_simp [ne_of_gt (sub_pos.mpr ha)] <;> ring
    · simp only [if_neg hj, sub_zero]; field_simp [ne_of_gt (sub_pos.mpr ha)] <;> ring
  rw [← tsum_mul_left, heq, Summable.tsum_sub (bounded_summable M h B hb i a)
    (hasSum_ite_eq 0 (α * h 0)).summable, tsum_ite_eq]

/-- An attained discounted Bellman equation for a bounded real function yields
    the original process's average-cost equation. Identifying that function with
    the strategic-path discounted value is a separate obligation. -/
theorem bellman_to_acoe (M M' : CMP A) (α : ℝ) (ha : α < 1)
    (hm : ModifiedLaw M M' α) (h : ℕ → ℝ) (B : ℝ) (hb : ∀ j, |h j| ≤ B)
    (hBell : ∀ i,
      (∃ a ∈ M'.U i, h i = M'.c i a + (1-α) * ∑' j, prob M' i a j * h j) ∧
      (∀ a ∈ M'.U i, h i ≤ M'.c i a + (1-α) * ∑' j, prob M' i a j * h j)) :
    ACOE M (α * h 0) h := by
  intro i
  refine ⟨fun a _ => bounded_summable M h B hb i a, ?_, ?_⟩
  · obtain ⟨a, hadm, heq⟩ := (hBell i).1
    rw [hm.1] at hadm
    refine ⟨a, hadm, ?_⟩
    rw [hm.2.1 i a hadm, expectation M M' α ha hm h B hb i a hadm] at heq
    linarith
  · intro a hadm
    have hi := (hBell i).2 a (by simpa [hm.1] using hadm)
    rw [hm.2.1 i a hadm, expectation M M' α ha hm h B hb i a hadm] at hi
    linarith
end RossBellman

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace RossVerification
open ArapostathisAC.RossReduction RossPath
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

lemma real_row_expectation (M : CMP A) (h : ℕ → ℝ) (B : ℝ)
    (hn : ∀ j, 0 ≤ h j) (hb : ∀ j, |h j| ≤ B) (i : ℕ) (a : A) :
    (∫⁻ j, ENNReal.ofReal (h j) ∂M.P (i,a)) =
      ENNReal.ofReal (∑' j, prob M i a j * h j) := by
  rw [lintegral_countable']
  simp only [prob]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (hn j))
    (RossBellman.bounded_summable M h B hb i a)]
  apply tsum_congr
  intro j
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simp only [prob, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact mul_comm _ _

theorem real_bellman_identification (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (h : ℕ → ℝ) (B : ℝ) (hn : ∀ j, 0 ≤ h j) (hbound : ∀ j, |h j| ≤ B)
    (hBell : ∀ i,
      (∃ a ∈ M.U i, h i = M.c i a + β * ∑' j, prob M i a j * h j) ∧
      (∀ a ∈ M.U i, h i ≤ M.c i a + β * ∑' j, prob M i a j * h j)) :
    (∀ i, discValue M β i = ENNReal.ofReal (h i)) ∧
      ∃ f : StationaryPolicy M, DiscountOptimal M β f ∧
        ∀ i, discCost M f.toPolicy β i = ENNReal.ofReal (h i) := by
  classical
  choose f hf he using fun i => (hBell i).1
  let sf : StationaryPolicy M := ⟨f,hf⟩
  have hs (i : ℕ) (a : A) : 0 ≤ ∑' j, prob M i a j * h j :=
    tsum_nonneg fun j => mul_nonneg ENNReal.toReal_nonneg (hn j)
  have hr (i : ℕ) (a : A) (ha : a ∈ M.U i) :
      ENNReal.ofReal (M.c i a + β * ∑' j, prob M i a j * h j) =
        ENNReal.ofReal (M.c i a) + ENNReal.ofReal β *
          ∫⁻ j, ENNReal.ofReal (h j) ∂M.P (i,a) := by
    rw [ENNReal.ofReal_add (M.c_nonneg i a ha) (mul_nonneg hb (hs i a)),
      ENNReal.ofReal_mul hb, real_row_expectation M h B hn hbound i a]
  have hsub (i : ℕ) (a : A) (ha : a ∈ M.U i) :
      ENNReal.ofReal (h i) ≤ ENNReal.ofReal (M.c i a) + ENNReal.ofReal β *
        ∫⁻ j, ENNReal.ofReal (h j) ∂M.P (i,a) := by
    rw [← hr i a ha]
    exact ENNReal.ofReal_le_ofReal ((hBell i).2 a ha)
  have heq (i : ℕ) : ENNReal.ofReal (h i) = ENNReal.ofReal (M.c i (sf.1 i)) +
      ENNReal.ofReal β * ∫⁻ j, ENNReal.ofReal (h j) ∂M.P (i,sf.1 i) := by
    change _ = ENNReal.ofReal (M.c i (f i)) + _
    rw [← hr i (f i) (hf i), he i]
  have result := bounded_bellman_verification M β hb hb1 (fun i => ENNReal.ofReal (h i))
    (ENNReal.ofReal B) ENNReal.ofReal_ne_top
    (fun i => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hbound i))) hsub sf heq
  refine ⟨result.2.1,sf,result.2.2,?_⟩
  intro i
  exact (result.2.2 i).trans (result.2.1 i)

/-- Conditional on existence of a bounded nonnegative attained Bellman solution,
    this identifies it with the actual strategic-path value and obtains the
    rewritten average-cost equation. Bellman-solution existence is not assumed proved. -/
theorem identified_transformed_acoe (M M' : CMP A) (α : ℝ) (ha : 0 < α) (ha1 : α < 1)
    (hm : ModifiedLaw M M' α) (h : ℕ → ℝ) (B : ℝ)
    (hn : ∀ j, 0 ≤ h j) (hbound : ∀ j, |h j| ≤ B)
    (hBell : ∀ i,
      (∃ a ∈ M'.U i, h i = M'.c i a + (1-α) * ∑' j, prob M' i a j * h j) ∧
      (∀ a ∈ M'.U i, h i ≤ M'.c i a + (1-α) * ∑' j, prob M' i a j * h j)) :
    (∀ i, discValue M' (1-α) i = ENNReal.ofReal (h i)) ∧
      (∃ f : StationaryPolicy M', DiscountOptimal M' (1-α) f) ∧
      ACOE M (α * (discValue M' (1-α) 0).toReal)
        (fun i => (discValue M' (1-α) i).toReal) := by
  have result := real_bellman_identification M' (1-α) (by linarith) (by linarith)
    h B hn hbound hBell
  refine ⟨result.1,?_,?_⟩
  · obtain ⟨f,hf,_⟩ := result.2
    exact ⟨f,hf⟩
  · have he (i : ℕ) : (discValue M' (1-α) i).toReal = h i := by
      rw [result.1 i,ENNReal.toReal_ofReal (hn i)]
    simp_rw [he]
    exact RossBellman.bellman_to_acoe M M' α ha1 hm h B hbound hBell

#print axioms real_bellman_identification
#print axioms identified_transformed_acoe
end RossVerification

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
noncomputable section
namespace RossExistence
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
lemma prob_summable (M : CMP A) (i : ℕ) (a : A) : Summable (prob M i a) :=
  summable_measure_toReal (fun j => measurableSet_singleton j) (by
    intro j k hjk; exact disjoint_singleton.mpr hjk)
lemma prob_total (M : CMP A) (i : ℕ) (a : A) : ∑' j, prob M i a j = 1 := by
  simp only [prob]
  rw [← ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have he : (∑' j : ℕ, M.P (i,a) {j}) = 1 := by
    have h := lintegral_countable' (μ := M.P (i,a)) (fun _ : ℕ => (1 : ℝ≥0∞))
    simpa using h.symm
  rw [he]
  simp
lemma expectation_const (M : CMP A) (i : ℕ) (a : A) (B : ℝ) :
    ∑' j, prob M i a j * B = B := by
  rw [tsum_mul_right, prob_total, one_mul]
lemma positive_expectation_lsc (M : CMP A) (i : ℕ) (h : ℕ → ℝ)
    (hn : ∀ j, 0 ≤ h j) (hs : ∀ a, Summable (fun j => prob M i a j * h j)) :
    LowerSemicontinuousOn (fun a => ∑' j, prob M i a j * h j) (M.U i) := by
  intro a ha y hy
  obtain ⟨s, hsy⟩ := ((hs a).hasSum.eventually (Ioi_mem_nhds hy)).exists
  have hc : ContinuousOn (fun a => ∑ j ∈ s, prob M i a j * h j) (M.U i) := by
    exact continuousOn_finsetSum s fun j _ => (M.P_cont i j).mul_const (h j)
  have he := (hc a ha).eventually (Ioi_mem_nhds hsy)
  filter_upwards [he] with b hb
  exact hb.trans_le ((hs b).sum_le_tsum s (fun j _ => mul_nonneg ENNReal.toReal_nonneg (hn j)))
lemma bounded_expectation_continuous (M : CMP A) (h : ℕ → ℝ) (B : ℝ)
    (hb : ∀ j, |h j| ≤ B) (i : ℕ) :
    ContinuousOn (fun a => ∑' j, prob M i a j * h j) (M.U i) := by
  have hs (a : A) := RossBellman.bounded_summable M h B hb i a
  have hp (a : A) : Summable (fun j => prob M i a j * (h j+B)) := by
    simpa only [mul_add] using (hs a).add ((prob_summable M i a).mul_right B)
  have hm (a : A) : Summable (fun j => prob M i a j * (B-h j)) := by
    simpa only [mul_sub] using ((prob_summable M i a).mul_right B).sub (hs a)
  have ep (a : A) : (∑' j, prob M i a j * (h j+B)) = (∑' j, prob M i a j * h j)+B := by
    simp only [mul_add]
    rw [(hs a).tsum_add ((prob_summable M i a).mul_right B), expectation_const]
  have em (a : A) : (∑' j, prob M i a j * (B-h j)) = B-(∑' j, prob M i a j * h j) := by
    simp only [mul_sub]
    rw [((prob_summable M i a).mul_right B).tsum_sub (hs a), expectation_const]
  have lp := positive_expectation_lsc M i (fun j => h j+B)
    (fun j => by have := (abs_le.mp (hb j)).1; linarith) hp
  have lm := positive_expectation_lsc M i (fun j => B-h j)
    (fun j => sub_nonneg.mpr ((le_abs_self _).trans (hb j))) hm
  apply continuousOn_iff_lower_upperSemicontinuousOn.mpr
  constructor
  · intro a ha y hy
    have he := lp a ha (y+B) (by dsimp; rw [ep]; linarith)
    filter_upwards [he] with b h
    rw [ep] at h
    linarith
  · intro a ha y hy
    have he := lm a ha (B-y) (by dsimp; rw [em]; exact sub_lt_sub_left hy B)
    filter_upwards [he] with b h
    rw [em] at h
    linarith
#print axioms bounded_expectation_continuous
end RossExistence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
noncomputable section
namespace RossExistence
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
lemma expectation_bound (M : CMP A) (h : ℕ → ℝ) (B : ℝ)
    (hb : ∀ j, |h j| ≤ B) (i : ℕ) (a : A) :
    |∑' j, prob M i a j * h j| ≤ B := by
  have hs := RossBellman.bounded_summable M h B hb i a
  have lo := ((prob_summable M i a).mul_right (-B)).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (abs_le.mp (hb j)).1 ENNReal.toReal_nonneg) hs
  have hi := hs.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (abs_le.mp (hb j)).2 ENNReal.toReal_nonneg)
    ((prob_summable M i a).mul_right B)
  change (∑' j, prob M i a j * (-B)) ≤ (∑' j, prob M i a j * h j) at lo
  change (∑' j, prob M i a j * h j) ≤ (∑' j, prob M i a j * B) at hi
  rw [expectation_const] at lo hi
  exact abs_le.mpr ⟨lo,hi⟩
def q (M : CMP A) (β : ℝ) (v : BoundedContinuousFunction ℕ ℝ) (i : ℕ) (a : A) : ℝ :=
  M.c i a + β * ∑' j, prob M i a j * v j
lemma q_continuous (M : CMP A) (β : ℝ) (v : BoundedContinuousFunction ℕ ℝ) (i : ℕ) :
    ContinuousOn (q M β v i) (M.U i) :=
  (M.c_cont i).add ((bounded_expectation_continuous M v ‖v‖
    (fun j => v.norm_coe_le_norm j) i).const_mul β)
lemma exists_minimizer (M : CMP A) (β : ℝ) (v : BoundedContinuousFunction ℕ ℝ) (i : ℕ) :
    ∃ a ∈ M.U i, ∀ b ∈ M.U i, q M β v i a ≤ q M β v i b :=
  (M.U_compact i).exists_isMinOn (M.U_nonempty i) (q_continuous M β v i)
def argmin (M : CMP A) (β : ℝ) (v : BoundedContinuousFunction ℕ ℝ) (i : ℕ) : A :=
  (exists_minimizer M β v i).choose
lemma argmin_mem (M : CMP A) (β : ℝ) (v : BoundedContinuousFunction ℕ ℝ) (i : ℕ) :
    argmin M β v i ∈ M.U i := (exists_minimizer M β v i).choose_spec.1
lemma argmin_le (M : CMP A) (β : ℝ) (v : BoundedContinuousFunction ℕ ℝ) (i : ℕ) (a : A) (ha : a ∈ M.U i) :
    q M β v i (argmin M β v i) ≤ q M β v i a :=
  (exists_minimizer M β v i).choose_spec.2 a ha
lemma q_bound (M : CMP A) (β : ℝ) (C : ℝ)
    (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) (v : BoundedContinuousFunction ℕ ℝ)
    (i : ℕ) (a : A) (ha : a ∈ M.U i) :
    |q M β v i a| ≤ C + |β| * ‖v‖ := by
  unfold q
  calc
    _ ≤ |M.c i a| + |β * ∑' j, prob M i a j * v j| := abs_add_le _ _
    _ ≤ C + |β| * ‖v‖ := by
      rw [abs_of_nonneg (M.c_nonneg i a ha), abs_mul]
      exact add_le_add (hc i a ha) (mul_le_mul_of_nonneg_left
        (expectation_bound M v ‖v‖ (fun j => v.norm_coe_le_norm j) i a) (abs_nonneg β))
def bellman (M : CMP A) (β : ℝ) (C : ℝ)
    (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) (v : BoundedContinuousFunction ℕ ℝ) : BoundedContinuousFunction ℕ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (fun i => q M β v i (argmin M β v i))
    (2*(C+|β| * ‖v‖)) (by
      intro i j
      rw [Real.dist_eq]
      calc
        _ ≤ |q M β v i (argmin M β v i)|+|q M β v j (argmin M β v j)| := abs_sub _ _
        _ ≤ _ := by
          have hi := q_bound M β C hc v i _ (argmin_mem M β v i)
          have hj := q_bound M β C hc v j _ (argmin_mem M β v j)
          linarith)
lemma q_difference (M : CMP A) (β : ℝ) (v w : BoundedContinuousFunction ℕ ℝ) (i : ℕ) (a : A) :
    |q M β v i a - q M β w i a| ≤ |β| * dist v w := by
  have hv := RossBellman.bounded_summable M v ‖v‖ (fun j => v.norm_coe_le_norm j) i a
  have hw := RossBellman.bounded_summable M w ‖w‖ (fun j => w.norm_coe_le_norm j) i a
  have he : q M β v i a - q M β w i a = β * ∑' j, prob M i a j * (v j-w j) := by
    simp only [mul_sub]
    rw [hv.tsum_sub hw]
    unfold q
    ring
  rw [he,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
  apply expectation_bound M (fun j => v j-w j) (dist v w) _ i a
  intro j
  exact BoundedContinuousFunction.dist_coe_le_dist (f := v) (g := w) j
lemma bellman_lipschitz (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (C : ℝ)
    (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) :
    LipschitzWith ⟨β,hb⟩ (bellman M β C hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  apply (BoundedContinuousFunction.dist_le (mul_nonneg hb dist_nonneg)).mpr
  intro i
  change |q M β v i (argmin M β v i) - q M β w i (argmin M β w i)| ≤ β * dist v w
  have h1 := argmin_le M β v i (argmin M β w i) (argmin_mem M β w i)
  have h2 := argmin_le M β w i (argmin M β v i) (argmin_mem M β v i)
  have d1 := q_difference M β v w i (argmin M β w i)
  have d2 := q_difference M β v w i (argmin M β v i)
  rw [abs_of_nonneg hb] at d1 d2
  exact abs_le.mpr ⟨by have := (abs_le.mp d2).1; linarith,
    by have := (abs_le.mp d1).2; linarith⟩
lemma bellman_nonneg (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (C : ℝ)
    (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) (v : BoundedContinuousFunction ℕ ℝ) (hv : ∀ j, 0 ≤ v j) :
    ∀ i, 0 ≤ bellman M β C hc v i := by
  intro i
  exact add_nonneg (M.c_nonneg i _ (argmin_mem M β v i))
    (mul_nonneg hb (tsum_nonneg fun j => mul_nonneg ENNReal.toReal_nonneg (hv j)))
end RossExistence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
noncomputable section
namespace RossExistence
open ArapostathisAC.RossReduction
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
theorem bounded_bellman_exists (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (C : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) :
    ∃ (v : ℕ → ℝ) (B : ℝ), (∀ j, 0 ≤ v j) ∧ (∀ j, |v j| ≤ B) ∧
      ∀ i, (∃ a ∈ M.U i, v i = M.c i a + β * ∑' j, prob M i a j * v j) ∧
        (∀ a ∈ M.U i, v i ≤ M.c i a + β * ∑' j, prob M i a j * v j) := by
  let T := bellman M β C hc
  have hT : ContractingWith ⟨β,hb⟩ T := ⟨hb1,bellman_lipschitz M β hb C hc⟩
  let v : BoundedContinuousFunction ℕ ℝ := hT.fixedPoint T
  have he : T v = v := hT.fixedPoint_isFixedPt
  have hn (n : ℕ) : ∀ i, 0 ≤ (T^[n] (0 : BoundedContinuousFunction ℕ ℝ)) i := by
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact bellman_nonneg M β hb C hc _ ih
  have hnonneg (i : ℕ) : 0 ≤ v i := by
    have ht : Tendsto (fun n => (T^[n] (0 : BoundedContinuousFunction ℕ ℝ)) i) atTop (𝓝 (v i)) :=
      (BoundedContinuousFunction.lipschitz_eval_const i).continuous.continuousAt.tendsto.comp
        (hT.tendsto_iterate_fixedPoint (0 : BoundedContinuousFunction ℕ ℝ))
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hn n i)
  refine ⟨v,‖v‖,hnonneg,(fun j => v.norm_coe_le_norm j),?_⟩
  intro i
  have hei : v i = q M β v i (argmin M β v i) := congrArg (fun f : BoundedContinuousFunction ℕ ℝ => f i) he.symm
  refine ⟨⟨argmin M β v i,argmin_mem M β v i,hei⟩,?_⟩
  intro a ha
  rw [hei]
  exact argmin_le M β v i a ha
#print axioms bounded_bellman_exists
end RossExistence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.RossReduction
noncomputable section

/-- The discounted optimality equation for the transformed process,
rewritten as the original process's average cost optimality equation. -/
theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M M' : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0)
    (hmod : ModifiedLaw M M' α)
    (C : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) :
    (∀ i, discValue M' (1 - α) i ≠ ⊤) ∧
    (∃ B : ℝ, ∀ i, |(discValue M' (1 - α) i).toReal| ≤ B) ∧
    ACOE M (α * (discValue M' (1 - α) 0).toReal)
      (fun i => (discValue M' (1 - α) i).toReal) := by
  have hc' : ∀ i, ∀ a ∈ M'.U i, M'.c i a ≤ C := by
    intro i a ha
    have ha' : a ∈ M.U i := by simpa [hmod.1] using ha
    rw [hmod.2.1 i a ha']
    exact hc i a ha'
  obtain ⟨v,B,hn,hb,hBell⟩ := RossExistence.bounded_bellman_exists M' (1-α)
    (by linarith) (by linarith) C hc'
  have hv := RossVerification.identified_transformed_acoe M M' α hα hα1 hmod v B hn hb hBell
  refine ⟨?_,⟨B,?_⟩,hv.2.2⟩
  · intro i
    rw [hv.1 i]
    exact ENNReal.ofReal_ne_top
  · intro i
    rw [hv.1 i, ENNReal.toReal_ofReal (hn i)]
    exact hb i

#print axioms solution
