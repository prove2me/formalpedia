-- Prove2me | solution 1 for ArapostathisAC.RossReduction.theorem_5_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T00:46:14.198263+00:00
-- url     : https://prove2.me/submissions/b6d3be48-9d44-47f5-8e82-d75cbf6f452a

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
noncomputable section
namespace RossAverage
open ArapostathisAC.RossReduction RossPath
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
def transitionKernel (M : CMP A) (t : ℕ) : Kernel (ℕ → ℕ × A) ℕ :=
  M.P.comap (fun ω => ω t) (measurable_pi_apply t)
lemma state_law (M : CMP A) (π : Policy M) (i t : ℕ) :
    (pathMeasure M π i).map (fun ω => (ω (t+1)).1) =
      transitionKernel M t ∘ₘ pathMeasure M π i := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    _ = ∫⁻ ω, g (ω (t+1)).1 ∂pathMeasure M π i :=
      lintegral_map hg (show Measurable (fun ω : ℕ → ℕ × A => (ω (t+1)).1) from by fun_prop)
    _ = ∫⁻ ω, (∫⁻ j, g j ∂M.P (ω t)) ∂pathMeasure M π i := state_transition M π i t g
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply,Kernel.lintegral_comp _ _ _ hg]
      rfl

lemma bias_integrable_comp (M : CMP A) (π : Policy M) (i t : ℕ) (h : ℕ → ℝ)
    (hi : Integrable (fun ω : ℕ → ℕ × A => h (ω (t+1)).1) (pathMeasure M π i)) :
    Integrable h (transitionKernel M t ∘ₘ pathMeasure M π i) := by
  rw [← state_law M π i t]
  exact (integrable_map_measure (measurable_of_countable h).aestronglyMeasurable
    ((measurable_pi_apply (t+1)).fst.aemeasurable)).mpr hi
lemma bias_next_integral (M : CMP A) (π : Policy M) (i t : ℕ) (h : ℕ → ℝ)
    (hi : Integrable (fun ω : ℕ → ℕ × A => h (ω (t+1)).1) (pathMeasure M π i)) :
    (∫ ω, h (ω (t+1)).1 ∂pathMeasure M π i) =
      ∫ ω, (∫ j, h j ∂M.P (ω t)) ∂pathMeasure M π i := by
  have hc := bias_integrable_comp M π i t h hi
  rw [Measure.comp_eq_comp_const_apply] at hc
  calc
    _ = ∫ j, h j ∂(pathMeasure M π i).map (fun ω => (ω (t+1)).1) :=
      (integral_map ((measurable_pi_apply (t+1)).fst.aemeasurable)
        (measurable_of_countable h).aestronglyMeasurable).symm
    _ = _ := by
      rw [state_law,Measure.comp_eq_comp_const_apply]
      simpa only [Kernel.const_apply,transitionKernel,Kernel.comap_apply] using Kernel.integral_comp hc
lemma bias_kernel_integrable (M : CMP A) (π : Policy M) (i t : ℕ) (h : ℕ → ℝ)
    (hi : Integrable (fun ω : ℕ → ℕ × A => h (ω (t+1)).1) (pathMeasure M π i)) :
    Integrable (fun ω => ∫ j, h j ∂M.P (ω t)) (pathMeasure M π i) := by
  have hc := bias_integrable_comp M π i t h hi
  rw [Measure.comp_eq_comp_const_apply] at hc
  simpa only [Kernel.const_apply,transitionKernel,Kernel.comap_apply] using hc.integral_comp
lemma bias_initial (M : CMP A) (π : Policy M) (i : ℕ) (h : ℕ → ℝ) :
    (∫ ω, h (ω 0).1 ∂pathMeasure M π i) = h i := by
  have hm : Measurable (fun p : ℕ × A => h p.1) := (measurable_of_countable h).comp measurable_fst
  calc
    _ = ∫ p : ℕ × A, h p.1 ∂(pathMeasure M π i).map (fun ω => ω 0) :=
      (integral_map (φ := fun ω : ℕ → ℕ × A => ω 0)
        (f := fun p : ℕ × A => h p.1) (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ p : ℕ × A, h p.1 ∂initMeasure π i := by rw [initial_marginal]
    _ = h i := by
      rw [initMeasure,integral_map (φ := fun a : A => (i,a))
        (f := fun p : ℕ × A => h p.1)
        (show AEMeasurable (fun a : A => (i,a)) _ from
          (measurable_const.prodMk measurable_id).aemeasurable) hm.aestronglyMeasurable]
      simp

lemma row_integrable (M : CMP A) (h : ℕ → ℝ) (i : ℕ) (a : A)
    (hs : Summable (fun j => prob M i a j * h j)) : Integrable h (M.P (i,a)) := by
  rw [← Measure.sum_smul_dirac (M.P (i,a))]
  apply integrable_sum_dirac (fun j => measure_ne_top _ _)
  simpa only [prob,Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg] using hs.abs
lemma row_integral (M : CMP A) (h : ℕ → ℝ) (i : ℕ) (a : A)
    (hs : Summable (fun j => prob M i a j * h j)) :
    (∫ j, h j ∂M.P (i,a)) = ∑' j, prob M i a j * h j := by
  simpa only [prob,Measure.real,smul_eq_mul] using integral_countable (row_integrable M h i a hs)
#print axioms bias_next_integral
#print axioms bias_kernel_integrable
#print axioms row_integral
end RossAverage

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RossAverage
open ArapostathisAC.RossReduction RossPath RossVerification
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
def bias (M : CMP A) (π : Policy M) (i : ℕ) (h : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∫ ω, h (ω t).1 ∂pathMeasure M π i
lemma cost_nonneg_ae (M : CMP A) (π : Policy M) (i t : ℕ) :
    0 ≤ᵐ[pathMeasure M π i] (fun ω => M.c (ω t).1 (ω t).2) := by
  filter_upwards [admissible_time M π i t] with ω hω
  exact M.c_nonneg _ _ hω
lemma stage_integrable (M : CMP A) (π : Policy M) (i t : ℕ)
    (hc : stage M π i t ≠ ⊤) :
    Integrable (fun ω => M.c (ω t).1 (ω t).2) (pathMeasure M π i) := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (M.c_meas.comp (measurable_pi_apply t)).aestronglyMeasurable (cost_nonneg_ae M π i t)).mp hc
lemma stage_mean (M : CMP A) (π : Policy M) (i t : ℕ) :
    (∫ ω, M.c (ω t).1 (ω t).2 ∂pathMeasure M π i) = (stage M π i t).toReal :=
  integral_eq_lintegral_of_nonneg_ae (cost_nonneg_ae M π i t)
    (M.c_meas.comp (measurable_pi_apply t)).aestronglyMeasurable
lemma finite_stage_sum (M : CMP A) (π : Policy M) (N i : ℕ) :
    costN M π N i = ∑ t ∈ Finset.range N, stage M π i t := by
  unfold costN stage
  apply lintegral_finsetSum
  intro t ht
  exact (show Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) from
    (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal)
lemma stage_finite_of_cost_finite (M : CMP A) (π : Policy M) (N i t : ℕ)
    (hc : costN M π N i ≠ ⊤) (ht : t < N) : stage M π i t ≠ ⊤ := by
  apply ne_top_of_le_ne_top hc
  rw [finite_stage_sum]
  exact Finset.single_le_sum (fun j hj => zero_le) (Finset.mem_range.mpr ht)
lemma cost_toReal_sum (M : CMP A) (π : Policy M) (N i : ℕ)
    (hc : costN M π N i ≠ ⊤) :
    (costN M π N i).toReal = ∑ t ∈ Finset.range N, (stage M π i t).toReal := by
  rw [finite_stage_sum,ENNReal.toReal_sum]
  intro t ht
  exact stage_finite_of_cost_finite M π N i t hc (Finset.mem_range.mp ht)
lemma stage_lower (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (π : Policy M) (i t : ℕ)
    (ht : Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i))
    (hn : Integrable (fun ω : ℕ → ℕ × A => h (ω (t+1)).1) (pathMeasure M π i))
    (hc : stage M π i t ≠ ⊤) :
    ρ + bias M π i h t ≤ (stage M π i t).toReal + bias M π i h (t+1) := by
  have ic := stage_integrable M π i t hc
  have ik := bias_kernel_integrable M π i t h hn
  have hi : (∫ ω, ρ + h (ω t).1 ∂pathMeasure M π i) ≤
      ∫ ω, (M.c (ω t).1 (ω t).2 + ∫ j, h j ∂M.P (ω t)) ∂pathMeasure M π i := by
    apply integral_mono_ae ((integrable_const ρ).add ht) (ic.add ik)
    filter_upwards [admissible_time M π i t] with ω hω
    dsimp only [Pi.add_apply]
    rw [row_integral M h _ _ ((hacoe _).1 _ hω)]
    exact (hacoe _).2.2 _ hω
  rw [integral_add (integrable_const ρ) ht,integral_add ic ik,stage_mean,
    ← bias_next_integral M π i t h hn] at hi
  simpa [bias] using hi
lemma telescope_lower (ρ : ℝ) (u c : ℕ → ℝ) (N : ℕ)
    (hc : ∀ t < N, ρ + u t ≤ c t + u (t+1)) :
    (N : ℝ)*ρ + u 0 - u N ≤ ∑ t ∈ Finset.range N, c t := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := ih (fun t ht => hc t (Nat.lt.step ht))
    have hn := hc N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ]
    push_cast
    linarith
lemma finite_cost_lower (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (π : Policy M) (i : ℕ)
    (hint : ∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i)) (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)*ρ + h i - bias M π i h N) ≤ costN M π N i := by
  by_cases hc : costN M π N i = ⊤
  · simp [hc]
  rw [ENNReal.ofReal_le_iff_le_toReal hc,cost_toReal_sum M π N i hc]
  have hl := telescope_lower ρ (bias M π i h) (fun t => (stage M π i t).toReal) N
    (fun t ht => stage_lower M ρ h hacoe π i t (hint t) (hint (t+1))
      (stage_finite_of_cost_finite M π N i t hc ht))
  simpa only [bias,bias_initial] using hl
lemma stationary_stage (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (f : StationaryPolicy M) (heq : ∀ j, ρ + h j = M.c j (f.1 j) + ∑' k, prob M j (f.1 j) k * h k)
    (i t : ℕ)
    (ht : Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M f.toPolicy i))
    (hn : Integrable (fun ω : ℕ → ℕ × A => h (ω (t+1)).1) (pathMeasure M f.toPolicy i)) :
    stage M f.toPolicy i t ≠ ⊤ ∧
      (stage M f.toPolicy i t).toReal = ρ + bias M f.toPolicy i h t - bias M f.toPolicy i h (t+1) := by
  have ik := bias_kernel_integrable M f.toPolicy i t h hn
  have he : (fun ω : ℕ → ℕ × A => M.c (ω t).1 (ω t).2) =ᵐ[pathMeasure M f.toPolicy i]
      (fun ω => ρ + h (ω t).1 - ∫ j, h j ∂M.P (ω t)) := by
    filter_upwards [admissible_time M f.toPolicy i t,stationary_action f i t] with ω ha hf
    rw [row_integral M h _ _ ((hacoe _).1 _ ha)]
    have hh := heq (ω t).1
    rw [← hf] at hh
    linarith
  have ic : Integrable (fun ω : ℕ → ℕ × A => M.c (ω t).1 (ω t).2) (pathMeasure M f.toPolicy i) :=
    (((integrable_const ρ).add ht).sub ik).congr he.symm
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable
    (M.c_meas.comp (measurable_pi_apply t)).aestronglyMeasurable (cost_nonneg_ae M f.toPolicy i t)).mpr ic,?_⟩
  rw [← stage_mean,integral_congr_ae he]
  change (∫ ω, ((fun _ : ℕ → ℕ × A => ρ) + (fun ω : ℕ → ℕ × A => h (ω t).1)) ω -
    (∫ j, h j ∂M.P (ω t)) ∂pathMeasure M f.toPolicy i) = _
  rw [integral_sub ((integrable_const ρ).add ht) ik]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const ρ) ht,← bias_next_integral M f.toPolicy i t h hn]
  simp [bias]
lemma telescope_eq (ρ : ℝ) (u : ℕ → ℝ) (N : ℕ) :
    (∑ t ∈ Finset.range N, (ρ + u t - u (t+1))) = (N : ℝ)*ρ + u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; push_cast; ring
lemma stationary_cost_identity (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (f : StationaryPolicy M) (heq : ∀ j, ρ + h j = M.c j (f.1 j) + ∑' k, prob M j (f.1 j) k * h k)
    (i : ℕ) (hint : ∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M f.toPolicy i)) (N : ℕ) :
    costN M f.toPolicy N i = ENNReal.ofReal ((N : ℝ)*ρ + h i - bias M f.toPolicy i h N) := by
  have hs := fun t => stationary_stage M ρ h hacoe f heq i t (hint t) (hint (t+1))
  have hc : costN M f.toPolicy N i ≠ ⊤ := by
    rw [finite_stage_sum]
    exact ENNReal.sum_ne_top.mpr (fun t ht => (hs t).1)
  have hr : (costN M f.toPolicy N i).toReal = (N : ℝ)*ρ + h i - bias M f.toPolicy i h N := by
    rw [cost_toReal_sum M f.toPolicy N i hc]
    simp_rw [(fun t => (hs t).2)]
    rw [telescope_eq]
    simp only [bias,bias_initial]
  rw [← hr,ENNReal.ofReal_toReal hc]
#print axioms finite_cost_lower
#print axioms stationary_cost_identity
end RossAverage

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RossAverage
open ArapostathisAC.RossReduction RossPath RossVerification
lemma real_normalized_limit (ρ x : ℝ) (u : ℕ → ℝ)
    (hu : Tendsto (fun N : ℕ => u N / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ρ + x/(N : ℝ) - u N/(N : ℝ)) atTop (𝓝 ρ) := by
  have hx : Tendsto (fun N : ℕ => x/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds.add hx).sub hu
lemma normalized_eq (ρ x : ℝ) (u : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((N : ℝ)*ρ+x-u N) =
      ENNReal.ofReal (ρ+x/(N : ℝ)-u N/(N : ℝ)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    _ = ENNReal.ofReal ((N : ℝ)*ρ+x-u N) / ENNReal.ofReal (N : ℝ) := by
      simp [div_eq_mul_inv,mul_comm]
    _ = ENNReal.ofReal (((N : ℝ)*ρ+x-u N)/(N : ℝ)) := (ENNReal.ofReal_div_of_pos hn).symm
    _ = _ := by congr 1; field_simp [ne_of_gt hn]
lemma normalized_limit (ρ x : ℝ) (u : ℕ → ℝ)
    (hu : Tendsto (fun N : ℕ => u N/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((N : ℝ)*ρ+x-u N))
      atTop (𝓝 (ENNReal.ofReal ρ)) := by
  have hl := ENNReal.continuous_ofReal.tendsto ρ |>.comp (real_normalized_limit ρ x u hu)
  apply hl.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (normalized_eq ρ x u N (by omega)).symm
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
lemma average_lower (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (π : Policy M) (i : ℕ)
    (hint : ∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i))
    (hv : Tendsto (fun t : ℕ => bias M π i h t/(t : ℝ)) atTop (𝓝 0)) :
    ENNReal.ofReal ρ ≤ avgCost M π i := by
  have hm : (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((N : ℝ)*ρ+h i-bias M π i h N)) ≤ᶠ[atTop]
      (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * costN M π N i) :=
    Filter.Eventually.of_forall fun N => mul_le_mul_right (finite_cost_lower M ρ h hacoe π i hint N) _
  have hl := Filter.limsup_le_limsup hm
  rw [(normalized_limit ρ (h i) (bias M π i h) hv).limsup_eq] at hl
  exact hl
lemma stationary_average (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (f : StationaryPolicy M) (heq : ∀ j, ρ+h j = M.c j (f.1 j) + ∑' k, prob M j (f.1 j) k*h k)
    (i : ℕ) (hint : ∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M f.toPolicy i))
    (hv : Tendsto (fun t : ℕ => bias M f.toPolicy i h t/(t : ℝ)) atTop (𝓝 0)) :
    avgCost M f.toPolicy i = ENNReal.ofReal ρ := by
  unfold avgCost
  simp_rw [stationary_cost_identity M ρ h hacoe f heq i hint]
  exact (normalized_limit ρ (h i) (bias M f.toPolicy i h) hv).limsup_eq
lemma rho_nonneg (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (f : StationaryPolicy M) (heq : ∀ j, ρ+h j = M.c j (f.1 j) + ∑' k, prob M j (f.1 j) k*h k)
    (i : ℕ) (hint : ∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M f.toPolicy i))
    (hv : Tendsto (fun t : ℕ => bias M f.toPolicy i h t/(t : ℝ)) atTop (𝓝 0)) : 0 ≤ ρ := by
  have hnum (N : ℕ) : 0 ≤ (N : ℝ)*ρ+h i-bias M f.toPolicy i h N := by
    have hs : 0 ≤ ∑ t ∈ Finset.range N, (stage M f.toPolicy i t).toReal :=
      Finset.sum_nonneg fun t ht => ENNReal.toReal_nonneg
    simp_rw [(fun t => (stationary_stage M ρ h hacoe f heq i t (hint t) (hint (t+1))).2)] at hs
    rw [telescope_eq] at hs
    simpa only [bias,bias_initial] using hs
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (real_normalized_limit ρ (h i) (bias M f.toPolicy i h) hv)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hh := div_nonneg (hnum N) hn.le
  have he : ((N : ℝ)*ρ+h i-bias M f.toPolicy i h N)/(N : ℝ) =
      ρ+h i/(N : ℝ)-bias M f.toPolicy i h N/(N : ℝ) := by field_simp [ne_of_gt hn]
  rwa [he] at hh
#print axioms average_lower
#print axioms stationary_average
#print axioms rho_nonneg
end RossAverage

open MeasureTheory Filter Topology ArapostathisAC.RossReduction RossAverage
noncomputable section
theorem average_verification {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (hint : ∀ (π : Policy M) (i t : ℕ),
      Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i))
    (hvanish : ∀ (π : Policy M) (i : ℕ),
      Tendsto (fun t : ℕ =>
        (∫ ω, h (ω t).1 ∂(pathMeasure M π i)) / (t : ℝ)) atTop (𝓝 0)) :
    0 ≤ ρ ∧
    (∃ f : ℕ → A, AverageOptimalFor M f ∧
      ∀ i, optAvg M i = ENNReal.ofReal ρ) ∧
    (∀ f : ℕ → A, (∀ i, f i ∈ M.U i) →
      (∀ i, ρ + h i = M.c i (f i) + ∑' j, prob M i (f i) j * h j) →
      AverageOptimalFor M f) := by
  choose f hf heq using fun j => (hacoe j).2.1
  let f₀ : StationaryPolicy M := ⟨f,hf⟩
  have low (π : Policy M) (i : ℕ) : ENNReal.ofReal ρ ≤ avgCost M π i :=
    average_lower M ρ h hacoe π i (hint π i) (hvanish π i)
  have eqv (g : StationaryPolicy M)
      (hg : ∀ j, ρ + h j = M.c j (g.1 j) + ∑' k, prob M j (g.1 j) k * h k) (i : ℕ) :
      avgCost M g.toPolicy i = ENNReal.ofReal ρ :=
    stationary_average M ρ h hacoe g hg i (hint g.toPolicy i) (hvanish g.toPolicy i)
  have opt (i : ℕ) : optAvg M i = ENNReal.ofReal ρ :=
    le_antisymm ((iInf_le _ f₀.toPolicy).trans_eq (eqv f₀ heq i)) (le_iInf (fun π => low π i))
  refine ⟨rho_nonneg M ρ h hacoe f₀ heq 0 (hint f₀.toPolicy 0) (hvanish f₀.toPolicy 0),?_,?_⟩
  · exact ⟨f,⟨hf,fun i => (eqv f₀ heq i).trans (opt i).symm⟩,opt⟩
  · intro g hg he
    exact ⟨hg,fun i => (eqv ⟨g,hg⟩ he i).trans (opt i).symm⟩
#print axioms average_verification

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace RossTransfer
open ArapostathisAC.RossReduction RossPath RossVerification
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
lemma initial_stationary (M : CMP A) (f : StationaryPolicy M) (i : ℕ)
    (g : ℕ × A → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω,g (ω 0) ∂pathMeasure M f.toPolicy i) = g (i,f.1 i) := by
  rw [← lintegral_map hg (measurable_pi_apply 0),initial_marginal]
  rw [initMeasure,lintegral_map hg (show Measurable (fun a : A => (i,a)) from measurable_const.prodMk measurable_id)]
  simp [StationaryPolicy.toPolicy,Kernel.deterministic_apply]
lemma stage_zero (M : CMP A) (f : StationaryPolicy M) (i : ℕ) :
    stage M f.toPolicy i 0 = ENNReal.ofReal (M.c i (f.1 i)) :=
  initial_stationary M f i (fun p => ENNReal.ofReal (M.c p.1 p.2)) M.c_meas.ennreal_ofReal
lemma potential_one (M : CMP A) (f : StationaryPolicy M) (i : ℕ) (v : ℕ → ℝ≥0∞) :
    potential M f.toPolicy i v 1 = ∫⁻ j,v j ∂M.P (i,f.1 i) := by
  rw [potential,state_transition M f.toPolicy i 0 v]
  exact initial_stationary M f i (fun p => ∫⁻ j,v j ∂M.P p)
    ((measurable_of_countable v).lintegral_kernel)
lemma first_step_lower (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (v : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (hB : B ≠ ⊤) (hv : ∀ j,v j ≤ B)
    (hsub : ∀ j a,a ∈ M.U j → v j ≤ ENNReal.ofReal (M.c j a) +
      ENNReal.ofReal β * ∫⁻ k,v k ∂M.P (j,a)) (f : StationaryPolicy M) (i : ℕ) :
    ENNReal.ofReal (M.c i (f.1 i)) + ENNReal.ofReal β * (∫⁻ j,v j ∂M.P (i,f.1 i)) ≤
      discCost M f.toPolicy β i := by
  have htail := infinite_lower (ENNReal.ofReal β) B (ENNReal.ofReal_lt_one.mpr hb1) hB
    (fun t => potential M f.toPolicy i v (t+1)) (fun t => stage M f.toPolicy i (t+1))
    (fun t => potential_bound M f.toPolicy i v B hv (t+1))
    (fun t => expected_lower M f.toPolicy i v (ENNReal.ofReal β) hsub (t+1))
  change potential M f.toPolicy i v 1 ≤ _ at htail
  rw [potential_one] at htail
  rw [discounted_stage_sum M f.toPolicy β hb i,tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero,one_mul,stage_zero]
  apply add_le_add le_rfl
  calc
    _ ≤ ENNReal.ofReal β * ∑' t, (ENNReal.ofReal β)^t * stage M f.toPolicy i (t+1) := by gcongr
    _ = ∑' t,(ENNReal.ofReal β)^(t+1) * stage M f.toPolicy i (t+1) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro t
      rw [pow_succ]
      ring
lemma optimal_attains (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (v : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (hB : B ≠ ⊤) (hv : ∀ j,v j ≤ B)
    (hsub : ∀ j a,a ∈ M.U j → v j ≤ ENNReal.ofReal (M.c j a) +
      ENNReal.ofReal β * ∫⁻ k,v k ∂M.P (j,a))
    (he : ∀ i,discValue M β i = v i) (f : StationaryPolicy M) (hf : DiscountOptimal M β f) (i : ℕ) :
    v i = ENNReal.ofReal (M.c i (f.1 i)) + ENNReal.ofReal β * ∫⁻ j,v j ∂M.P (i,f.1 i) := by
  apply le_antisymm (hsub i (f.1 i) (f.2 i))
  exact (first_step_lower M β hb hb1 v B hB hv hsub f i).trans_eq ((hf i).trans (he i))
#print axioms optimal_attains
end RossTransfer

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace RossTransfer
open ArapostathisAC.RossReduction RossPath RossVerification RossAverage
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
lemma real_optimal_attains (M : CMP A) (β : ℝ) (hb : 0 ≤ β) (hb1 : β < 1)
    (v : ℕ → ℝ) (B : ℝ) (hn : ∀ i,0 ≤ v i) (hbound : ∀ i,|v i| ≤ B)
    (hsub : ∀ i a,a ∈ M.U i → v i ≤ M.c i a + β * ∑' j,prob M i a j * v j)
    (he : ∀ i,discValue M β i = ENNReal.ofReal (v i))
    (f : StationaryPolicy M) (hf : DiscountOptimal M β f) (i : ℕ) :
    v i = M.c i (f.1 i) + β * ∑' j,prob M i (f.1 i) j * v j := by
  have hsum (i : ℕ) (a : A) : 0 ≤ ∑' j,prob M i a j * v j :=
    tsum_nonneg fun j => mul_nonneg ENNReal.toReal_nonneg (hn j)
  have hr (i : ℕ) (a : A) (ha : a ∈ M.U i) :
      ENNReal.ofReal (M.c i a + β * ∑' j,prob M i a j * v j) =
      ENNReal.ofReal (M.c i a) + ENNReal.ofReal β * ∫⁻ j,ENNReal.ofReal (v j) ∂M.P (i,a) := by
    rw [ENNReal.ofReal_add (M.c_nonneg i a ha) (mul_nonneg hb (hsum i a)),
      ENNReal.ofReal_mul hb,real_row_expectation M v B hn hbound i a]
  have hs (i : ℕ) (a : A) (ha : a ∈ M.U i) :
      ENNReal.ofReal (v i) ≤ ENNReal.ofReal (M.c i a) + ENNReal.ofReal β *
        ∫⁻ j,ENNReal.ofReal (v j) ∂M.P (i,a) := by
    rw [← hr i a ha]
    exact ENNReal.ofReal_le_ofReal (hsub i a ha)
  have hh := optimal_attains M β hb hb1 (fun i => ENNReal.ofReal (v i)) (ENNReal.ofReal B)
    ENNReal.ofReal_ne_top (fun i => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hbound i))) hs he f hf i
  rw [← hr i (f.1 i) (f.2 i)] at hh
  have ht := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (hn i),ENNReal.toReal_ofReal
    (add_nonneg (M.c_nonneg i (f.1 i) (f.2 i)) (mul_nonneg hb (hsum i (f.1 i))))] using ht
lemma bounded_bias_integrable (M : CMP A) (h : ℕ → ℝ) (B : ℝ) (hb : ∀ i,|h i| ≤ B)
    (π : Policy M) (i t : ℕ) :
    Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i) := by
  apply (integrable_const B).mono'
    (((measurable_of_countable h).comp ((measurable_pi_apply t).fst)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb (ω t).1
lemma bounded_bias_vanishes (M : CMP A) (h : ℕ → ℝ) (B : ℝ) (hb : ∀ i,|h i| ≤ B)
    (π : Policy M) (i : ℕ) :
    Tendsto (fun t : ℕ => (∫ ω,h (ω t).1 ∂pathMeasure M π i)/(t : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℕ => B/(t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm _ hlim
  intro t
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (show 0 ≤ (t : ℝ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∫ ω, |h (ω t).1| ∂pathMeasure M π i := abs_integral_le_integral_abs
    _ ≤ ∫ _ω : ℕ → ℕ × A,B ∂pathMeasure M π i :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
        (integrable_const B) (Filter.Eventually.of_forall fun ω => hb _)
    _ = B := by simp
#print axioms real_optimal_attains
#print axioms bounded_bias_vanishes
end RossTransfer

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace RossResidual
lemma atom_le (μ : Measure ℕ) (a : ℝ≥0∞) (ha : a ≤ μ {0}) :
    a • Measure.dirac 0 ≤ μ := by
  intro s
  by_cases h : 0 ∈ s
  · simpa [Measure.smul_apply, Measure.dirac_apply_of_mem h] using
      ha.trans (measure_mono (singleton_subset_iff.mpr h))
  · simp [Measure.smul_apply, Measure.dirac_apply, h]

def residual {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) (a : ℝ≥0∞) : X → Measure ℕ :=
  fun x => if a ≤ P x {0} then (1-a)⁻¹ • (P x - a • Measure.dirac 0) else P x

lemma residual_apply {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) (a : ℝ≥0∞)
    (ha : a ≠ ∞) (x : X) (s : Set ℕ) :
    residual P a x s = if a ≤ P x {0} then (1-a)⁻¹ * (P x s - a * Measure.dirac 0 s) else P x s := by
  classical
  letI : IsFiniteMeasure (a • Measure.dirac (0 : ℕ)) := ⟨by simp [ha.lt_top]⟩
  by_cases h : a ≤ P x {0}
  · simp [residual, h, Measure.smul_apply, Measure.sub_apply ((Set.to_countable s).measurableSet) (atom_le _ _ h)]
  · simp [residual, h]

def kernel {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) (a : ℝ≥0∞)
    (ha : a ≠ ∞) : Kernel X ℕ where
  toFun := residual P a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [residual_apply P a ha]
    exact Measurable.ite (measurableSet_le measurable_const (P.measurable_coe (measurableSet_singleton 0)))
      (measurable_const.mul ((P.measurable_coe hs).sub measurable_const)) (P.measurable_coe hs)

lemma markov {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) [IsMarkovKernel P]
    (a : ℝ≥0∞) (ha : a < 1) : IsMarkovKernel (kernel P a (ha.trans_le le_top).ne) := by
  constructor
  intro x
  constructor
  change residual P a x univ = 1
  rw [residual_apply P a (ha.trans_le le_top).ne]
  split_ifs
  · simp only [measure_univ, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
    exact ENNReal.inv_mul_cancel (tsub_pos_iff_lt.mpr ha).ne' (by finiteness)
  · exact measure_univ
end RossResidual

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace RossResidual
open ArapostathisAC.RossReduction
lemma probability {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0)
    (i : ℕ) (a : A) (ha : a ∈ M.U i) (j : ℕ) :
    ((kernel M.P (ENNReal.ofReal α) ENNReal.ofReal_ne_top) (i,a) {j}).toReal =
      (prob M i a j - if j = 0 then α else 0) / (1-α) := by
  have h : ENNReal.ofReal α ≤ M.P (i,a) {0} :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hP i a ha)
  change (residual M.P (ENNReal.ofReal α) (i,a) {j}).toReal = _
  rw [residual_apply M.P _ ENNReal.ofReal_ne_top, if_pos h]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le (ENNReal.ofReal_lt_one.mpr hα1).le ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal hα.le]
  by_cases hj : j = 0
  · subst j
    simp only [Measure.dirac_apply_of_mem (mem_singleton 0), mul_one, if_true]
    rw [ENNReal.toReal_sub_of_le h (measure_ne_top _ _), ENNReal.toReal_ofReal hα.le]
    simp [prob, div_eq_mul_inv, mul_comm]
  · simp [Measure.dirac_apply, hj, Ne.symm hj, prob, div_eq_mul_inv, mul_comm]
end RossResidual

open ArapostathisAC.RossReduction
 theorem modified_exists {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0) :
    ∃ M' : CMP A, ModifiedLaw M M' α := by
  let K := RossResidual.kernel M.P (ENNReal.ofReal α) ENNReal.ofReal_ne_top
  letI : IsMarkovKernel K := RossResidual.markov M.P _ (ENNReal.ofReal_lt_one.mpr hα1)
  have hp := RossResidual.probability M α hα hα1 hP
  let M' : CMP A := {
    U := M.U
    U_nonempty := M.U_nonempty
    U_compact := M.U_compact
    c := M.c
    c_meas := M.c_meas
    c_nonneg := M.c_nonneg
    P := K
    c_cont := M.c_cont
    P_cont := by
      intro i j
      apply ContinuousOn.congr ((M.P_cont i j).sub continuousOn_const |>.div_const (1-α))
      intro a ha
      exact hp i a ha j
  }
  exact ⟨M', rfl, fun _ _ _ => rfl, hp⟩

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.RossReduction
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Ross reduction, including transfer of every discounted-optimal stationary policy. -/
theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (C : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0) :
    ∃ M' : CMP A, ModifiedLaw M M' α ∧
      (∀ i, discValue M' (1 - α) i ≠ ⊤) ∧
      (∃ f : ℕ → A, DiscountOptimalFor M' (1 - α) f) ∧
      (∀ f : ℕ → A, DiscountOptimalFor M' (1 - α) f → AverageOptimalFor M f) ∧
      (∀ i, optAvg M i = ENNReal.ofReal (α * (discValue M' (1 - α) 0).toReal)) := by
  obtain ⟨M',hmod⟩ := modified_exists M α hα hα1 hP
  have hc' : ∀ i,∀ a ∈ M'.U i,M'.c i a ≤ C := by
    intro i a ha
    have ha' : a ∈ M.U i := by simpa [hmod.1] using ha
    rw [hmod.2.1 i a ha']
    exact hc i a ha'
  obtain ⟨v,B,hn,hbound,hBell⟩ := RossExistence.bounded_bellman_exists M' (1-α)
    (by linarith) (by linarith) C hc'
  have hv := RossVerification.real_bellman_identification M' (1-α)
    (by linarith) (by linarith) v B hn hbound hBell
  have hacoe := RossBellman.bellman_to_acoe M M' α hα1 hmod v B hbound hBell
  have havg := average_verification M (α*v 0) v hacoe
    (RossTransfer.bounded_bias_integrable M v B hbound)
    (RossTransfer.bounded_bias_vanishes M v B hbound)
  refine ⟨M',hmod,?_,?_,?_,?_⟩
  · intro i
    rw [hv.1 i]
    exact ENNReal.ofReal_ne_top
  · obtain ⟨f,hf,_⟩ := hv.2
    exact ⟨f.1,f.2,hf⟩
  · intro f hf
    obtain ⟨hadm,hopt⟩ := hf
    have hadm' : ∀ i,f i ∈ M.U i := by
      intro i
      simpa [hmod.1] using hadm i
    apply havg.2.2 f hadm'
    intro i
    have he := RossTransfer.real_optimal_attains M' (1-α) (by linarith) (by linarith)
      v B hn hbound (fun i a ha => (hBell i).2 a ha) hv.1 ⟨f,hadm⟩ hopt i
    change v i = M'.c i (f i) + (1-α) * ∑' j,prob M' i (f i) j * v j at he
    rw [hmod.2.1 i (f i) (hadm' i),RossBellman.expectation M M' α hα1 hmod v B hbound i (f i) (hadm' i)] at he
    linarith
  · intro i
    rw [hv.1 0,ENNReal.toReal_ofReal (hn 0)]
    exact havg.2.1.choose_spec.2 i
#print axioms solution
