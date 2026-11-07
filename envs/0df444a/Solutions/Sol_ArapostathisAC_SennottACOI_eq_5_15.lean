-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.eq_5_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:41:16.6211+00:00
-- url     : https://prove2.me/submissions/341396f0-eb82-484a-aa63-362527b73e1b

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.SennottACOI

namespace SennottMarkovAux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The state transition kernel of the chain under a stationary policy. -/
noncomputable def Q (M : ArapostathisAC.VanishingDiscount.CMP A) (f : ℕ → A) : Kernel ℕ ℕ where
  toFun k := M.P (k, f k)
  measurable' := measurable_of_countable _

instance (M : ArapostathisAC.VanishingDiscount.CMP A) (f : ℕ → A) : IsMarkovKernel (Q M f) :=
  ⟨fun k => (inferInstance : IsProbabilityMeasure (M.P (k, f k)))⟩

/-- `t`-step state kernel. -/
noncomputable def Qn (M : ArapostathisAC.VanishingDiscount.CMP A) (f : ℕ → A) : ℕ → Kernel ℕ ℕ
  | 0 => Kernel.id
  | t + 1 => Q M f ∘ₖ Qn M f t

instance (M : ArapostathisAC.VanishingDiscount.CMP A) (f : ℕ → A) (t : ℕ) :
    IsMarkovKernel (Qn M f t) := by
  induction t with
  | zero => simp only [Qn]; infer_instance
  | succ t ih => simp only [Qn]; infer_instance

lemma Qn_succ' (M : ArapostathisAC.VanishingDiscount.CMP A) (f : ℕ → A) (t : ℕ) :
    Qn M f (t + 1) = Qn M f t ∘ₖ Q M f := by
  induction t with
  | zero => simp [Qn, Kernel.comp_id, Kernel.id_comp]
  | succ t ih =>
    show Q M f ∘ₖ Qn M f (t + 1) = (Q M f ∘ₖ Qn M f t) ∘ₖ Q M f
    rw [ih, Kernel.comp_assoc]

lemma lintegral_Q (M : ArapostathisAC.VanishingDiscount.CMP A) (f : ℕ → A) (k : ℕ)
    (G : ℕ → ℝ≥0∞) : ∫⁻ j, G j ∂(Q M f k) = ∑' j, G j * M.P (k, f k) {j} := by
  rw [lintegral_countable']
  rfl

/-- One-step integral against the step kernel of a stationary policy. -/
lemma lintegral_stepKernel (M : ArapostathisAC.VanishingDiscount.CMP A)
    (f : ArapostathisAC.SennottACOI.StationaryPolicy M) (t : ℕ)
    (h : Π _ : Finset.Iic t, ℕ × A) {F : ℕ × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂(ArapostathisAC.VanishingDiscount.stepKernel M f.toPolicy t h) =
      ∫⁻ j, F (j, f.1 j) ∂(M.P (ArapostathisAC.VanishingDiscount.lastPair t h)) := by
  haveI : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t)
      (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
  rw [ArapostathisAC.VanishingDiscount.stepKernel, Kernel.lintegral_compProd _ _ _ hF]
  congr 1; funext j
  rw [Kernel.comap_apply]
  simp only [ArapostathisAC.SennottACOI.StationaryPolicy.toPolicy, Kernel.deterministic_apply]
  rw [lintegral_dirac]

/-- Law of the state–action pair at time `t` under a stationary policy. -/
theorem lintegral_path (M : ArapostathisAC.VanishingDiscount.CMP A)
    (f : ArapostathisAC.SennottACOI.StationaryPolicy M) (i : ℕ) (t : ℕ)
    {F : ℕ × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω t) ∂(ArapostathisAC.VanishingDiscount.pathMeasure M f.toPolicy i) =
      ∫⁻ j, F (j, f.1 j) ∂(Qn M f.1 t i) := by
  induction t generalizing F with
  | zero =>
    have hμ0 : IsProbabilityMeasure (ArapostathisAC.VanishingDiscount.initMeasure f.toPolicy i) := by
      unfold ArapostathisAC.VanishingDiscount.initMeasure
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    simp only [ArapostathisAC.VanishingDiscount.pathMeasure, Kernel.trajMeasure]
    have hF0 : Measurable (fun ω : ℕ → ℕ × A => F (ω 0)) := hF.comp (measurable_pi_apply 0)
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF0.aemeasurable]
    have hin : ∀ y : (Π _ : Finset.Iic 0, ℕ × A),
        ∫⁻ ω : ℕ → ℕ × A, F (ω 0) ∂(Kernel.traj (X := fun _ => ℕ × A) (ArapostathisAC.VanishingDiscount.stepKernel M f.toPolicy) 0 y)
          = F (y ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
      intro y
      rw [Kernel.lintegral_traj y hF0]
      have : ∀ x : ℕ → ℕ × A, Function.updateFinset x (Finset.Iic 0) y 0 = y ⟨0, Finset.mem_Iic.2 le_rfl⟩ := by
        intro x; simp [Function.updateFinset]
      simp only [this, lintegral_const, measure_univ, mul_one]
    rw [lintegral_congr (fun y => hin y)]
    rw [lintegral_map (f := fun a : (Π _ : Finset.Iic 0, ℕ × A) =>
      F (a ⟨0, Finset.mem_Iic.2 le_rfl⟩)) (hF.comp (measurable_pi_apply _))
      (MeasurableEquiv.measurable _)]
    simp only [MeasurableEquiv.piUnique_symm_apply]
    unfold ArapostathisAC.VanishingDiscount.initMeasure
    change ∫⁻ a, F a ∂ _ = _
    rw [lintegral_map hF measurable_prodMk_left]
    simp only [ArapostathisAC.SennottACOI.StationaryPolicy.toPolicy, Kernel.deterministic_apply,
      lintegral_dirac, Qn, Kernel.id_apply]
  | succ t ih =>
    set κ := ArapostathisAC.VanishingDiscount.stepKernel M f.toPolicy with hκ
    set μ0 := ArapostathisAC.VanishingDiscount.initMeasure f.toPolicy i with hμ0def
    have hμ0 : IsProbabilityMeasure μ0 := by
      rw [hμ0def]; unfold ArapostathisAC.VanishingDiscount.initMeasure
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    have hpath : ArapostathisAC.VanishingDiscount.pathMeasure M f.toPolicy i =
        Kernel.trajMeasure (X := fun _ => ℕ × A) μ0 κ := rfl
    rw [hpath]
    have key := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => ℕ × A) (μ₀ := μ0) (κ := κ) (a := t)
    have hFs : Measurable (fun p : (Π _ : Finset.Iic t, ℕ × A) × (ℕ × A) => F p.2) :=
      hF.comp measurable_snd
    have h1 : ∫⁻ ω, F (ω (t + 1)) ∂(Kernel.trajMeasure (X := fun _ => ℕ × A) μ0 κ) =
        ∫⁻ p, F p.2 ∂((Kernel.trajMeasure (X := fun _ => ℕ × A) μ0 κ).map
          (fun x => (Preorder.frestrictLe t x, x (t + 1)))) := by
      rw [lintegral_map hFs (by fun_prop)]
    rw [h1, ← key, Measure.lintegral_compProd hFs]
    have hG : Measurable (fun p : ℕ × A => ∫⁻ j, F (j, f.1 j) ∂(M.P p)) :=
      (measurable_of_countable (fun j => F (j, f.1 j))).lintegral_kernel
    have h2 : ∀ h : (Π _ : Finset.Iic t, ℕ × A), ∫⁻ z, F (h, z).2 ∂(κ t h) =
        (fun p : ℕ × A => ∫⁻ j, F (j, f.1 j) ∂(M.P p))
          (ArapostathisAC.VanishingDiscount.lastPair t h) := fun h =>
      lintegral_stepKernel M f t h hF
    have hGl : Measurable (fun h : (Π _ : Finset.Iic t, ℕ × A) =>
        (fun p : ℕ × A => ∫⁻ j, F (j, f.1 j) ∂(M.P p))
          (ArapostathisAC.VanishingDiscount.lastPair t h)) :=
      hG.comp (measurable_pi_apply _)
    rw [lintegral_congr h2, lintegral_map hGl (by fun_prop)]
    have h3 := ih hG
    rw [hpath] at h3
    change ∫⁻ ω : ℕ → ℕ × A, (fun p : ℕ × A => ∫⁻ j, F (j, f.1 j) ∂(M.P p)) (ω t) ∂_ = _
    rw [h3]
    show _ = ∫⁻ j, F (j, f.1 j) ∂((Q M f.1 ∘ₖ Qn M f.1 t) i)
    rw [Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
    rfl

end SennottMarkovAux

lemma sennott_prob_hasSum {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (i : ℕ) (a : A) :
    HasSum (fun j => ArapostathisAC.VanishingDiscount.prob M i a j) 1 := by
  have h1 : ∑' j, M.P (i, a) {j} = 1 := by
    have := Measure.tsum_indicator_apply_singleton (M.P (i, a)) Set.univ MeasurableSet.univ
    simpa [Set.indicator_univ] using this
  have h2 := ENNReal.hasSum_toReal (f := fun j => M.P (i, a) {j}) (by rw [h1]; simp)
  rw [← ENNReal.tsum_toReal_eq (fun j => measure_ne_top _ _), h1] at h2
  simpa [ArapostathisAC.VanishingDiscount.prob] using h2


open SennottMarkovAux

/-- The discounted cost of a stationary policy satisfies the policy evaluation equation. -/
lemma sennott_disc_eval {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (f : StationaryPolicy M) (β : ℝ) (hβ : 0 ≤ β)
    (k : ℕ) :
    ArapostathisAC.VanishingDiscount.discCost M f.toPolicy β k =
      ENNReal.ofReal (M.c k (f.1 k)) + ENNReal.ofReal β *
        ∑' j, M.P (k, f.1 k) {j} * ArapostathisAC.VanishingDiscount.discCost M f.toPolicy β j := by
  set c' : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (M.c k (f.1 k)) with hc'
  set C : ℕ → ℕ → ℝ≥0∞ := fun t k => ∫⁻ j, c' j ∂(Qn M f.1 t k) with hC
  set b' := ENNReal.ofReal β with hb'
  have hD : ∀ k, ArapostathisAC.VanishingDiscount.discCost M f.toPolicy β k =
      ∑' t, b' ^ t * C t k := by
    intro k
    unfold ArapostathisAC.VanishingDiscount.discCost
    have hm2 : ∀ t, AEMeasurable
        (fun ω : ℕ → ℕ × A => ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2))
        (ArapostathisAC.VanishingDiscount.pathMeasure M f.toPolicy k) := fun t =>
      (measurable_const.mul (M.c_meas.comp (measurable_pi_apply t))).ennreal_ofReal.aemeasurable
    rw [lintegral_tsum hm2]
    congr 1; funext t
    have : ∀ ω : ℕ → ℕ × A, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) =
        b' ^ t * ENNReal.ofReal (M.c (ω t).1 (ω t).2) := by
      intro ω
      rw [ENNReal.ofReal_mul (pow_nonneg hβ t), ENNReal.ofReal_pow hβ]
    simp_rw [this]
    have hmt : Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
      (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal
    rw [lintegral_const_mul _ hmt]
    congr 1
    exact lintegral_path M f k t (F := fun p : ℕ × A => ENNReal.ofReal (M.c p.1 p.2))
      M.c_meas.ennreal_ofReal
  have hC0 : ∀ k, C 0 k = c' k := fun k => by
    simp [hC, Qn, Kernel.id_apply, lintegral_dirac]
  have hCs : ∀ t k, C (t + 1) k = ∫⁻ j, C t j ∂(Q M f.1 k) := by
    intro t k
    simp only [hC]
    rw [Qn_succ', Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
  refine (hD k).trans ?_
  rw [tsum_eq_zero_add' (f := fun t => b' ^ t * C t k) ENNReal.summable]
  rw [pow_zero, one_mul, hC0]
  congr 1
  have h1 : ∑' j, M.P (k, f.1 k) {j} * ArapostathisAC.VanishingDiscount.discCost M f.toPolicy β j
      = ∫⁻ j, (∑' t, b' ^ t * C t j) ∂(Q M f.1 k) := by
    rw [lintegral_Q]
    congr 1; funext j; rw [hD j, mul_comm]
  rw [h1, lintegral_tsum (fun t => (measurable_of_countable _).aemeasurable),
    ← ENNReal.tsum_mul_left]
  congr 1; funext t
  rw [lintegral_const_mul _ (measurable_of_countable _), hCs, pow_succ]
  ring

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : ∀ i, ArapostathisAC.VanishingDiscount.discValue M β i ≠ ⊤) (f : StationaryPolicy M) (hf : ArapostathisAC.VanishingDiscount.IsDiscOptimal M β f)
    (i : ℕ) :
    Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * ArapostathisAC.VanishingDiscount.hRel M β j) ∧
    (1 - β) * (ArapostathisAC.VanishingDiscount.discValue M β 0).toReal + ArapostathisAC.VanishingDiscount.hRel M β i =
      M.c i (f.1 i) + β * ∑' j, ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * ArapostathisAC.VanishingDiscount.hRel M β j := by
  set J := ArapostathisAC.VanishingDiscount.discValue M β with hJ
  have hfJ : ∀ k, ArapostathisAC.VanishingDiscount.discCost M f.toPolicy β k = J k := hf
  have hev := sennott_disc_eval M f β hβ.1.le i
  simp only [hfJ] at hev
  -- the ENNReal series is finite
  set X := ∑' j, M.P (i, f.1 i) {j} * J j with hX
  have hb'pos : ENNReal.ofReal β ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hβ.1
  have hXfin : X ≠ ⊤ := by
    intro hXt
    apply hfin i
    rw [hev, hXt, ENNReal.mul_top hb'pos]
    simp
  have hterm : ∀ j, M.P (i, f.1 i) {j} * J j ≠ ⊤ := fun j =>
    ENNReal.mul_ne_top (measure_ne_top _ _) (hfin j)
  have hXr : HasSum (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * (J j).toReal)
      X.toReal := by
    have := ENNReal.hasSum_toReal hXfin
    rw [hX, ENNReal.tsum_toReal_eq hterm]
    refine (this.congr_fun (fun j => ?_))
    simp [ArapostathisAC.VanishingDiscount.prob, ENNReal.toReal_mul]
  have hJi : (J i).toReal = M.c i (f.1 i) + β * X.toReal := by
    rw [hev, ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (M.c_nonneg i (f.1 i) (f.2 i)),
      ENNReal.toReal_ofReal hβ.1.le]
  have hP := sennott_prob_hasSum M i (f.1 i)
  have hH : HasSum (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j *
      ArapostathisAC.VanishingDiscount.hRel M β j) (X.toReal - 1 * (J 0).toReal) := by
    have := hXr.sub (hP.mul_right (J 0).toReal)
    refine this.congr_fun (fun j => ?_)
    simp only [ArapostathisAC.VanishingDiscount.hRel, hJ]; ring
  refine ⟨hH.summable, ?_⟩
  rw [hH.tsum_eq]
  simp only [ArapostathisAC.VanishingDiscount.hRel, ← hJ]
  rw [hJi]
  ring
