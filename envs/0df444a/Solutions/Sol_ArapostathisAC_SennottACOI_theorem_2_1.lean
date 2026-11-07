-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:46:33.77304+00:00
-- url     : https://prove2.me/submissions/dec1252f-bcc5-45ec-be74-59ef8515a3b9

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP

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

namespace SennottDCOEAux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The one-step cost-to-go `c(i,a) + β Σ_j P(j | i, a) v(j)`. -/
noncomputable def w (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞)
    (i : ℕ) (a : A) : ℝ≥0∞ :=
  ENNReal.ofReal (M.c i a) + ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * v j

/-- The dynamic programming operator `T`. -/
noncomputable def T (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞)
    (i : ℕ) : ℝ≥0∞ :=
  ⨅ a ∈ M.U i, w M β v i a

/-- Value iteration from `0`. -/
noncomputable def vseq (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) : ℕ → ℕ → ℝ≥0∞
  | 0 => fun _ => 0
  | k + 1 => T M β (vseq M β k)

lemma w_mono (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) {v v' : ℕ → ℝ≥0∞}
    (h : v ≤ v') (i : ℕ) (a : A) : w M β v i a ≤ w M β v' i a := by
  unfold w
  gcongr with j
  exact h j

lemma T_mono (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) {v v' : ℕ → ℝ≥0∞}
    (h : v ≤ v') : T M β v ≤ T M β v' := fun i => by
  unfold T
  exact iInf₂_mono (fun a _ => w_mono M β h i a)

lemma vseq_mono (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) :
    Monotone (vseq M β) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  induction k with
  | zero => intro i; exact bot_le
  | succ k ih => exact T_mono M β ih

lemma w_tsum_eq_lintegral (M : ArapostathisAC.VanishingDiscount.CMP A) (v : ℕ → ℝ≥0∞)
    (p : ℕ × A) : ∑' j, M.P p {j} * v j = ∫⁻ j, v j ∂(M.P p) := by
  rw [lintegral_countable']
  congr 1; funext j; rw [mul_comm]

lemma w_measurable (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) :
    Measurable (fun p : ℕ × A => w M β v p.1 p.2) := by
  unfold w
  refine (M.c_meas.ennreal_ofReal).add (measurable_const.mul ?_)
  have : (fun p : ℕ × A => ∑' j, M.P (p.1, p.2) {j} * v j) =
      fun p => ∫⁻ j, v j ∂(M.P p) := by
    funext p; exact w_tsum_eq_lintegral M v p
  rw [this]
  exact (measurable_of_countable v).lintegral_kernel

lemma lsc_ofReal_mul (g : A → ℝ) (s : Set A) (hg : ContinuousOn g s) (C : ℝ≥0∞) :
    LowerSemicontinuousOn (fun a => ENNReal.ofReal (g a) * C) s := by
  have hC : C = ⨆ n : ℕ, min C (n : ℝ≥0∞) := by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]; simp
  have : (fun a => ENNReal.ofReal (g a) * C) =
      fun a => ⨆ n : ℕ, ENNReal.ofReal (g a) * min C (n : ℝ≥0∞) := by
    funext a; rw [← ENNReal.mul_iSup, ← hC]
  rw [this]
  refine lowerSemicontinuousOn_iSup (fun n => ?_)
  refine ContinuousOn.lowerSemicontinuousOn ?_
  exact (ENNReal.continuous_mul_const (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
    (min_le_right _ _))).comp_continuousOn (ENNReal.continuous_ofReal.comp_continuousOn hg)

lemma w_lsc (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) :
    LowerSemicontinuousOn (w M β v i) (M.U i) := by
  unfold w
  refine LowerSemicontinuousOn.add ?_ ?_
  · exact (ENNReal.continuous_ofReal.comp_continuousOn (M.c_cont i)).lowerSemicontinuousOn
  · have : (fun a => ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * v j) =
        fun a => ∑' j, ENNReal.ofReal (ArapostathisAC.VanishingDiscount.prob M i a j) *
          (ENNReal.ofReal β * v j) := by
      funext a
      rw [← ENNReal.tsum_mul_left]
      congr 1; funext j
      simp only [ArapostathisAC.VanishingDiscount.prob,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      ring
    rw [this]
    exact lowerSemicontinuousOn_tsum (fun j => lsc_ofReal_mul _ _ (M.P_cont i j) _)

lemma exists_min (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) :
    ∃ a ∈ M.U i, T M β v i = w M β v i a := by
  obtain ⟨a, ha, hmin⟩ := (w_lsc M β v i).exists_isMinOn (M.U_nonempty i) (M.U_compact i)
  refine ⟨a, ha, le_antisymm (iInf₂_le a ha) (le_iInf₂ (fun b hb => hmin hb))⟩

lemma w_iSup (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (i : ℕ) (a : A) :
    w M β (fun j => ⨆ k, vseq M β k j) i a = ⨆ k, w M β (vseq M β k) i a := by
  unfold w
  rw [← ENNReal.add_iSup, ← ENNReal.mul_iSup]
  congr 2
  rw [w_tsum_eq_lintegral M (fun j => ⨆ k, vseq M β k j)]
  have hmono : Monotone (fun k => fun j => vseq M β k j) := fun k k' hkk' j => vseq_mono M β hkk' j
  rw [lintegral_iSup (fun k => measurable_of_countable _) hmono]
  congr 1; funext k; rw [w_tsum_eq_lintegral]

lemma T_vinf_le (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (i : ℕ) :
    T M β (fun j => ⨆ k, vseq M β k j) i ≤ ⨆ k, vseq M β k i := by
  choose a ha hmin using fun k => exists_min M β (vseq M β k) i
  obtain ⟨a0, ha0, φ, hφ, hlim⟩ := (M.U_compact i).tendsto_subseq ha
  refine (iInf₂_le a0 ha0).trans ?_
  rw [w_iSup]
  refine iSup_le (fun m => ?_)
  by_contra hcon
  push Not at hcon
  have hlsc := w_lsc M β (vseq M β m) i a0 ha0 _ hcon
  have hlimw : Tendsto (fun k => a (φ k)) atTop (𝓝[M.U i] a0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall (fun k => ha (φ k))⟩
  have h1 := hlimw.eventually hlsc
  have h2 : ∀ᶠ k in atTop, m ≤ φ k := hφ.tendsto_atTop.eventually (eventually_ge_atTop m)
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  have : w M β (vseq M β m) i (a (φ k)) ≤ ⨆ k, vseq M β k i :=
    calc w M β (vseq M β m) i (a (φ k)) ≤ w M β (vseq M β (φ k)) i (a (φ k)) :=
          w_mono M β (vseq_mono M β hk2) i _
      _ = vseq M β (φ k + 1) i := by rw [← hmin]; rfl
      _ ≤ ⨆ k, vseq M β k i := le_iSup (fun k => vseq M β k i) (φ k + 1)
  exact absurd hk1 (not_lt.2 this)

lemma T_vinf (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) :
    T M β (fun j => ⨆ k, vseq M β k j) = fun j => ⨆ k, vseq M β k j := by
  funext i
  refine le_antisymm (T_vinf_le M β i) (iSup_le (fun k => ?_))
  have : vseq M β k ≤ vseq M β (k + 1) := vseq_mono M β (Nat.le_succ k)
  calc vseq M β k i ≤ vseq M β (k + 1) i := this i
    _ = T M β (vseq M β k) i := rfl
    _ ≤ T M β (fun j => ⨆ k, vseq M β k j) i :=
        T_mono M β (fun j => le_iSup (fun k => vseq M β k j) k) i

/-! ### The controlled process under a general policy -/

lemma lintegral_step_general (M : ArapostathisAC.VanishingDiscount.CMP A)
    (π : ArapostathisAC.VanishingDiscount.Policy M) (t : ℕ)
    (h : Π _ : Finset.Iic t, ℕ × A) {F : ℕ × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂(ArapostathisAC.VanishingDiscount.stepKernel M π t h) =
      ∫⁻ j, ∫⁻ a, F (j, a) ∂(π.rule (t + 1) (ArapostathisAC.VanishingDiscount.histFin t h, j))
        ∂(M.P (ArapostathisAC.VanishingDiscount.lastPair t h)) := by
  haveI : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t)
      (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
  rw [ArapostathisAC.VanishingDiscount.stepKernel, Kernel.lintegral_compProd _ _ _ hF]
  rfl

lemma lintegral_path_zero (M : ArapostathisAC.VanishingDiscount.CMP A)
    (π : ArapostathisAC.VanishingDiscount.Policy M) (i : ℕ)
    {F : ℕ × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂(ArapostathisAC.VanishingDiscount.pathMeasure M π i) =
      ∫⁻ a, F (i, a) ∂(π.rule 0 (fun j => j.elim0, i)) := by
  have hμ0 : IsProbabilityMeasure (ArapostathisAC.VanishingDiscount.initMeasure π i) := by
    unfold ArapostathisAC.VanishingDiscount.initMeasure
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  simp only [ArapostathisAC.VanishingDiscount.pathMeasure, Kernel.trajMeasure]
  have hF0 : Measurable (fun ω : ℕ → ℕ × A => F (ω 0)) := hF.comp (measurable_pi_apply 0)
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF0.aemeasurable]
  have hin : ∀ y : (Π _ : Finset.Iic 0, ℕ × A),
      ∫⁻ ω : ℕ → ℕ × A, F (ω 0) ∂(Kernel.traj (X := fun _ => ℕ × A)
        (ArapostathisAC.VanishingDiscount.stepKernel M π) 0 y)
        = F (y ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
    intro y
    rw [Kernel.lintegral_traj y hF0]
    have : ∀ x : ℕ → ℕ × A, Function.updateFinset x (Finset.Iic 0) y 0 =
        y ⟨0, Finset.mem_Iic.2 le_rfl⟩ := by
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

lemma lintegral_path_succ (M : ArapostathisAC.VanishingDiscount.CMP A)
    (π : ArapostathisAC.VanishingDiscount.Policy M) (i : ℕ) (t : ℕ)
    {F : ℕ × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω (t + 1)) ∂(ArapostathisAC.VanishingDiscount.pathMeasure M π i) =
      ∫⁻ ω, ∫⁻ z, F z ∂(ArapostathisAC.VanishingDiscount.stepKernel M π t
        (Preorder.frestrictLe t ω)) ∂(ArapostathisAC.VanishingDiscount.pathMeasure M π i) := by
  set κ := ArapostathisAC.VanishingDiscount.stepKernel M π with hκ
  set μ0 := ArapostathisAC.VanishingDiscount.initMeasure π i with hμ0def
  have hμ0 : IsProbabilityMeasure μ0 := by
    rw [hμ0def]; unfold ArapostathisAC.VanishingDiscount.initMeasure
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hpath : ArapostathisAC.VanishingDiscount.pathMeasure M π i =
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
  have hGl : Measurable (fun h : (Π _ : Finset.Iic t, ℕ × A) => ∫⁻ z, F z ∂(κ t h)) :=
    hF.lintegral_kernel
  rw [lintegral_map hGl (by fun_prop)]

/-- Under any admissible policy the action at time `t` is admissible almost surely. -/
lemma ae_adm (M : ArapostathisAC.VanishingDiscount.CMP A)
    (π : ArapostathisAC.VanishingDiscount.Policy M) (i : ℕ) (t : ℕ) :
    ∀ᵐ ω ∂(ArapostathisAC.VanishingDiscount.pathMeasure M π i), (ω t).2 ∈ M.U (ω t).1 := by
  set Bad : Set (ℕ × A) := {p | p.2 ∉ M.U p.1} with hBad
  have hBm : MeasurableSet Bad := by
    have : Bad = ⋃ x : ℕ, ({x} : Set ℕ) ×ˢ (M.U x)ᶜ := by
      ext p; simp [hBad]
    rw [this]
    exact MeasurableSet.iUnion (fun x =>
      (measurableSet_singleton x).prod (M.U_compact x).isClosed.measurableSet.compl)
  have hF : Measurable (Bad.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hBm
  have hzero : ∫⁻ ω, Bad.indicator (fun _ => (1 : ℝ≥0∞)) (ω t)
      ∂(ArapostathisAC.VanishingDiscount.pathMeasure M π i) = 0 := by
    have hsec : ∀ (x : ℕ) (ν : Measure A), ν (M.U x)ᶜ = 0 →
        ∫⁻ a, Bad.indicator (fun _ => (1 : ℝ≥0∞)) (x, a) ∂ν = 0 := by
      intro x ν hν
      have : (fun a => Bad.indicator (fun _ => (1 : ℝ≥0∞)) (x, a)) =
          (M.U x)ᶜ.indicator (fun _ => 1) := by
        funext a; by_cases h : a ∈ M.U x <;> simp [hBad, Set.indicator_apply, h]
      rw [this, lintegral_indicator_const (M.U_compact x).isClosed.measurableSet.compl, hν,
        mul_zero]
    cases t with
    | zero =>
      rw [lintegral_path_zero M π i hF]
      exact hsec i _ (π.adm 0 _)
    | succ t =>
      rw [lintegral_path_succ M π i t hF]
      have hin : ∀ ω : ℕ → ℕ × A, ∫⁻ z, Bad.indicator (fun _ => (1 : ℝ≥0∞)) z
          ∂(ArapostathisAC.VanishingDiscount.stepKernel M π t (Preorder.frestrictLe t ω)) = 0 := by
        intro ω
        rw [lintegral_step_general M π t _ hF]
        have : ∀ j, ∫⁻ a, Bad.indicator (fun _ => (1 : ℝ≥0∞)) (j, a)
            ∂(π.rule (t + 1) (ArapostathisAC.VanishingDiscount.histFin t
              (Preorder.frestrictLe t ω), j)) = 0 :=
          fun j => hsec j _ (π.adm (t + 1) _)
        simp only [this, lintegral_zero]
      simp only [hin, lintegral_zero]
  have hae := (lintegral_eq_zero_iff (hF.comp (measurable_pi_apply t))).1 hzero
  filter_upwards [hae] with ω hω
  by_contra hc
  have : Bad.indicator (fun _ => (1 : ℝ≥0∞)) (ω t) = 1 := Set.indicator_of_mem hc _
  simp only [Function.comp, Pi.zero_apply] at hω
  rw [this] at hω
  exact one_ne_zero hω

/-- The discounted cost as a power series of expected stage costs. -/
lemma discCost_eq (M : ArapostathisAC.VanishingDiscount.CMP A)
    (π : ArapostathisAC.VanishingDiscount.Policy M) (β : ℝ) (hβ : 0 ≤ β) (i : ℕ) :
    ArapostathisAC.VanishingDiscount.discCost M π β i =
      ∑' t, ENNReal.ofReal β ^ t * ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2)
        ∂(ArapostathisAC.VanishingDiscount.pathMeasure M π i) := by
  unfold ArapostathisAC.VanishingDiscount.discCost
  have hm2 : ∀ t, AEMeasurable
      (fun ω : ℕ → ℕ × A => ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2))
      (ArapostathisAC.VanishingDiscount.pathMeasure M π i) := fun t =>
    (measurable_const.mul (M.c_meas.comp (measurable_pi_apply t))).ennreal_ofReal.aemeasurable
  rw [lintegral_tsum hm2]
  congr 1; funext t
  have : ∀ ω : ℕ → ℕ × A, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) =
      ENNReal.ofReal β ^ t * ENNReal.ofReal (M.c (ω t).1 (ω t).2) := by
    intro ω
    rw [ENNReal.ofReal_mul (pow_nonneg hβ t), ENNReal.ofReal_pow hβ]
  simp_rw [this]
  have hmt : Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
    (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal
  rw [lintegral_const_mul _ hmt]

/-- Value iteration bounds every policy from below. -/
lemma vseq_le_discCost (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (hβ : 0 ≤ β)
    (π : ArapostathisAC.VanishingDiscount.Policy M) (i n : ℕ) :
    vseq M β n i ≤ ArapostathisAC.VanishingDiscount.discCost M π β i := by
  set μ := ArapostathisAC.VanishingDiscount.pathMeasure M π i with hμ
  set b' := ENNReal.ofReal β with hb'
  set E : ℕ → ℝ≥0∞ := fun t => ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2) ∂μ with hE
  have hmc : ∀ t, Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
    fun t => (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal
  have hclaim : ∀ m, m ≤ n → vseq M β n i ≤ (∑ t ∈ Finset.range m, b' ^ t * E t) +
      b' ^ m * ∫⁻ ω, vseq M β (n - m) (ω m).1 ∂μ := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, one_mul,
        Nat.sub_zero]
      rw [hμ, lintegral_path_zero M π i (F := fun p : ℕ × A => vseq M β n p.1)
        ((measurable_of_countable _).comp measurable_fst)]
      simp
    | succ m ih =>
      intro hm
      have ih := ih (Nat.le_of_succ_le hm)
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      have hk' : n - (m + 1) = k := by omega
      rw [hk] at ih
      rw [hk']
      refine ih.trans ?_
      rw [Finset.sum_range_succ, add_assoc]
      gcongr
      -- `v_{k+1}(X_m) ≤ w_k(X_m, A_m)` almost surely
      have hle : ∫⁻ ω, vseq M β (k + 1) (ω m).1 ∂μ ≤
          ∫⁻ ω, w M β (vseq M β k) (ω m).1 (ω m).2 ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_adm M π i m] with ω hω
        exact iInf₂_le _ hω
      have hw : ∫⁻ ω, w M β (vseq M β k) (ω m).1 (ω m).2 ∂μ =
          E m + b' * ∫⁻ ω, vseq M β k (ω (m + 1)).1 ∂μ := by
        have hstep : ∫⁻ ω, vseq M β k (ω (m + 1)).1 ∂μ =
            ∫⁻ ω, ∑' j, M.P (ω m) {j} * vseq M β k j ∂μ := by
          rw [hμ, lintegral_path_succ M π i m (F := fun p : ℕ × A => vseq M β k p.1)
            ((measurable_of_countable _).comp measurable_fst)]
          congr 1; funext ω
          rw [lintegral_step_general M π m _ (F := fun p : ℕ × A => vseq M β k p.1)
            ((measurable_of_countable _).comp measurable_fst)]
          simp only [lintegral_const, measure_univ, mul_one]
          rw [w_tsum_eq_lintegral]
          rfl
        rw [hstep]
        unfold w
        have hm1 : Measurable (fun ω : ℕ → ℕ × A =>
            ∑' j, M.P (ω m) {j} * vseq M β k j) := by
          have : (fun ω : ℕ → ℕ × A => ∑' j, M.P (ω m) {j} * vseq M β k j) =
              fun ω => ∫⁻ j, vseq M β k j ∂(M.P (ω m)) := by
            funext ω; exact w_tsum_eq_lintegral M _ _
          rw [this]
          exact ((measurable_of_countable _).lintegral_kernel).comp (measurable_pi_apply m)
        rw [lintegral_add_left (hmc m), lintegral_const_mul _ hm1]
      calc b' ^ m * ∫⁻ ω, vseq M β (k + 1) (ω m).1 ∂μ
          ≤ b' ^ m * (E m + b' * ∫⁻ ω, vseq M β k (ω (m + 1)).1 ∂μ) := by
            gcongr; exact hle.trans hw.le
        _ = b' ^ m * E m + b' ^ (m + 1) * ∫⁻ ω, vseq M β k (ω (m + 1)).1 ∂μ := by
            rw [mul_add, pow_succ, mul_assoc]
  have hn := hclaim n le_rfl
  simp only [Nat.sub_self, vseq, lintegral_zero, mul_zero, add_zero] at hn
  refine hn.trans ?_
  rw [discCost_eq M π β hβ i]
  exact ENNReal.sum_le_tsum _

end SennottDCOEAux

open SennottDCOEAux

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ i, ArapostathisAC.VanishingDiscount.discValue M β i =
      ⨅ a ∈ M.U i, (ENNReal.ofReal (M.c i a) +
        ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * ArapostathisAC.VanishingDiscount.discValue M β j)) ∧
    ∃ f : StationaryPolicy M, ArapostathisAC.VanishingDiscount.IsDiscOptimal M β f := by
  have hβ0 : 0 ≤ β := hβ.1.le
  set V : ℕ → ℝ≥0∞ := fun j => ⨆ k, vseq M β k j with hV
  have hfix := T_vinf M β
  -- a minimizing stationary policy
  choose a ha hmin using fun i => exists_min M β V i
  let f : StationaryPolicy M := ⟨a, ha⟩
  have hfeq : ∀ k, V k = ENNReal.ofReal (M.c k (f.1 k)) +
      ENNReal.ofReal β * ∫⁻ j, V j ∂(Q M f.1 k) := by
    intro k
    have h1 : V k = T M β V k := by rw [hfix]
    rw [h1, hmin k]
    unfold w
    rw [w_tsum_eq_lintegral]
    rfl
  -- the stationary policy has cost at most `V`
  have hfle : ∀ i, ArapostathisAC.VanishingDiscount.discCost M f.toPolicy β i ≤ V i := by
    intro i
    set b' := ENNReal.ofReal β
    set c' : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (M.c k (f.1 k)) with hc'
    have hC : ∀ t, ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2)
        ∂(ArapostathisAC.VanishingDiscount.pathMeasure M f.toPolicy i) =
        ∫⁻ j, c' j ∂(Qn M f.1 t i) := fun t =>
      lintegral_path M f i t (F := fun p : ℕ × A => ENNReal.ofReal (M.c p.1 p.2))
        M.c_meas.ennreal_ofReal
    have hpart : ∀ n, (∑ t ∈ Finset.range n, b' ^ t * ∫⁻ j, c' j ∂(Qn M f.1 t i)) +
        b' ^ n * ∫⁻ j, V j ∂(Qn M f.1 n i) ≤ V i := by
      intro n
      induction n with
      | zero => simp [Qn, Kernel.id_apply, lintegral_dirac]
      | succ n ih =>
        refine le_trans (le_of_eq ?_) ih
        have hstep : ∫⁻ j, V j ∂(Qn M f.1 n i) = ∫⁻ j, c' j ∂(Qn M f.1 n i) +
            b' * ∫⁻ j, V j ∂(Qn M f.1 (n + 1) i) := by
          have : ∫⁻ j, V j ∂(Qn M f.1 (n + 1) i) =
              ∫⁻ k, ∫⁻ j, V j ∂(Q M f.1 k) ∂(Qn M f.1 n i) := by
            show ∫⁻ j, V j ∂((Q M f.1 ∘ₖ Qn M f.1 n) i) = _
            rw [Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
          rw [this, ← lintegral_const_mul _ (measurable_of_countable _),
            ← lintegral_add_left (measurable_of_countable _)]
          congr 1; funext k; exact hfeq k
        rw [Finset.sum_range_succ, hstep, mul_add, pow_succ, mul_assoc]
        ring
    rw [discCost_eq M f.toPolicy β hβ0 i]
    simp_rw [hC]
    exact ENNReal.tsum_le_of_sum_range_le (fun n => le_trans le_self_add (hpart n))
  -- `V ≤ J*`
  have hVle : ∀ i, V i ≤ ArapostathisAC.VanishingDiscount.discValue M β i := fun i =>
    iSup_le (fun k => le_iInf (fun π => vseq_le_discCost M β hβ0 π i k))
  have hJ : ∀ i, ArapostathisAC.VanishingDiscount.discValue M β i = V i := fun i =>
    le_antisymm ((iInf_le _ f.toPolicy).trans (hfle i)) (hVle i)
  have hJfun : ArapostathisAC.VanishingDiscount.discValue M β = V := funext hJ
  refine ⟨fun i => ?_, f, fun i => ?_⟩
  · rw [hJfun]
    exact (congrFun hfix i).symm
  · exact le_antisymm ((hfle i).trans (hJ i).symm.le) (iInf_le _ _)
