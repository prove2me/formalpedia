-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.acoi_avgCost_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:37:59.793946+00:00
-- url     : https://prove2.me/submissions/40dd0f49-2962-43af-9bee-142c3e74f566

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

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hb : BddBelow (Set.range h))
    (f : StationaryPolicy M) (hsum : ∀ i, Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j))
    (hineq : ∀ i, M.c i (f.1 i) + ∑' j, ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j ≤ ρ + h i) (i : ℕ) :
    ArapostathisAC.VanishingDiscount.avgCost M f.toPolicy i ≤ ENNReal.ofReal ρ := by
  obtain ⟨b0, hb0⟩ := hb
  have hb0' : ∀ j, b0 ≤ h j := fun j => hb0 ⟨j, rfl⟩
  set b : ℝ := max (-b0) 0 with hbdef
  have hb_nn : 0 ≤ b := le_max_right _ _
  set g : ℕ → ℝ := fun j => h j + b with hgdef
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    simp only [hgdef]; linarith [hb0' j, le_max_left (-b0) 0]
  set c' : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (M.c k (f.1 k)) with hc'
  set G : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (g k) with hG
  set ρ' := ENNReal.ofReal ρ with hρ'
  -- the ACOI in `[0, ∞]`
  have hE : ∀ k, c' k + ∫⁻ j, G j ∂(Q M f.1 k) ≤ ρ' + G k := by
    intro k
    have hsg : HasSum (fun j => ArapostathisAC.VanishingDiscount.prob M k (f.1 k) j * g j)
        ((∑' j, ArapostathisAC.VanishingDiscount.prob M k (f.1 k) j * h j) + 1 * b) := by
      have := (hsum k).hasSum.add ((sennott_prob_hasSum M k (f.1 k)).mul_right b)
      refine this.congr_fun (fun j => ?_)
      simp only [hgdef]; ring
    rw [lintegral_Q]
    have h1 : ∑' j, G j * M.P (k, f.1 k) {j} =
        ENNReal.ofReal (∑' j, ArapostathisAC.VanishingDiscount.prob M k (f.1 k) j * g j) := by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (f := fun j => ArapostathisAC.VanishingDiscount.prob M k (f.1 k) j * g j)
        (fun j => mul_nonneg ENNReal.toReal_nonneg (hg0 j)) hsg.summable]
      congr 1; funext j
      simp only [hG, ArapostathisAC.VanishingDiscount.prob]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _),
        mul_comm]
    rw [h1, hsg.tsum_eq]
    have hc0 : 0 ≤ M.c k (f.1 k) := M.c_nonneg k (f.1 k) (f.2 k)
    have hS0 : 0 ≤ (∑' j, ArapostathisAC.VanishingDiscount.prob M k (f.1 k) j * h j) + 1 * b := by
      rw [← hsg.tsum_eq]; exact tsum_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (hg0 j))
    simp only [hc', hG, hρ']
    rw [← ENNReal.ofReal_add hc0 hS0]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
    have := hineq k
    simp only [hgdef]; linarith
  set C : ℕ → ℝ≥0∞ := fun t => ∫⁻ j, c' j ∂(Qn M f.1 t i) with hC
  set e : ℕ → ℝ≥0∞ := fun t => ∫⁻ j, G j ∂(Qn M f.1 t i) with he
  have hstep : ∀ t, C t + e (t + 1) ≤ ρ' + e t := by
    intro t
    have he1 : e (t + 1) = ∫⁻ k, ∫⁻ j, G j ∂(Q M f.1 k) ∂(Qn M f.1 t i) := by
      simp only [he]
      show ∫⁻ j, G j ∂((Q M f.1 ∘ₖ Qn M f.1 t) i) = _
      rw [Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
    rw [he1]
    simp only [hC, he]
    rw [← lintegral_add_left (measurable_of_countable _)]
    calc ∫⁻ k, (c' k + ∫⁻ j, G j ∂(Q M f.1 k)) ∂(Qn M f.1 t i)
        ≤ ∫⁻ k, (ρ' + G k) ∂(Qn M f.1 t i) := lintegral_mono (fun k => hE k)
      _ = ρ' + ∫⁻ k, G k ∂(Qn M f.1 t i) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have hsumN : ∀ N : ℕ, (∑ t ∈ Finset.range N, C t) + e N ≤ (N : ℝ≥0∞) * ρ' + G i := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_zero, zero_mul, he]
      simp [Qn, Kernel.id_apply, lintegral_dirac]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      calc (∑ t ∈ Finset.range N, C t) + C N + e (N + 1)
          = (∑ t ∈ Finset.range N, C t) + (C N + e (N + 1)) := by rw [add_assoc]
        _ ≤ (∑ t ∈ Finset.range N, C t) + (ρ' + e N) := add_le_add_right (hstep N) _
        _ = ((∑ t ∈ Finset.range N, C t) + e N) + ρ' := by ring
        _ ≤ ((N : ℝ≥0∞) * ρ' + G i) + ρ' := by gcongr
        _ = ((N + 1 : ℕ) : ℝ≥0∞) * ρ' + G i := by push_cast; ring
  have hcost : ∀ N, ArapostathisAC.VanishingDiscount.costN M f.toPolicy N i ≤
      (N : ℝ≥0∞) * ρ' + G i := by
    intro N
    have hm : ∀ t, Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
      fun t => (M.c_meas.comp (measurable_pi_apply t)).ennreal_ofReal
    have : ArapostathisAC.VanishingDiscount.costN M f.toPolicy N i = ∑ t ∈ Finset.range N, C t := by
      unfold ArapostathisAC.VanishingDiscount.costN
      rw [lintegral_finsetSum _ (fun t _ => hm t)]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      exact lintegral_path M f i t (F := fun p : ℕ × A => ENNReal.ofReal (M.c p.1 p.2))
        M.c_meas.ennreal_ofReal
    rw [this]
    exact le_trans le_self_add (hsumN N)
  unfold ArapostathisAC.VanishingDiscount.avgCost
  have hlim : Tendsto (fun N : ℕ => ρ' + (N : ℝ≥0∞)⁻¹ * G i) atTop (𝓝 ρ') := by
    have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.ofReal_ne_top (r := g i)))
    have := (tendsto_const_nhds (x := ρ')).add this
    simpa using this
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  calc (N : ℝ≥0∞)⁻¹ * ArapostathisAC.VanishingDiscount.costN M f.toPolicy N i
      ≤ (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * ρ' + G i) := by gcongr; exact hcost N
    _ = ρ' + (N : ℝ≥0∞)⁻¹ * G i := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : N ≠ 0))
          (ENNReal.natCast_ne_top N), one_mul]
