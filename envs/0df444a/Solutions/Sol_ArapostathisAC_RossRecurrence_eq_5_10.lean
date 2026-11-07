-- Prove2me | solution 1 for ArapostathisAC.RossRecurrence.eq_5_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:27:04.204132+00:00
-- url     : https://prove2.me/submissions/030d5893-b165-41c4-a8f9-34350339dcd6

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
import Theorems.Thm_ArapostathisAC_RossRecurrence_theorem_2_1_iii
import Theorems.Thm_ArapostathisAC_RossRecurrence_jensen_step
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ArapostathisAC.RossRecurrence

namespace Ross53Aux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

instance initMeasure_isProb {M : CMP A} (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (initMeasure π i) := by
  unfold initMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance pathMeasure_isProb (M : CMP A) (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (pathMeasure M π i) := by
  unfold pathMeasure; infer_instance

lemma measurableSet_bad (M : CMP A) : MeasurableSet {q : ℕ × A | q.2 ∉ M.U q.1} := by
  have : {q : ℕ × A | q.2 ∉ M.U q.1} = ⋃ j : ℕ, ({j} : Set ℕ) ×ˢ (M.U j)ᶜ := by
    ext ⟨j, a⟩; simp
  rw [this]
  exact MeasurableSet.iUnion fun j =>
    (measurableSet_singleton j).prod (M.U_compact j).isClosed.measurableSet.compl

lemma compProd_bad (M : CMP A) {X : Type*} [MeasurableSpace X] (κ : Kernel X ℕ) [IsSFiniteKernel κ]
    (η : Kernel (X × ℕ) A) [IsSFiniteKernel η] (hη : ∀ x j, η (x, j) (M.U j)ᶜ = 0) (x : X) :
    (κ ⊗ₖ η) x {q : ℕ × A | q.2 ∉ M.U q.1} = 0 := by
  rw [Kernel.compProd_apply (measurableSet_bad M)]
  have : ∀ j : ℕ, η (x, j) {a | a ∉ M.U j} = 0 := fun j => hη x j
  simp [this]

lemma stepKernel_bad (M : CMP A) (π : Policy M) (t : ℕ) (h : Π _ : Finset.Iic t, ℕ × A) :
    stepKernel M π t h {q : ℕ × A | q.2 ∉ M.U q.1} = 0 :=
  haveI h1 : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t)
      (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
  haveI h2 : IsMarkovKernel ((π.rule (t + 1)).comap
      (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  compProd_bad M _ _ (fun x j => by rw [Kernel.comap_apply]; exact π.adm (t + 1) _) h

lemma adm_ae (M : CMP A) (π : Policy M) (i : ℕ) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M π i), (ω t).2 ∈ M.U (ω t).1 := by
  rw [ae_iff]
  have hB := measurableSet_bad M
  cases t with
  | zero =>
    have hg : Measurable (fun y : Π _ : Finset.Iic 0, ℕ × A => y ⟨0, by simp⟩) :=
      measurable_pi_apply _
    have hk : (Kernel.traj (X := fun _ => ℕ × A) (stepKernel M π) 0).map (fun ω => ω 0) =
        Kernel.deterministic _ hg := by
      rw [← Kernel.id_map hg, ← Kernel.partialTraj_self (X := fun _ => ℕ × A) (κ := stepKernel M π),
        ← Kernel.traj_map_frestrictLe, ← Kernel.map_comp_right _ (by fun_prop) hg]
      rfl
    have hmap : (pathMeasure M π i).map (fun ω => ω 0) = initMeasure π i := by
      unfold pathMeasure Kernel.trajMeasure
      rw [Measure.map_comp _ _ (by fun_prop), hk, Measure.deterministic_comp_eq_map,
        Measure.map_map hg (by fun_prop)]
      convert Measure.map_id
      funext x; rfl
    have h0 : (pathMeasure M π i) {ω | ¬ (ω 0).2 ∈ M.U (ω 0).1} =
        ((pathMeasure M π i).map (fun ω => ω 0)) {q : ℕ × A | q.2 ∉ M.U q.1} := by
      rw [Measure.map_apply (by fun_prop) hB]; rfl
    rw [h0, hmap]
    unfold initMeasure
    rw [Measure.map_apply (by fun_prop) hB]
    exact π.adm 0 (fun j => j.elim0, i)

  | succ a =>
    have hlaw := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => ℕ × A) (μ₀ := initMeasure π i) (κ := stepKernel M π) (a := a)
    have := congrArg (fun μ => μ (Set.univ ×ˢ {q : ℕ × A | q.2 ∉ M.U q.1})) hlaw
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hB),
      Measure.compProd_apply_prod MeasurableSet.univ hB] at this
    simp only [stepKernel_bad, MeasureTheory.lintegral_zero] at this
    unfold pathMeasure
    rw [this]; congr 1; ext ω; simp

lemma M0_nonneg (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀) : 0 ≤ M₀ := by
  obtain ⟨a, ha⟩ := M.U_nonempty 0
  exact (M.c_nonneg 0 a ha).trans (hc 0 a ha)

/-- A stationary deterministic policy exists (choice from the nonempty `U i`). -/
noncomputable def someStat (M : CMP A) : StationaryPolicy M :=
  ⟨fun i => (M.U_nonempty i).some, fun i => (M.U_nonempty i).some_mem⟩

lemma discCost_le (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (π : Policy M) (i : ℕ) :
    discCost M π β i ≤ ENNReal.ofReal (M₀ / (1 - β)) := by
  have hM := M0_nonneg M M₀ hc
  have hae : ∀ᵐ ω ∂(pathMeasure M π i), ∀ t, (ω t).2 ∈ M.U (ω t).1 :=
    ae_all_iff.2 (adm_ae M π i)
  have hgeom : ∑' t : ℕ, ENNReal.ofReal (β ^ t * M₀) = ENNReal.ofReal (M₀ / (1 - β)) := by
    have hs : Summable (fun t : ℕ => β ^ t * M₀) :=
      (summable_geometric_of_lt_one hβ.1.le hβ.2).mul_right _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ.1.le t) hM) hs,
      tsum_mul_right, tsum_geometric_of_lt_one hβ.1.le hβ.2, div_eq_inv_mul]
  unfold discCost
  calc ∫⁻ ω, ∑' t, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) ∂(pathMeasure M π i)
      ≤ ∫⁻ _ω, ENNReal.ofReal (M₀ / (1 - β)) ∂(pathMeasure M π i) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with ω hω
        rw [← hgeom]
        exact ENNReal.tsum_le_tsum fun t => ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hc _ _ (hω t)) (pow_nonneg hβ.1.le t))
    _ = ENNReal.ofReal (M₀ / (1 - β)) := by simp

lemma discValue_le (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    discValue M β i ≤ ENNReal.ofReal (M₀ / (1 - β)) :=
  (iInf_le _ (someStat M).toPolicy).trans (discCost_le M M₀ hc β hβ _ i)

lemma one_le_returnTime (ω : ℕ → ℕ × A) : 1 ≤ returnTime ω := by
  unfold returnTime
  apply le_sInf
  rintro _ ⟨t, ht, rfl⟩
  show (1 : ℕ∞) ≤ (t : ℕ∞)
  exact_mod_cast ht.1

lemma one_le_meanReturnTime (M : CMP A) (f : StationaryPolicy M) (i : ℕ) :
    1 ≤ meanReturnTime M f i := by
  unfold meanReturnTime
  calc (1 : ℝ≥0∞) = ∫⁻ _ω, 1 ∂(pathMeasure M f.toPolicy i) := by simp
    _ ≤ _ := lintegral_mono fun ω => by
        have := one_le_returnTime ω
        rw [← ENat.toENNReal_one]; exact ENat.toENNReal_le.2 this

lemma one_lt_K (M : CMP A) (K : ℝ)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K) : 1 < K := by
  have h := (one_le_meanReturnTime M (someStat M) 0).trans_lt (h57 (someStat M) 0)
  rw [← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).1 h

lemma discAtReturn_le (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (ω : ℕ → ℕ × A) :
    discAtReturn β ω ≤ ENNReal.ofReal β := by
  unfold discAtReturn
  split_ifs with h
  · exact zero_le
  · apply ENNReal.ofReal_le_ofReal
    have h1 := one_le_returnTime ω
    have hn : 1 ≤ (returnTime ω).toNat := by
      lift returnTime ω to ℕ using h with n
      simpa using h1
    calc β ^ (returnTime ω).toNat ≤ β ^ 1 := pow_le_pow_of_le_one hβ.1.le hβ.2.le hn
      _ = β := pow_one β

lemma expDiscAtReturn_le (M : CMP A) (f : StationaryPolicy M) (β : ℝ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    expDiscAtReturn M f β i ≤ ENNReal.ofReal β := by
  unfold expDiscAtReturn
  calc ∫⁻ ω, discAtReturn β ω ∂(pathMeasure M f.toPolicy i)
      ≤ ∫⁻ _ω, ENNReal.ofReal β ∂(pathMeasure M f.toPolicy i) :=
        lintegral_mono fun ω => discAtReturn_le β hβ ω
    _ = ENNReal.ofReal β := by simp

/-- Bernoulli: `1 - β^K ≤ K (1 - β)` for `K ≥ 1`, `β ∈ (0,1)`. -/
lemma one_sub_rpow_le (β K : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hK : 1 ≤ K) :
    1 - β ^ K ≤ K * (1 - β) := by
  have := one_add_mul_self_le_rpow_one_add (s := β - 1) (by linarith [hβ.1]) hK
  have e : (1 : ℝ) + (β - 1) = β := by ring
  rw [e] at this
  nlinarith

end Ross53Aux

open Ross53Aux in
theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    (discValue M β 0).toReal - (discValue M β i).toReal ≤ (1 - β ^ K) * (discValue M β 0).toReal ∧
      (1 - β ^ K) * (discValue M β 0).toReal ≤ (1 - β ^ K) * (M₀ / (1 - β)) ∧
      (1 - β ^ K) * (M₀ / (1 - β)) ≤ M₀ * K := by
  obtain ⟨f, hf⟩ := theorem_2_1_iii M β hβ
  obtain ⟨hj1, hj2⟩ := jensen_step M M₀ hc K hK h57 β hβ f hf i
  have hM := M0_nonneg M M₀ hc
  have hK1 := one_lt_K M K h57
  have hb : 0 < 1 - β := by linarith [hβ.2]
  have hbK0 : 0 ≤ β ^ K := Real.rpow_nonneg hβ.1.le K
  have hbK1 : β ^ K ≤ 1 := Real.rpow_le_one hβ.1.le hβ.2.le hK.le
  have hifin : discValue M β i ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (discValue_le M M₀ hc β hβ i)
  have hle := ENNReal.toReal_mono hifin (hj2.trans hj1)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hbK0] at hle
  have h0le : (discValue M β 0).toReal ≤ M₀ / (1 - β) :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg hM hb.le) (discValue_le M M₀ hc β hβ 0)
  refine ⟨by nlinarith, mul_le_mul_of_nonneg_left h0le (by linarith), ?_⟩
  have hB := one_sub_rpow_le β K hβ hK1.le
  rw [mul_div_assoc', div_le_iff₀ hb]
  nlinarith
