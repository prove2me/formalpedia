-- Prove2me | solution 1 for AdaptiveStepIPM.Probabilistic.theorem_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:56:44.83337+00:00
-- url     : https://prove2.me/submissions/fcb29b97-5a10-4a90-a97a-2bdf0a6afc3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AdaptiveStepIPM_Probabilistic_lemma_6
import Theorems.Thm_AdaptiveStepIPM_Probabilistic_lemma_7
import Theorems.Thm_AdaptiveStepIPM_Probabilistic_equations_18_19

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

lemma pi_gauss_ac (n : ℕ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1) ≪
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
    have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => gaussianReal 0 1)
      (Fin.last k)).symm
    have h2 := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => (volume : Measure ℝ))
      (Fin.last k)).symm
    rw [← h1.map_eq, ← h2.map_eq]
    exact ((gaussianReal_absolutelyContinuous 0 one_ne_zero).prod ih).map
      (MeasurableEquiv.measurable _)

lemma gauss_submodule_null (n : ℕ) (S : Submodule ℝ (Fin n → ℝ)) (hS : S ≠ ⊤) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1) (S : Set (Fin n → ℝ)) = 0 := by
  apply pi_gauss_ac n
  rw [← volume_pi]
  exact Measure.addHaar_submodule _ S hS

lemma ae_linIndep (n : ℕ) : ∀ m, m ≤ n →
    ∀ᵐ G ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => gaussianReal 0 1),
      LinearIndependent ℝ G := by
  intro m
  induction m with
  | zero => intro _; exact Filter.Eventually.of_forall fun G => linearIndependent_empty_type
  | succ k ih =>
    intro hk
    set μ := Measure.pi fun _ : Fin n => gaussianReal 0 1
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) (Fin.last k)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => (Fin n → ℝ)) (Fin.last k)
    have hopen : IsOpen {G : Fin (k+1) → Fin n → ℝ | LinearIndependent ℝ G} :=
      isOpen_setOfPred_linearIndependent
    have key : ∀ᵐ y ∂(μ.prod (Measure.pi fun _ : Fin k => μ)),
        LinearIndependent ℝ (e.symm y) := by
      have hmeas : MeasurableSet {y : (Fin n → ℝ) × (Fin k → Fin n → ℝ) |
          LinearIndependent ℝ (e.symm (y.1, y.2))} := by
        have := hopen.measurableSet.preimage e.symm.measurable
        simpa using this
      rw [Measure.ae_prod_iff_ae_ae hmeas, Measure.ae_ae_comm hmeas]
      filter_upwards [ih (by omega)] with v hv
      have hne : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
        intro htop
        have h1 := finrank_range_le_card (R := ℝ) v
        rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
        omega
      have h0 := gauss_submodule_null n _ hne
      rw [measure_eq_zero_iff_ae_notMem] at h0
      filter_upwards [h0] with x hx
      have : e.symm (x, v) = Fin.snoc v x := by
        simp [e, MeasurableEquiv.piFinSuccAbove]
        rfl
      rw [this, linearIndependent_finSnoc]
      exact ⟨hv, hx⟩
    have := hmp.quasiMeasurePreserving.ae key
    simpa using this


lemma ker_bot_of_linIndep {n : ℕ} (G : Fin n → Fin n → ℝ) (hG : LinearIndependent ℝ G) :
    kernel n n G = ⊥ := by
  have hu : @IsUnit (Matrix (Fin n) (Fin n) ℝ) _ G := Matrix.linearIndependent_rows_iff_isUnit.mp hG
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  unfold kernel
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h1 : Matrix.mulVec (G : Matrix (Fin n) (Fin n) ℝ) x.ofLp = 0 := by
    have := congrArg WithLp.ofLp hx
    exact this
  have h2 : x.ofLp = 0 := hinj (by rw [h1]; exact (Matrix.mulVec_zero (A := (G : Matrix (Fin n) (Fin n) ℝ))).symm)
  ext i
  simpa using congrFun h2 i

/-- A frame with prescribed unit first column. -/
noncomputable def mkFrame {n : ℕ} (hn : 1 ≤ n) (g : EuclideanSpace ℝ (Fin n)) (hg : ‖g‖ = 1) :
    Frame n :=
  have hfin : Module.finrank ℝ (ℝ ∙ g)ᗮ = n - 1 := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) :=
      ⟨by simp; omega⟩
    exact Submodule.finrank_orthogonal_span_singleton (by rintro rfl; simp at hg)
  let b : OrthonormalBasis (Fin (n - 1)) ℝ (ℝ ∙ g)ᗮ :=
    (stdOrthonormalBasis ℝ (ℝ ∙ g)ᗮ).reindex (finCongr hfin)
  { g := g
    H := (ℝ ∙ g)ᗮ.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    coordinates := b.repr.toLinearEquiv.toLinearMap ∘ₗ
      (ℝ ∙ g)ᗮ.orthogonalProjectionOnto.toLinearMap
    g_unit := hg
    g_orthogonal := by
      intro v
      have := (b.repr.symm v).2
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      simpa using this
    coordinates_H := by
      intro v
      simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    decomposition := by
      intro x
      have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := ℝ ∙ g) x
      rw [Submodule.starProjection_unit_singleton ℝ hg, real_inner_comm] at h1
      conv_lhs => rw [← h1]
      congr 1
      change _ = (((b.repr.symm (b.repr ((ℝ ∙ g)ᗮ.orthogonalProjectionOnto x)) : (ℝ ∙ g)ᗮ)) :
        EuclideanSpace ℝ (Fin n))
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl }

lemma prob_le_one' {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

instance (k : ℕ) : IsProbabilityMeasure (sphereGaussian k) := by
  unfold sphereGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance (m n : ℕ) : IsProbabilityMeasure (gaussianMatrix m n) := by
  unfold gaussianMatrix
  infer_instance

lemma one_le_of_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) (h : ∀ᵐ x ∂μ, x ∈ s) : 1 ≤ (μ s).toReal := by
  have : μ Set.univ ≤ μ s := measure_mono_ae (h.mono fun x hx _ => hx)
  rw [measure_univ] at this
  have hs : μ s = 1 := le_antisymm prob_le_one this
  simp [hs]

lemma negSupNorm_le {n : ℕ} (z : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ j, -B ≤ z j) :
    negSupNorm z ≤ B := by
  unfold negSupNorm
  refine (pi_norm_le_iff_of_nonneg hB).2 fun j => ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_min (h j) (neg_nonpos.mpr hB)
  · exact (min_le_right _ _).trans hB

lemma key (n m d : ℕ) (hdm : d + m = n) (hn : 2 ≤ n) (r : EuclideanSpace ℝ (Fin n))
    (F : Frame n) (hF : r ≠ 0 → F.g = ‖r‖⁻¹ • r) :
    ((sphereGaussian (n - 1)) {v | supNorm (F.H v) ≤
        Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ))}).toReal ≤
      ((gaussianMatrix m n) {G | negSupNorm (pq m n G r) ≤
        Real.log (n : ℝ) / (n : ℝ) * ‖r‖ ^ 2}).toReal := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hB : 0 ≤ Real.log (n : ℝ) / (n : ℝ) * ‖r‖ ^ 2 := by positivity
  have hzero : ∀ G : Fin m → Fin n → ℝ, pq m n G r = 0 → negSupNorm (pq m n G r) ≤
      Real.log (n : ℝ) / (n : ℝ) * ‖r‖ ^ 2 := by
    intro G hG
    rw [hG]
    exact negSupNorm_le _ _ hB (fun j => by simp; linarith)
  have triv : (∀ᵐ G : Fin m → Fin n → ℝ ∂ gaussianMatrix m n, pq m n G r = 0) →
      ((sphereGaussian (n - 1)) {v | supNorm (F.H v) ≤
        Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ))}).toReal ≤
      ((gaussianMatrix m n) {G | negSupNorm (pq m n G r) ≤
        Real.log (n : ℝ) / (n : ℝ) * ‖r‖ ^ 2}).toReal := fun h =>
    (prob_le_one' _ _).trans (one_le_of_ae _ _ (h.mono fun G hG => hzero G hG))
  by_cases hr : r = 0
  · apply triv
    refine Filter.Eventually.of_forall fun G => ?_
    funext j
    simp [pq, p, q, hr]
  by_cases hm : m = 0
  · subst hm
    apply triv
    refine Filter.Eventually.of_forall fun G => ?_
    have hmem : r ∈ kernel 0 n G := by
      unfold kernel
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    have hp : p 0 n G r = r := (Submodule.starProjection_eq_self_iff).2 hmem
    funext j
    simp [pq, q, hp]
  by_cases hd : d = 0
  · subst hd
    simp only [zero_add] at hdm
    subst hdm
    apply triv
    filter_upwards [ae_linIndep m m le_rfl] with G hG
    have hk := ker_bot_of_linIndep G hG
    have hp : p m m G r = 0 := by
      have hmem : p m m G r ∈ kernel m m G := Submodule.starProjection_apply_mem (kernel m m G) r
      rw [hk, Submodule.mem_bot] at hmem
      exact hmem
    funext j
    simp [pq, hp]
  -- main case
  have hd1 : 1 ≤ d := by omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨_, h2, _, h4, h5⟩ := lemma_6 hn hd1 hm1 hdm F
  have hg := hF hr
  have hrpos : 0 < ‖r‖ := norm_pos_iff.mpr hr
  set s := Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ)) with hs
  have hs2 : s ^ 2 = 3 * Real.log (n : ℝ) / (n : ℝ) := Real.sq_sqrt (by positivity)
  have hmeasB : MeasurableSet {x : EuclideanSpace ℝ (Fin (n - 1)) | supNorm (F.H x) ≤ s} := by
    apply measurableSet_le _ measurable_const
    unfold supNorm
    exact (continuous_norm.comp ((EuclideanSpace.equiv (Fin n) ℝ).continuous.comp
      F.H.continuous)).measurable
  have heq : (sphereGaussian (n - 1)) {x | supNorm (F.H x) ≤ s} =
      gaussianMatrix m n {G | supNorm (F.H (v F G)) ≤ s} := by
    rw [← h4, Measure.map_apply_of_aemeasurable h2 hmeasB]
    rfl
  rw [heq]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h5] with G hG hGs
  obtain ⟨hdec, -, -⟩ := hG
  set g := F.g with hgdef
  set ζ := zeta F G with hζdef
  set w := F.H (v F G) with hw
  set c : ℝ := ‖r‖ / 2 with hc
  have h2g : (2 • g) = (2:ℝ) • g := by rw [two_smul ℕ, two_smul ℝ]
  have hr2 : r = c • (2 • g) := by
    rw [h2g, smul_smul, hg, smul_smul]
    have : c * 2 * ‖r‖⁻¹ = 1 := by rw [hc]; field_simp
    rw [this, one_smul]
  have hpr : p m n G r = c • p m n G (2 • g) := by
    conv_lhs => rw [hr2]
    exact map_smul (kernel m n G).starProjection c (2 • g)
  -- ζ^2 ≤ 1
  have hζ : ζ ^ 2 ≤ 1 := by
    set P := (kernel m n G).starProjection
    have hP2 : p m n G (2 • g) = (2:ℝ) • P g := by
      rw [h2g]; exact map_smul P (2:ℝ) g
    have ht : inner ℝ (P g) g = ‖P g‖ ^ 2 := by
      have h0 := Submodule.starProjection_inner_eq_zero (K := kernel m n G) g (P g)
        (Submodule.starProjection_apply_mem _ _)
      rw [inner_sub_left] at h0
      have hc' := real_inner_comm g (P g)
      rw [← real_inner_self_eq_norm_sq]
      linarith
    have hle : ‖P g‖ ≤ 1 := by
      have := Submodule.norm_starProjection_apply_le (K := kernel m n G) g
      rw [F.g_unit] at this
      exact this
    have hz : ζ = 2 * ‖P g‖ ^ 2 - 1 := by
      rw [hζdef]
      unfold zeta
      rw [hP2, inner_smul_left, ht]
      simp
    rw [hz]
    have h0 : 0 ≤ ‖P g‖ := norm_nonneg _
    have hx1 : ‖P g‖ ^ 2 ≤ 1 := pow_le_one₀ h0 hle
    nlinarith [mul_nonneg (sq_nonneg ‖P g‖) (sub_nonneg.2 hx1)]
  have H := equations_18_19 g w ζ hζ
  simp only at H
  obtain ⟨hall, -⟩ := H
  have hsw : supNorm w ^ 2 ≤ s ^ 2 := by
    have h0 : 0 ≤ supNorm w := norm_nonneg _
    have hGs' : supNorm w ≤ s := hGs
    exact pow_le_pow_left₀ h0 hGs' 2
  apply negSupNorm_le _ _ hB
  intro j
  have hj := (hall j).2.2
  have hpj : p m n G (2 • g) j = (1 + ζ) * g j + Real.sqrt (1 - ζ ^ 2) * w j := by
    rw [hdec]; simp [hw]; left; rfl
  have hrj : r j = c * (2 * g j) := by
    conv_lhs => rw [hr2]
    rw [h2g]; simp
  have hpq : pq m n G r j = c ^ 2 * (((1 + ζ) * g j + Real.sqrt (1 - ζ ^ 2) * w j) *
      ((1 - ζ) * g j - Real.sqrt (1 - ζ ^ 2) * w j)) := by
    simp only [pq, q]
    rw [PiLp.sub_apply, hpr, PiLp.smul_apply, smul_eq_mul, hpj, hrj]
    ring
  rw [hpq]
  have hc2 : c ^ 2 = ‖r‖ ^ 2 / 4 := by rw [hc]; ring
  have hfin : c ^ 2 * supNorm w ^ 2 ≤ Real.log (n : ℝ) / (n : ℝ) * ‖r‖ ^ 2 := by
    rw [hc2]
    calc ‖r‖ ^ 2 / 4 * supNorm w ^ 2 ≤ ‖r‖ ^ 2 / 4 * s ^ 2 := by gcongr
      _ = 3 / 4 * (Real.log (n : ℝ) / (n : ℝ) * ‖r‖ ^ 2) := by rw [hs2]; ring
      _ ≤ _ := by nlinarith
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hj hc0]

end AdaptiveStepIPM.Probabilistic

open AdaptiveStepIPM.Probabilistic in
theorem solution (d : ℕ → ℕ) (hd : ∀ n, d n ≤ n)
    (r : (n : ℕ) → EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun n : ℕ =>
      ((gaussianMatrix (n - d n) n)
        {G | negSupNorm (pq (n - d n) n G (r n)) ≤
          Real.log (n : ℝ) / (n : ℝ) * ‖r n‖ ^ 2}).toReal)
      atTop (nhds 1) := by
  classical
  let gv : ∀ n, 2 ≤ n → EuclideanSpace ℝ (Fin n) := fun n hn =>
    if r n = 0 then EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) else ‖r n‖⁻¹ • r n
  have hunit : ∀ n (hn : 2 ≤ n), ‖gv n hn‖ = 1 := by
    intro n hn
    by_cases h : r n = 0
    · simp [gv, h]
    · simp only [gv, h, if_false]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
  let F : ∀ n, 2 ≤ n → Frame n := fun n hn => mkFrame (by omega) (gv n hn) (hunit n hn)
  have h7 := lemma_7 F
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h7 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    rw [dif_pos hn]
    refine key n (n - d n) (d n) (by have := hd n; omega) hn (r n) (F n hn) ?_
    intro hr
    show gv n hn = _
    simp [gv, hr]
  · exact Eventually.of_forall fun n => prob_le_one' _ _
