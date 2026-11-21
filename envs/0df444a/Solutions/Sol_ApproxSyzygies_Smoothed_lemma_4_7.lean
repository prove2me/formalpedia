-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:24:57.32708+00:00
-- url     : https://prove2.me/submissions/e13037b7-d8ed-4fbd-bd67-4099ba5cac08

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_9

section
open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.L47

open ApproxSyzygies.Smoothed

section Spectral

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]

lemma spectral (M : W →ₗ[ℝ] V) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℝ W)) ℝ W) (e : Fin (finrank ℝ W) → ℝ)
      (I : Finset (Fin (finrank ℝ W))),
      I.card = numSmallSV M lam ∧
      (∀ w, ‖M w‖ ^ 2 = ∑ i, e i * (b.repr w i) ^ 2) ∧
      (∀ i ∈ I, e i ≤ lam ^ 2) ∧ (∀ i, i ∉ I → lam ^ 2 < e i) ∧ (∀ i, 0 ≤ e i) := by
  classical
  set n := finrank ℝ W with hn
  have hT := M.isSymmetric_adjoint_comp_self
  set b := hT.eigenvectorBasis rfl with hb
  set e := hT.eigenvalues (n := n) rfl with he
  set I : Finset (Fin n) := Finset.univ.filter fun i : Fin n => M.singularValues i ≤ lam with hI
  have hcard : numSmallSV M lam = I.card := by
    unfold numSmallSV
    refine (Finset.card_bij (fun k hk => (⟨k, Finset.mem_range.1 (Finset.mem_filter.1 hk).1⟩ : Fin n))
      ?_ ?_ ?_).trans rfl
    · intro k hk; simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]; exact (Finset.mem_filter.1 hk).2
    · intro a _ b _ h; simpa using h
    · intro j hj
      refine ⟨j.val, ?_, by simp⟩
      simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [Finset.mem_range, hj]
  have hsq : ∀ i : Fin n, M.singularValues i ^ 2 = e i := fun i => M.sq_singularValues_fin rfl i
  have hnn : ∀ i : Fin n, 0 ≤ M.singularValues i := fun i => M.singularValues_nonneg i
  refine ⟨b, e, I, hcard.symm, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_left, ← b.sum_inner_mul_inner _ w]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : inner ℝ ((LinearMap.adjoint M) (M w)) (b i : W) = e i * inner ℝ (b i : W) w := by
      have h2 := hT w (b i)
      have h3 : (LinearMap.adjoint M ∘ₗ M) (b i : W) = e i • (b i : W) := by
        have := hT.apply_eigenvectorBasis (n := n) rfl i
        simpa [hb, he] using this
      rw [LinearMap.comp_apply] at h2
      rw [h2, h3, real_inner_smul_right, real_inner_comm]
    rw [h1, OrthonormalBasis.repr_apply_apply]; ring
  · intro i hi
    have hs : M.singularValues i ≤ lam := (Finset.mem_filter.1 hi).2
    rw [← hsq i]; exact pow_le_pow_left₀ (hnn i) hs 2
  · intro i hi
    have hs : ¬ M.singularValues i ≤ lam := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [← hsq i]; exact pow_lt_pow_left₀ (not_le.1 hs) hlam (by norm_num)
  · intro i; rw [← hsq i]; positivity

lemma norm_sq_repr {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ W) (w : W) :
    ‖w‖ ^ 2 = ∑ i, (b.repr w) i ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
  simp

lemma large_subspace (M : W →ₗ[ℝ] V) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ S : Submodule ℝ W, finrank ℝ S ≤ numSmallSV M lam ∧
      ∀ w : W, ∃ s ∈ S, lam * ‖w - s‖ ≤ ‖M w‖ := by
  classical
  obtain ⟨b, e, I, hI, hM, hle, hlt, hnn⟩ := spectral M lam hlam
  refine ⟨Submodule.span ℝ (Set.range fun j : I => (b j : W)), ?_, ?_⟩
  · calc _ ≤ Fintype.card I := finrank_range_le_card _
      _ = _ := by rw [Fintype.card_coe, hI]
  · intro w
    let x : EuclideanSpace ℝ (Fin (finrank ℝ W)) :=
      WithLp.toLp 2 (fun i => if i ∈ I then b.repr w i else 0)
    refine ⟨b.repr.symm x, ?_, ?_⟩
    · rw [← b.sum_repr_symm]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : i ∈ I
      · simp only [x, hi, if_true]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · simp [x, hi]
    · have hr : ∀ i, b.repr (w - b.repr.symm x) i = if i ∈ I then 0 else b.repr w i := by
        intro i
        by_cases hi : i ∈ I <;> simp [x, hi]
      have h1 : ‖w - b.repr.symm x‖ ^ 2 = ∑ i, (if i ∈ I then (0:ℝ) else b.repr w i) ^ 2 := by
        rw [norm_sq_repr b]; exact Finset.sum_congr rfl fun i _ => by rw [hr]
      have h2 : (lam * ‖w - b.repr.symm x‖) ^ 2 ≤ ‖M w‖ ^ 2 := by
        rw [mul_pow, h1, hM, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i ∈ I
        · simp only [hi, if_true]; nlinarith [hnn i, sq_nonneg (b.repr w i)]
        · simp only [hi, if_false]
          nlinarith [hlt i hi, sq_nonneg (b.repr w i)]
      exact le_of_sq_le_sq h2 (norm_nonneg _)

lemma small_subspace (M : W →ₗ[ℝ] V) (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ)
    (hq : q ≤ numSmallSV M lam) :
    ∃ U : Submodule ℝ W, q ≤ finrank ℝ U ∧ ∀ w ∈ U, ‖M w‖ ≤ lam * ‖w‖ := by
  classical
  obtain ⟨b, e, I, hI, hM, hle, hlt, hnn⟩ := spectral M lam hlam
  refine ⟨Submodule.span ℝ (Set.range fun j : I => (b j : W)), ?_, ?_⟩
  · have hli : LinearIndependent ℝ (fun j : I => (b j : W)) :=
      b.orthonormal.linearIndependent.comp (fun j : I => (j : Fin (finrank ℝ W))) Subtype.val_injective
    rw [finrank_span_eq_card hli]
    simp [hI, hq]
  · intro w hw
    have hzero : ∀ i, i ∉ I → b.repr w i = 0 := by
      intro i hi
      have : Submodule.span ℝ (Set.range fun j : I => (b j : W)) ≤ LinearMap.ker (innerₛₗ ℝ (b i : W)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have hij : (j : Fin (finrank ℝ W)) ≠ i := fun h => hi (h ▸ j.2)
        simpa using b.orthonormal.inner_eq_zero hij.symm
      have := this hw
      simpa [OrthonormalBasis.repr_apply_apply] using this
    have hle2 : ‖M w‖ ^ 2 ≤ (lam * ‖w‖) ^ 2 := by
      rw [hM, mul_pow, norm_sq_repr b, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i ∈ I
      · nlinarith [hle i hi, sq_nonneg (b.repr w i)]
      · rw [hzero i hi]; simp
    exact le_of_sq_le_sq hle2 (by positivity)

lemma numSmallSV_ge (M : W →ₗ[ℝ] V) (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ)
    (U : Submodule ℝ W) (hU : q ≤ finrank ℝ U) (hM : ∀ w ∈ U, ‖M w‖ ≤ lam * ‖w‖) :
    q ≤ numSmallSV M lam := by
  classical
  obtain ⟨b, e, I, hI, hMe, hle, hlt, hnn⟩ := spectral M lam hlam
  by_contra hcon
  rw [not_le, ← hI] at hcon
  set L := (Submodule.span ℝ (Set.range fun j : I => (b j : W)))ᗮ with hL
  have hspan : finrank ℝ (Submodule.span ℝ (Set.range fun j : I => (b j : W))) ≤ I.card := by
    calc _ ≤ Fintype.card I := finrank_range_le_card _
      _ = _ := by rw [Fintype.card_coe]
  have hLd : finrank ℝ (Submodule.span ℝ (Set.range fun j : I => (b j : W))) + finrank ℝ L
      = finrank ℝ W := Submodule.finrank_add_finrank_orthogonal _
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U L
  have h2 : finrank ℝ ↥(U ⊔ L) ≤ finrank ℝ W := Submodule.finrank_le _
  have hn : finrank ℝ W = finrank ℝ W := rfl
  have hpos : 0 < finrank ℝ ↥(U ⊓ L) := by omega
  obtain ⟨w, hwm, hw0⟩ : ∃ w ∈ U ⊓ L, w ≠ 0 := by
    by_contra hh
    push Not at hh
    have : U ⊓ L = ⊥ := (Submodule.eq_bot_iff _).2 hh
    rw [this] at hpos; simp at hpos
  have hwU := hwm.1
  have hwL := hwm.2
  have hzero : ∀ i ∈ I, b.repr w i = 0 := by
    intro i hi
    rw [OrthonormalBasis.repr_apply_apply]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (⟨⟨i, hi⟩, rfl⟩ : (b i : W) ∈ Set.range fun j : I => (b j : W))) hwL
  have hwpos : 0 < ‖w‖ ^ 2 := by positivity
  have hle2 := pow_le_pow_left₀ (norm_nonneg _) (hM w hwU) 2
  rw [hMe, mul_pow, norm_sq_repr b, Finset.mul_sum] at hle2
  rw [norm_sq_repr b] at hwpos
  have hex : ∃ i, b.repr w i ≠ 0 := by
    by_contra hh; push Not at hh; simp [hh] at hwpos
  obtain ⟨i0, hi0⟩ := hex
  have hi0I : i0 ∉ I := fun h => hi0 (hzero i0 h)
  have : ∑ i, lam ^ 2 * (b.repr w i) ^ 2 < ∑ i, e i * (b.repr w i) ^ 2 := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · by_cases hi : i ∈ I
      · rw [hzero i hi]; simp
      · nlinarith [hlt i hi, sq_nonneg (b.repr w i)]
    · have := hlt i0 hi0I
      have hp : 0 < (b.repr w i0) ^ 2 := by positivity
      nlinarith
  linarith

end Spectral


section Tens

variable {ι κ : Type} [Fintype ι] [Fintype κ]

lemma norm_tens (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) :
    ‖tens u w‖ = ‖u‖ * ‖w‖ := by
  have h : ‖tens u w‖ ^ 2 = (‖u‖ * ‖w‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [tens, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- The map `M_u` of Lemma 4.9 for the subspace `X`. -/
noncomputable def Mop (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (u : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) :=
  (Xᗮ.starProjection : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).toLinearMap ∘ₗ
    tensLeft u

lemma Mop_apply (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (u : EuclideanSpace ℝ ι)
    (w : EuclideanSpace ℝ κ) : Mop X u w = Xᗮ.starProjection (tens u w) := rfl

lemma norm_Mop_le (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (u : EuclideanSpace ℝ ι)
    (w : EuclideanSpace ℝ κ) : ‖Mop X u w‖ ≤ ‖u‖ * ‖w‖ := by
  rw [Mop_apply, ← norm_tens]
  exact Submodule.norm_starProjection_apply_le Xᗮ _

/-- countable-infimum expression of the distance to the span of `y`. -/
noncomputable def Phi {r : ℕ} (z : EuclideanSpace ℝ (ι × κ)) (y : Fin r → EuclideanSpace ℝ (ι × κ)) :
    ℝ := ⨅ a : Fin r → ℚ, ‖z - ∑ j, (a j : ℝ) • y j‖

lemma proj_le_sub (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (z x : EuclideanSpace ℝ (ι × κ))
    (hx : x ∈ X) : ‖Xᗮ.starProjection z‖ ≤ ‖z - x‖ := by
  have h : Xᗮ.starProjection (z - x) = Xᗮ.starProjection z := by
    rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hx, sub_zero]
  rw [← h]; exact Submodule.norm_starProjection_apply_le Xᗮ _

lemma Phi_eq {r : ℕ} (z : EuclideanSpace ℝ (ι × κ)) (y : Fin r → EuclideanSpace ℝ (ι × κ)) :
    Phi z y = ‖(Submodule.span ℝ (Set.range y))ᗮ.starProjection z‖ := by
  set X := Submodule.span ℝ (Set.range y) with hX
  have hbdd : BddBelow (Set.range fun a : Fin r → ℚ => ‖z - ∑ j, (a j : ℝ) • y j‖) :=
    ⟨0, by rintro _ ⟨a, rfl⟩; exact norm_nonneg _⟩
  have hmem : ∀ c : Fin r → ℝ, ∑ j, c j • y j ∈ X := fun c =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    set x0 := X.starProjection z with hx0
    have hx0m : x0 ∈ X := Submodule.starProjection_apply_mem X z
    have hz : z - x0 = Xᗮ.starProjection z := by
      rw [hx0]; exact (Submodule.starProjection_orthogonal_val z).symm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx0m
    set B := 1 + ∑ j, ‖y j‖ with hB
    have hBpos : 0 < B := by
      have : 0 ≤ ∑ j, ‖y j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
    have hrat : ∀ j, ∃ q : ℚ, |(q : ℝ) - c j| < ε / B := by
      intro j
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c j < c j + ε / B by
        have : 0 < ε / B := by positivity
        linarith)
      refine ⟨q, ?_⟩
      rw [abs_lt]; constructor <;> linarith
    choose a ha using hrat
    have h1 : ‖∑ j, (a j : ℝ) • y j - x0‖ ≤ ε := by
      rw [← hc, ← Finset.sum_sub_distrib]
      calc ‖∑ j, ((a j : ℝ) • y j - c j • y j)‖ ≤ ∑ j, ‖(a j : ℝ) • y j - c j • y j‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j, (ε / B) * ‖y j‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [← sub_smul, norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (ha j).le (norm_nonneg _)
        _ = (ε / B) * ∑ j, ‖y j‖ := by rw [Finset.mul_sum]
        _ ≤ (ε / B) * B := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hB]; linarith
        _ = ε := by field_simp
    calc Phi z y ≤ ‖z - ∑ j, (a j : ℝ) • y j‖ := ciInf_le hbdd a
      _ = ‖(z - x0) + (x0 - ∑ j, (a j : ℝ) • y j)‖ := by congr 1; abel
      _ ≤ ‖z - x0‖ + ‖x0 - ∑ j, (a j : ℝ) • y j‖ := norm_add_le _ _
      _ ≤ ‖Xᗮ.starProjection z‖ + ε := by
          rw [hz, norm_sub_rev]; gcongr
  · exact le_ciInf fun a => proj_le_sub X z _ (hmem _)

end Tens


section BadSet

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- `u ↦ u ⊗ w` as a linear map. -/
noncomputable def tensRight (w : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun u := tens u w
  map_add' u u' := by ext p; simp [tens, add_mul]
  map_smul' c u := by ext p; simp [tens, mul_assoc]

lemma continuous_tens_left (w : EuclideanSpace ℝ κ) :
    Continuous fun u : EuclideanSpace ℝ ι => tens u w :=
  (tensRight (ι := ι) w).continuous_of_finiteDimensional

/-- The measurable bad set, built from a countable dense family of `W = ℝ^κ`. -/
noncomputable def Bset {r : ℕ} (q : ℕ) (lam2 : ℝ) :
    Set ((Fin r → EuclideanSpace ℝ (ι × κ)) × EuclideanSpace ℝ ι) :=
  {p | ∃ v : Fin q → ℕ,
    LinearIndependent ℝ (fun j => TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) (v j)) ∧
    ∀ a : Fin q → ℚ,
      Phi (tens p.2 (∑ j, (a j : ℝ) • TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) (v j))) p.1 ≤
        lam2 * ‖∑ j, (a j : ℝ) • TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) (v j)‖}

lemma measurable_Phi {r : ℕ} (w : EuclideanSpace ℝ κ) :
    Measurable fun p : (Fin r → EuclideanSpace ℝ (ι × κ)) × EuclideanSpace ℝ ι =>
      Phi (tens p.2 w) p.1 := by
  unfold Phi
  refine Measurable.iInf fun a => ?_
  refine Continuous.measurable ?_
  have h1 : Continuous fun p : (Fin r → EuclideanSpace ℝ (ι × κ)) × EuclideanSpace ℝ ι =>
      tens p.2 w := (continuous_tens_left w).comp continuous_snd
  have h2 : Continuous fun p : (Fin r → EuclideanSpace ℝ (ι × κ)) × EuclideanSpace ℝ ι =>
      ∑ j, (a j : ℝ) • p.1 j :=
    continuous_finsetSum _ fun j _ => by fun_prop
  exact (h1.sub h2).norm

lemma measurableSet_Bset {r : ℕ} (q : ℕ) (lam2 : ℝ) :
    MeasurableSet (Bset (ι := ι) (κ := κ) (r := r) q lam2) := by
  have : Bset (ι := ι) (κ := κ) (r := r) q lam2 = ⋃ v : Fin q → ℕ,
      {p | LinearIndependent ℝ (fun j => TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) (v j))} ∩
      ⋂ a : Fin q → ℚ, {p | Phi (tens p.2 (∑ j, (a j : ℝ) •
        TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) (v j))) p.1 ≤
        lam2 * ‖∑ j, (a j : ℝ) • TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) (v j)‖} := by
    ext p; simp [Bset]
  rw [this]
  refine MeasurableSet.iUnion fun v => MeasurableSet.inter (MeasurableSet.const _) ?_
  refine MeasurableSet.iInter fun a => ?_
  exact measurableSet_le (measurable_Phi _) measurable_const

lemma claim2 {r : ℕ} (q : ℕ) (lam2 : ℝ) (hl2 : 0 ≤ lam2)
    (y : Fin r → EuclideanSpace ℝ (ι × κ)) (u : EuclideanSpace ℝ ι)
    (hp : (y, u) ∈ Bset (ι := ι) (κ := κ) q lam2) :
    q ≤ numSmallSV (Mop (Submodule.span ℝ (Set.range y)) u) lam2 := by
  obtain ⟨v, hLI, ha⟩ := hp
  set D := TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) with hD
  set X := Submodule.span ℝ (Set.range y) with hX
  have hf : Continuous fun a : Fin q → ℝ => ‖Mop X u (∑ j, a j • D (v j))‖ := by
    refine (LinearMap.continuous_of_finiteDimensional (Mop X u)).comp ?_ |>.norm
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  have hg : Continuous fun a : Fin q → ℝ => lam2 * ‖∑ j, a j • D (v j)‖ := by
    refine continuous_const.mul (Continuous.norm ?_)
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  have hclosed : IsClosed {a : Fin q → ℝ | ‖Mop X u (∑ j, a j • D (v j))‖ ≤
      lam2 * ‖∑ j, a j • D (v j)‖} := isClosed_le hf hg
  have hdense : DenseRange (fun a : Fin q → ℚ => fun j => (a j : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast) 
  have hall : ∀ a : Fin q → ℝ, ‖Mop X u (∑ j, a j • D (v j))‖ ≤ lam2 * ‖∑ j, a j • D (v j)‖ := by
    have hsub : Set.range (fun a : Fin q → ℚ => fun j => (a j : ℝ)) ⊆
        {a : Fin q → ℝ | ‖Mop X u (∑ j, a j • D (v j))‖ ≤ lam2 * ‖∑ j, a j • D (v j)‖} := by
      rintro _ ⟨a, rfl⟩
      have := ha a
      rw [Phi_eq] at this
      exact this
    intro a
    have : a ∈ closure (Set.range (fun a : Fin q → ℚ => fun j => (a j : ℝ))) := by
      rw [hdense.closure_eq]; trivial
    exact (closure_minimal hsub hclosed) this
  refine numSmallSV_ge _ lam2 hl2 q (Submodule.span ℝ (Set.range fun j => D (v j))) ?_ ?_
  · rw [finrank_span_eq_card hLI]; simp
  · intro w hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
    exact hall c


lemma claim1 {r : ℕ} (q : ℕ) (hq : 1 ≤ q) (lam1 lam2 : ℝ) (h1 : 0 ≤ lam1) (h12 : lam1 < lam2)
    (y : Fin r → EuclideanSpace ℝ (ι × κ)) (u : EuclideanSpace ℝ ι)
    (hν : q ≤ numSmallSV (Mop (Submodule.span ℝ (Set.range y)) u) lam1) :
    (y, u) ∈ Bset (ι := ι) (κ := κ) q lam2 := by
  set D := TopologicalSpace.denseSeq (EuclideanSpace ℝ κ) with hD
  set X := Submodule.span ℝ (Set.range y) with hX
  obtain ⟨U, hqU, hU⟩ := small_subspace (Mop X u) lam1 h1 q hν
  let B := stdOrthonormalBasis ℝ U
  let b : Fin q → EuclideanSpace ℝ κ := fun j => (B (Fin.castLE hqU j) : EuclideanSpace ℝ κ)
  have hbU : ∀ j, b j ∈ U := fun j => (B (Fin.castLE hqU j)).2
  have hon : Orthonormal ℝ b := by
    have h0 : Orthonormal ℝ (fun j : Fin q => B (Fin.castLE hqU j)) :=
      B.orthonormal.comp _ (Fin.castLE_injective hqU)
    exact (U.subtypeₗᵢ.orthonormal_comp_iff).2 h0
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set ε : ℝ := (lam2 - lam1) / (lam2 + ‖u‖ + 1) with hε
  have hden : 0 < lam2 + ‖u‖ + 1 := by have := norm_nonneg u; linarith
  have hεpos : 0 < ε := div_pos (by linarith) hden
  have hεe : ε * (lam2 + ‖u‖ + 1) = lam2 - lam1 := by rw [hε]; field_simp
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one hden]; linarith [norm_nonneg u]
  have hδ : 0 < ε / q := by positivity
  have hex : ∀ j, ∃ n, dist (b j) (D n) < ε / q := fun j =>
    (TopologicalSpace.denseRange_denseSeq (EuclideanSpace ℝ κ)).exists_dist_lt (b j) hδ
  choose v hv using hex
  have hw0 : ∀ a : Fin q → ℝ, ∑ j, a j • b j ∈ U := fun a =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbU j)
  have hcoef : ∀ (a : Fin q → ℝ) j, |a j| ≤ ‖∑ j, a j • b j‖ := by
    intro a j
    have := hon.inner_right_fintype a j
    calc |a j| = |inner ℝ (b j) (∑ j, a j • b j)| := by rw [this]
      _ ≤ ‖b j‖ * ‖∑ j, a j • b j‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [hon.1 j]; ring
  have key : ∀ a : Fin q → ℝ,
      ‖∑ j, a j • D (v j) - ∑ j, a j • b j‖ ≤ ε * ‖∑ j, a j • b j‖ := by
    intro a
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ j, (a j • D (v j) - a j • b j)‖ ≤ ∑ j, ‖a j • D (v j) - a j • b j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin q, (ε / q) * ‖∑ j, a j • b j‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, norm_sub_rev]
          calc |a j| * ‖b j - D (v j)‖ ≤ ‖∑ j, a j • b j‖ * (ε / q) := by
                refine mul_le_mul (hcoef a j) ?_ (norm_nonneg _) (norm_nonneg _)
                rw [← dist_eq_norm]; exact (hv j).le
            _ = _ := by ring
      _ = ε * ‖∑ j, a j • b j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  refine ⟨v, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a hz j
    have h := key a
    rw [hz, zero_sub, norm_neg] at h
    have h2 : (1 - ε) * ‖∑ j, a j • b j‖ ≤ 0 := by linarith
    have h3 : ‖∑ j, a j • b j‖ ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have := hcoef a j
    have : |a j| = 0 := le_antisymm (by linarith) (abs_nonneg _)
    exact abs_eq_zero.1 this
  · intro a
    rw [Phi_eq]
    show ‖Mop X u _‖ ≤ _
    set w := ∑ j, (a j : ℝ) • D (v j) with hw
    set w0 := ∑ j, (a j : ℝ) • b j with hw0'
    have hk := key (fun j => (a j : ℝ))
    have hM0 := hU w0 (hw0 _)
    have hMd : ‖Mop X u (w - w0)‖ ≤ ‖u‖ * (ε * ‖w0‖) :=
      (norm_Mop_le X u _).trans (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
    have hsplit : Mop X u w = Mop X u w0 + Mop X u (w - w0) := by rw [← map_add]; congr 1; abel
    have hwn : (1 - ε) * ‖w0‖ ≤ ‖w‖ := by
      have := norm_sub_norm_le w0 w
      rw [norm_sub_rev] at this
      nlinarith [norm_nonneg w0]
    have hn0 := norm_nonneg w0
    calc ‖Mop X u w‖ ≤ ‖Mop X u w0‖ + ‖Mop X u (w - w0)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ lam1 * ‖w0‖ + ‖u‖ * (ε * ‖w0‖) := add_le_add hM0 hMd
      _ ≤ lam2 * ((1 - ε) * ‖w0‖) := by
          have : lam1 + ‖u‖ * ε ≤ lam2 * (1 - ε) := by nlinarith
          nlinarith
      _ ≤ lam2 * ‖w‖ := mul_le_mul_of_nonneg_left hwn (by linarith)


lemma norm_proj_le_infDist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) (u : E) :
    ‖Kᗮ.starProjection u‖ ≤ Metric.infDist u (K : Set E) := by
  refine (Metric.le_infDist ⟨0, K.zero_mem⟩).2 fun x hx => ?_
  have h : Kᗮ.starProjection (u - x) = Kᗮ.starProjection u := by
    rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hx, sub_zero]
  rw [dist_eq_norm, ← h]; exact Submodule.norm_starProjection_apply_le Kᗮ _

lemma section_bound {r : ℕ} (NG : ℕ) (hr : r ≤ NG) (q : ℕ) (hq : 1 ≤ q)
    (hdq : 2 * NG < Fintype.card ι * q) (lam2 η₀ γ : ℝ) (hl2 : 0 ≤ lam2)
    (hlam : lam2 * ((NG : ℝ) / q + 1) ≤ η₀) (μ : Measure (EuclideanSpace ℝ ι))
    (hsa : SubspaceAnticonc (1 / 4) η₀ γ μ) (y : Fin r → EuclideanSpace ℝ (ι × κ)) :
    μ {u | (y, u) ∈ Bset (ι := ι) (κ := κ) q lam2} ≤ ENNReal.ofReal (Real.exp (-γ)) := by
  set X := Submodule.span ℝ (Set.range y) with hX
  have hXd : finrank ℝ X ≤ NG := by
    refine le_trans ?_ hr
    calc finrank ℝ X ≤ Fintype.card (Fin r) := finrank_range_le_card _
      _ = r := Fintype.card_fin r
  set k := NG / q with hk
  have hkq : k * q ≤ NG := Nat.div_mul_le_self _ _
  have h2k : 2 * k < Fintype.card ι := by
    have : 2 * k * q < Fintype.card ι * q := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨Unull, hUd, hU⟩ := ApproxSyzygies.Smoothed.lemma_4_9 X NG hXd q hq (by omega) lam2 hl2
  refine le_trans (measure_mono ?_) (hsa.2.2 Unullᗮ ?_)
  · intro u hu
    have h1 := claim2 q lam2 hl2 y u hu
    have h2 := hU u h1
    simp only [Set.mem_setOf_eq]
    exact (norm_proj_le_infDist Unull u).trans (h2.trans hlam)
  · have hd : finrank ℝ Unullᗮ + finrank ℝ Unull = Fintype.card ι := by
      have := Submodule.finrank_add_finrank_orthogonal Unull
      rw [finrank_euclideanSpace] at this; omega
    have : 4 * finrank ℝ Unullᗮ ≥ Fintype.card ι := by omega
    have h' : (Fintype.card ι : ℝ) ≤ 4 * (finrank ℝ Unullᗮ : ℝ) := by exact_mod_cast this
    linarith

lemma prob_bound {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m r : ℕ} (ζ : Ω → EuclideanSpace ℝ ι) (hζ : Measurable ζ)
    (𝓕 : Fin m → MeasurableSpace Ω) (i : Fin m) (h𝓕 : 𝓕 i ≤ mΩ)
    (Y : Ω → (Fin r → EuclideanSpace ℝ (ι × κ)))
    (hY : Measurable[𝓕 i] Y)
    (hind : Indep (MeasurableSpace.comap ζ inferInstance) (𝓕 i) P)
    (B : Set ((Fin r → EuclideanSpace ℝ (ι × κ)) × EuclideanSpace ℝ ι)) (hB : MeasurableSet B)
    (c : ENNReal) (hc : ∀ y, (P.map ζ) {u | (y, u) ∈ B} ≤ c) :
    P {ω | (Y ω, ζ ω) ∈ B} ≤ c := by
  have hYm : Measurable Y := hY.mono h𝓕 le_rfl
  have hI : IndepFun Y ζ P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind.symm hY.comap_le
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hζ.aemeasurable).1 hI
  have hm : Measurable fun ω => (Y ω, ζ ω) := hYm.prodMk hζ
  have : P {ω | (Y ω, ζ ω) ∈ B} = (P.map fun ω => (Y ω, ζ ω)) B := by
    rw [Measure.map_apply hm hB]; rfl
  rw [this, hmap, Measure.prod_apply hB]
  calc ∫⁻ y, (P.map ζ) (Prod.mk y ⁻¹' B) ∂(P.map Y) ≤ ∫⁻ y, c ∂(P.map Y) :=
        lintegral_mono fun y => hc y
    _ = c := by
        rw [lintegral_const]
        haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
        simp

end BadSet

lemma assemble {m : ℕ} {ι κ : Fin m → Type} [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (G : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i))) (NG : ℕ) (η₀ : ℝ)
    (hη₀ : ∀ _ : Fin m, 0 < η₀) (hdim : ∀ i, 4 ≤ Fintype.card (ι i))
    (ζv : ∀ i, EuclideanSpace ℝ (ι i))
    (C : ∀ i, G →L[ℝ] EuclideanSpace ℝ (ι i × κ i))
    (X : ∀ i, Submodule ℝ (EuclideanSpace ℝ (ι i × κ i)))
    (hCX : ∀ i g, C i g ∈ X i)
    (hS : ∀ i, ¬ (2 * NG / Fintype.card (ι i) + 1) ≤
      numSmallSV (Mop (X i) (ζv i)) (η₀ / Fintype.card (ι i))) :
    ∃ G' : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i)), G' ≤ G ∧
      (Module.finrank ℝ G' : ℝ) ≤ 2 * ∑ i, (NG : ℝ) / (Fintype.card (ι i) : ℝ) ∧
      ∀ (η : ℝ) (g : G),
        (∀ i, ‖tens (ζv i) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i) + C i g‖ ≤ η) →
        Metric.infDist (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) G' ≤
          η * Real.sqrt (∑ i, ((Fintype.card (ι i) : ℝ)) ^ 2) / η₀ := by
  classical
  have hd : ∀ i, (0 : ℝ) < Fintype.card (ι i) := fun i => by
    have := hdim i; exact Nat.cast_pos.2 (by omega)
  have hl1 : ∀ i, 0 ≤ η₀ / (Fintype.card (ι i) : ℝ) := fun i => (div_pos (hη₀ i) (hd i)).le
  have hSub : ∀ i, ∃ S : Submodule ℝ (EuclideanSpace ℝ (κ i)),
      finrank ℝ S ≤ 2 * NG / Fintype.card (ι i) ∧
      ∀ w, ∃ s ∈ S, (η₀ / Fintype.card (ι i)) * ‖w - s‖ ≤ ‖Mop (X i) (ζv i) w‖ := by
    intro i
    obtain ⟨S, hS1, hS2⟩ := large_subspace (Mop (X i) (ζv i)) _ (hl1 i)
    exact ⟨S, by have := not_le.1 (hS i); omega, hS2⟩
  choose S hSd hSs using hSub
  let Φ : (∀ i, S i) →ₗ[ℝ] PiLp 2 (fun i => EuclideanSpace ℝ (κ i)) :=
    (WithLp.linearEquiv 2 ℝ (∀ i, EuclideanSpace ℝ (κ i))).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun i => (S i).subtype ∘ₗ LinearMap.proj i)
  let PG : PiLp 2 (fun i => EuclideanSpace ℝ (κ i)) →ₗ[ℝ] PiLp 2 (fun i => EuclideanSpace ℝ (κ i)) :=
    (G.starProjection : PiLp 2 (fun i => EuclideanSpace ℝ (κ i)) →L[ℝ]
      PiLp 2 (fun i => EuclideanSpace ℝ (κ i))).toLinearMap
  refine ⟨(LinearMap.range Φ).map PG, ?_, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩; exact Submodule.starProjection_apply_mem G x
  · have h1 : finrank ℝ ((LinearMap.range Φ).map PG) ≤ ∑ i, 2 * NG / Fintype.card (ι i) := by
      calc finrank ℝ ((LinearMap.range Φ).map PG) ≤ finrank ℝ (LinearMap.range Φ) :=
            Submodule.finrank_map_le _ _
        _ ≤ finrank ℝ (∀ i, S i) := LinearMap.finrank_range_le _
        _ = ∑ i, finrank ℝ (S i) := Module.finrank_pi_fintype ℝ
        _ ≤ _ := Finset.sum_le_sum fun i _ => hSd i
    have h2 : ((∑ i, 2 * NG / Fintype.card (ι i) : ℕ) : ℝ) ≤
        2 * ∑ i, (NG : ℝ) / (Fintype.card (ι i) : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ((2 * NG / Fintype.card (ι i) : ℕ) : ℝ) ≤ ((2 * NG : ℕ) : ℝ) / (Fintype.card (ι i) : ℝ) :=
            Nat.cast_div_le
        _ = _ := by push_cast; ring
    exact (Nat.cast_le.2 h1).trans h2
  · intro η g hg
    have hgi : ∀ i, ∃ s ∈ S i, ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i - s‖ ≤
        η * Fintype.card (ι i) / η₀ := by
      intro i
      obtain ⟨s, hs, hle⟩ := hSs i ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i)
      refine ⟨s, hs, ?_⟩
      have hMle : ‖Mop (X i) (ζv i) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i)‖ ≤ η := by
        refine le_trans ?_ (hg i)
        rw [Mop_apply]
        have h0 : (X i)ᗮ.starProjection (C i g) = 0 := Submodule.starProjection_orthogonal_apply_eq_zero (hCX i g)
        calc _ = ‖(X i)ᗮ.starProjection (tens (ζv i) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i) + C i g)‖ := by
              rw [map_add, h0, add_zero]
          _ ≤ _ := Submodule.norm_starProjection_apply_le _ _
      have h3 : (η₀ / Fintype.card (ι i)) * ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i - s‖ ≤ η :=
        hle.trans hMle
      rw [le_div_iff₀ (hη₀ i)]
      have := hd i
      have h4 : η₀ * ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i - s‖ ≤ η * Fintype.card (ι i) := by
        have := mul_le_mul_of_nonneg_left h3 this.le
        calc _ = (Fintype.card (ι i) : ℝ) * ((η₀ / Fintype.card (ι i)) * ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i - s‖) := by
              field_simp
          _ ≤ _ := this
          _ = _ := by ring
      linarith
    choose s hsS hsb using hgi
    set sv : PiLp 2 (fun i => EuclideanSpace ℝ (κ i)) := WithLp.toLp 2 (fun i => s i) with hsv
    have hsvmem : sv ∈ LinearMap.range Φ :=
      ⟨fun i => ⟨s i, hsS i⟩, by ext i j; simp [Φ, sv]⟩
    have hmemG' : PG sv ∈ (LinearMap.range Φ).map PG := ⟨sv, hsvmem, rfl⟩
    have hgG : PG (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) = g :=
      Submodule.starProjection_eq_self_iff.2 g.2
    refine (Metric.infDist_le_dist_of_mem hmemG').trans ?_
    have hdist : dist (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) (PG sv) ≤
        ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) - sv‖ := by
      rw [dist_eq_norm]
      calc _ = ‖PG ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) - sv)‖ := by
            rw [map_sub, hgG]
        _ ≤ _ := Submodule.norm_starProjection_apply_le G _
    refine hdist.trans ?_
    have hsq : ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) - sv‖ ^ 2 ≤
        ∑ i, (η * Fintype.card (ι i) / η₀) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hsb i
      simpa [sv] using pow_le_pow_left₀ (norm_nonneg _) this 2
    have hsum : ∑ i, (η * Fintype.card (ι i) / η₀) ^ 2 =
        (η / η₀) ^ 2 * ∑ i, ((Fintype.card (ι i) : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    have hnn : 0 ≤ η * Real.sqrt (∑ i, ((Fintype.card (ι i) : ℝ)) ^ 2) / η₀ := by
      rcases isEmpty_or_nonempty (Fin m) with h | hne
      · simp
      · obtain ⟨i0⟩ := hne
        have hη : 0 ≤ η := (norm_nonneg _).trans (hg i0)
        have := hη₀ i0
        positivity
    refine le_of_sq_le_sq ?_ hnn
    rw [div_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    calc _ ≤ _ := hsq
      _ = _ := by rw [hsum, div_pow]; ring

end ApproxSyzygies.Smoothed.Dev.L47

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

theorem chk_lemma_4_7 {m : ℕ} {ι κ : Fin m → Type} [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (G : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i))) (NG : ℕ)
    (hG : Module.finrank ℝ G ≤ NG) (η₀ γ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ζ : ∀ i, Ω → EuclideanSpace ℝ (ι i)) (hζ : ∀ i, Measurable (ζ i))
    (hind : iIndepFun ζ P)
    (hsa : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ (P.map (ζ i)))
    (hdim : ∀ i, 4 ≤ Fintype.card (ι i))
    (C : ∀ i, Ω → (G →L[ℝ] EuclideanSpace ℝ (ι i × κ i)))
    (𝓕 : Fin m → MeasurableSpace Ω) (h𝓕 : ∀ i, 𝓕 i ≤ ‹MeasurableSpace Ω›)
    (hCmeas : ∀ i (g : G), Measurable[𝓕 i] fun ω => C i ω g)
    (hCind : ∀ i, Indep (MeasurableSpace.comap (ζ i) inferInstance) (𝓕 i) P) :
    P {ω | ¬ ∃ G' : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i)), G' ≤ G ∧
          (Module.finrank ℝ G' : ℝ) ≤ 2 * ∑ i, (NG : ℝ) / (Fintype.card (ι i) : ℝ) ∧
          ∀ (η : ℝ) (g : G),
            (∀ i, ‖tens (ζ i ω) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i) + C i ω g‖ ≤ η) →
            Metric.infDist (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) G' ≤
              η * Real.sqrt (∑ i, ((Fintype.card (ι i) : ℝ)) ^ 2) / η₀}
      ≤ ENNReal.ofReal (m * Real.exp (-γ)) := by
  classical
  let bG := Module.finBasis ℝ G
  let Y : ∀ i, Ω → (Fin (Module.finrank ℝ G) → EuclideanSpace ℝ (ι i × κ i)) :=
    fun i ω j => C i ω (bG j)
  let q : Fin m → ℕ := fun i => 2 * NG / Fintype.card (ι i) + 1
  let A : Fin m → Set Ω := fun i => {ω | (Y i ω, ζ i ω) ∈
    Dev.L47.Bset (ι := ι i) (κ := κ i) (q i) (η₀ / ((Fintype.card (ι i) : ℝ) / 2 + 1))}
  have hη₀ : ∀ i, 0 < η₀ := fun i => (hsa i).2.1
  have hdpos : ∀ i, (4 : ℝ) ≤ Fintype.card (ι i) := fun i => by exact_mod_cast hdim i
  have hA : ∀ i, P (A i) ≤ ENNReal.ofReal (Real.exp (-γ)) := by
    intro i
    have hYm : Measurable[𝓕 i] (Y i) := by
      letI := 𝓕 i
      exact measurable_pi_iff.2 fun j => hCmeas i (bG j)
    refine Dev.L47.prob_bound P (ζ i) (hζ i) 𝓕 i (h𝓕 i) (Y i) hYm (hCind i) _
      (Dev.L47.measurableSet_Bset _ _) _ fun y => ?_
    have hdq : 2 * NG < Fintype.card (ι i) * q i :=
      Nat.lt_mul_div_succ _ (by have := hdim i; omega)
    have hdq' : (2 * NG : ℝ) < Fintype.card (ι i) * (q i : ℝ) := by exact_mod_cast hdq
    have hqpos : (0 : ℝ) < q i := by exact_mod_cast Nat.succ_pos _
    have hd2 : (0 : ℝ) < (Fintype.card (ι i) : ℝ) / 2 + 1 := by linarith [hdpos i]
    refine Dev.L47.section_bound (κ := κ i) NG hG (q i) (Nat.le_add_left 1 _) hdq _ η₀ γ
      (div_pos (hη₀ i) hd2).le ?_ (P.map (ζ i)) (hsa i) y
    have h1 : (NG : ℝ) / q i ≤ (Fintype.card (ι i) : ℝ) / 2 := by
      rw [div_le_iff₀ hqpos]; linarith
    calc η₀ / ((Fintype.card (ι i) : ℝ) / 2 + 1) * ((NG : ℝ) / q i + 1)
        ≤ η₀ / ((Fintype.card (ι i) : ℝ) / 2 + 1) * ((Fintype.card (ι i) : ℝ) / 2 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos (hη₀ i) hd2).le
      _ = η₀ := by field_simp
  have hsub : {ω | ¬ ∃ G' : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i)), G' ≤ G ∧
          (Module.finrank ℝ G' : ℝ) ≤ 2 * ∑ i, (NG : ℝ) / (Fintype.card (ι i) : ℝ) ∧
          ∀ (η : ℝ) (g : G),
            (∀ i, ‖tens (ζ i ω) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i) + C i ω g‖ ≤ η) →
            Metric.infDist (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) G' ≤
              η * Real.sqrt (∑ i, ((Fintype.card (ι i) : ℝ)) ^ 2) / η₀} ⊆ ⋃ i, A i := by
    intro ω hω
    by_contra hn
    apply hω
    refine Dev.L47.assemble G NG η₀ (fun i => hη₀ i) hdim (fun i => ζ i ω) (fun i => C i ω)
      (fun i => Submodule.span ℝ (Set.range (Y i ω))) ?_ ?_
    · intro i g
      have : g = ∑ j, bG.repr g j • bG j := (bG.sum_repr g).symm
      rw [this, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro i hν
      refine hn (Set.mem_iUnion.2 ⟨i, ?_⟩)
      have hd := hdpos i
      refine Dev.L47.claim1 (q i) (Nat.le_add_left 1 _) _ _
        (div_pos (hη₀ i) (by linarith)).le ?_ (Y i ω) (ζ i ω) hν
      exact div_lt_div_of_pos_left (hη₀ i) (by linarith) (by linarith)
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_iUnion_fintype_le P A) ?_
  calc ∑ i, P (A i) ≤ ∑ _i : Fin m, ENNReal.ofReal (Real.exp (-γ)) :=
        Finset.sum_le_sum fun i _ => hA i
    _ = ENNReal.ofReal (m * Real.exp (-γ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_lemma_4_7 := @ApproxSyzygies.Smoothed.chk_lemma_4_7
