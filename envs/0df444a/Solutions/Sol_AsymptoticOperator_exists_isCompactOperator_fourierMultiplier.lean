-- Prove2me | solution 1 for AsymptoticOperator.exists_isCompactOperator_fourierMultiplier
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:23:48.991985+00:00
-- url     : https://prove2.me/submissions/ab03c15e-3cb5-4f93-8654-9c884881ab05

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
import Theorems.Thm_AsymptoticOperator_exists_coeff_eq

namespace AsymptoticOperator

noncomputable section

open MeasureTheory Matrix ConleyZehnder

variable {n : ℕ}

/-- `complexify` as a continuous `ℝ`-linear map. -/
def cxL (n : ℕ) : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

lemma cxL_apply (v : Vec n) : cxL n v = complexify v := rfl

lemma integrable_L2 (f : L2 n) : Integrable (f : UnitAddCircle → Vec n) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (Lp.memLp f).integrable one_le_two

lemma integrable_cx (f : L2 n) : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (cxL n).integrable_comp (integrable_L2 f)

lemma integrable_mul (S : C(UnitAddCircle, Mat n)) (f : L2 n) :
    Integrable (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rw [integrable_pi_iff]
  intro i
  simp only [mulVec, dotProduct]
  refine integrable_finsetSum _ fun j _ => ?_
  have hj : Integrable (fun t => complexify (f t) j) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (integrable_pi_iff.1 (integrable_cx f)) j
  have hc : Continuous fun t => S t i j :=
    (continuous_apply j).comp ((continuous_apply i).comp S.continuous)
  let Sij : C(UnitAddCircle, ℝ) := ⟨fun t => S t i j, hc⟩
  refine hj.bdd_mul (c := ‖Sij‖) ?_ ?_
  · exact (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
  · refine ae_of_all _ fun t => ?_
    simp only [Matrix.map_apply, Complex.norm_real]
    exact Sij.norm_coe_le_norm t

lemma complexify_add (v w : Vec n) : complexify (v + w) = complexify v + complexify w := by
  simp only [← cxL_apply, map_add]

lemma complexify_smul (c : ℝ) (v : Vec n) : complexify (c • v) = (c : ℂ) • complexify v := by
  funext i; simp [complexify]

lemma coeff_add (f g : L2 n) : coeff ((f + g : L2 n) : UnitAddCircle → Vec n) = coeff f + coeff g := by
  have h : (fun t => complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => complexify (f t)) + (fun t => complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    simp only [ht, Pi.add_apply, complexify_add]
  funext k
  simp only [coeff]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (integrable_cx f) (integrable_cx g)]
  rfl

lemma coeff_smul (c : ℝ) (f : L2 n) : coeff ((c • f : L2 n) : UnitAddCircle → Vec n) = (c : ℂ) • coeff f := by
  have h : (fun t => complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    simp only [ht, Pi.smul_apply, complexify_smul]
  funext k
  simp only [coeff]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma coeff_zero : coeff ((0 : L2 n) : UnitAddCircle → Vec n) = 0 := by
  have := coeff_smul (0 : ℝ) (0 : L2 n)
  rwa [zero_smul, Complex.ofReal_zero, zero_smul] at this

lemma coeffMul_add (S : C(UnitAddCircle, Mat n)) (f g : L2 n) :
    coeffMul S ((f + g : L2 n) : UnitAddCircle → Vec n) = coeffMul S f + coeffMul S g := by
  have h : (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify ((f + g : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) +
        (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (g t)) := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    simp only [ht, Pi.add_apply, complexify_add, mulVec_add]
  funext k
  simp only [coeffMul]
  rw [fourierCoeff_congr_ae h, fourierCoeff.add (integrable_mul S f) (integrable_mul S g)]
  rfl

lemma coeffMul_smul (S : C(UnitAddCircle, Mat n)) (c : ℝ) (f : L2 n) :
    coeffMul S ((c • f : L2 n) : UnitAddCircle → Vec n) = (c : ℂ) • coeffMul S f := by
  have h : (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify ((c • f : L2 n) t)) =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)]
      (c : ℂ) • (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (f t)) := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    simp only [ht, Pi.smul_apply, complexify_smul, mulVec_smul]
  funext k
  simp only [coeffMul]
  rw [fourierCoeff_congr_ae h]
  exact fourierCoeff.const_smul _ _ k

lemma coeffMul_zero (S : C(UnitAddCircle, Mat n)) :
    coeffMul S ((0 : L2 n) : UnitAddCircle → Vec n) = 0 := by
  have := coeffMul_smul S (0 : ℝ) (0 : L2 n)
  rwa [zero_smul, Complex.ofReal_zero, zero_smul] at this

lemma eq_zero_of_coeff_eq_zero (g : L2 n) (h : ∀ k, coeff g k = 0) : g = 0 := by
  have hcomp : ∀ i, ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), (g t) i = 0 := by
    intro i
    let L : Vec n →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj i)
    let g' : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) := L.compLp g
    have hcoef : ∀ k, fourierCoeff (g' : UnitAddCircle → ℂ) k = 0 := by
      intro k
      rw [fourierCoeff_congr_ae (L.coeFn_compLp' g)]
      have hint := (integrable_cx g).fourier_smul (-k)
      have e := eval_integral (integrable_pi_iff.1 hint) i
      have : coeff g k i = fourierCoeff (fun t => L (g t)) k := by
        show (∫ t, fourier (-k) t • complexify (g t) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) i =
          ∫ t, fourier (-k) t • L (g t) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
        rw [e]; rfl
      rw [← this, h k]; rfl
    have h0 : g' = 0 := by
      apply fourierBasis.repr.injective
      rw [map_zero]
      ext k
      rw [fourierBasis_repr, hcoef]
      rfl
    filter_upwards [L.coeFn_compLp' g, Lp.coeFn_zero ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)] with t h1 h2
    have : L (g t) = 0 := by
      rw [← h1]; change (g' : UnitAddCircle → ℂ) t = 0; rw [h0]; exact h2
    simpa [L] using this
  apply Lp.ext
  filter_upwards [ae_all_iff.2 hcomp, Lp.coeFn_zero (Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)] with t ht h0
  rw [h0]
  ext i
  exact ht i

end

end AsymptoticOperator

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate Filter Topology

lemma ao6_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

lemma ao6_coeff_neg {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f (-k) i = conj (coeff f k i) := by
  rw [ao6_coeff_apply, ao6_coeff_apply]
  simp only [fourierCoeff]
  rw [← integral_conj]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal, neg_neg, fourier_neg,
    Complex.conj_conj]

lemma ao6_re_self {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) :
    (∑ i, conj (v i) * v i).re = ∑ i, ‖v i‖ ^ 2 := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  norm_cast

/-- Parseval: `‖f‖² = ∑ₖ |f̂ₖ|²`. -/
lemma ao6_norm_sq {n : ℕ} (f : L2 n) :
    HasSum (fun k : ℤ => ∑ i, ‖coeff f k i‖ ^ 2) (‖f‖ ^ 2) := by
  have h := hasSum_inner_coeff f f
  simp only [ao6_re_self, real_inner_self_eq_norm_sq] at h
  exact h

lemma ao6_norm_le {n : ℕ} (f g : L2 n) (ε : ℝ)
    (h : ∀ k, ∑ i, ‖coeff f k i‖ ^ 2 ≤ ε * ∑ i, ‖coeff g k i‖ ^ 2) :
    ‖f‖ ^ 2 ≤ ε * ‖g‖ ^ 2 :=
  hasSum_le h (ao6_norm_sq f) ((ao6_norm_sq g).mul_left ε)

lemma ao6_coeff_sub {n : ℕ} (f g : L2 n) (k : ℤ) :
    coeff ((f - g : L2 n) : UnitAddCircle → Vec n) k = coeff f k - coeff g k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, coeff_add, coeff_smul]
  simp [sub_eq_add_neg]

lemma ao6_ext {n : ℕ} (f g : L2 n) (h : ∀ k, coeff f k = coeff g k) : f = g :=
  sub_eq_zero.1 (AsymptoticOperator.eq_zero_of_coeff_eq_zero _ fun k => by
    rw [ao6_coeff_sub, h k, sub_self])

lemma ao6_mulVec_conj {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (v : Fin n ⊕ Fin n → ℂ) (i : Fin n ⊕ Fin n) :
    (M.map (starRingEnd ℂ) *ᵥ fun j => conj (v j)) i = conj ((M *ᵥ v) i) := by
  simp [mulVec, dotProduct, map_sum, map_mul]

/-- A bounded conjugate-symmetric Fourier multiplier as a continuous linear map. -/
lemma ao6_mult {n : ℕ} (m : ℤ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hm : ∀ k, m (-k) = (m k).map (starRingEnd ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (k : ℤ) (v : Fin n ⊕ Fin n → ℂ), ∑ i, ‖(m k *ᵥ v) i‖ ^ 2 ≤ C * ∑ i, ‖v i‖ ^ 2) :
    ∃ T : L2 n →L[ℝ] L2 n, ∀ (g : L2 n) (k : ℤ), coeff (T g) k = m k *ᵥ coeff g k := by
  have hex : ∀ g : L2 n, ∃ h : L2 n, ∀ k, coeff h k = m k *ᵥ coeff g k := by
    intro g
    apply exists_coeff_eq
    · exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hb k _)
        ((ao6_norm_sq g).summable.mul_left C)
    · intro k i
      rw [hm k, show coeff g (-k) = fun j => conj (coeff g k j) from
        funext fun j => ao6_coeff_neg g k j]
      exact ao6_mulVec_conj _ _ _
  choose F hF using hex
  let L : L2 n →ₗ[ℝ] L2 n :=
    { toFun := F
      map_add' := fun f g => ao6_ext _ _ fun k => by
        simp only [hF, coeff_add, Pi.add_apply, mulVec_add]
      map_smul' := fun c f => ao6_ext _ _ fun k => by
        simp only [hF, coeff_smul, RingHom.id_apply, Pi.smul_apply, mulVec_smul] }
  refine ⟨L.mkContinuous (Real.sqrt C) fun g => ?_, fun g k => hF g k⟩
  have h2 : ‖F g‖ ^ 2 ≤ (Real.sqrt C * ‖g‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    exact ao6_norm_le _ _ C fun k => by rw [hF]; exact hb k _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate Filter Topology

theorem solution {n : ℕ}
    (m : ℤ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hm : ∀ k, m (-k) = (m k).map (starRingEnd ℂ))
    (c : ℤ → ℝ) (hc : Filter.Tendsto c Filter.cofinite (nhds 0))
    (hbound : ∀ (k : ℤ) (v : Fin n ⊕ Fin n → ℂ),
      ∑ i, ‖(m k *ᵥ v) i‖ ^ 2 ≤ c k * ∑ i, ‖v i‖ ^ 2) :
    ∃ T : L2 n →L[ℝ] L2 n, IsCompactOperator T ∧
      ∀ (g : L2 n) (k : ℤ), coeff (T g) k = m k *ᵥ coeff g k := by
  obtain ⟨C0, hC0⟩ := hc.bddAbove_range_of_cofinite
  set C := max C0 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hcC : ∀ k, c k ≤ C := fun k => (hC0 ⟨k, rfl⟩).trans (le_max_left _ _)
  have hb : ∀ (k : ℤ) (v : Fin n ⊕ Fin n → ℂ), ∑ i, ‖(m k *ᵥ v) i‖ ^ 2 ≤ C * ∑ i, ‖v i‖ ^ 2 :=
    fun k v => (hbound k v).trans (mul_le_mul_of_nonneg_right (hcC k) (by positivity))
  obtain ⟨T, hT⟩ := ao6_mult m hm C hC hb
  -- truncated symbols
  let mN : ℕ → ℤ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun N k => if k.natAbs ≤ N then m k else 0
  have hmN : ∀ N k, mN N (-k) = (mN N k).map (starRingEnd ℂ) := by
    intro N k
    by_cases h : k.natAbs ≤ N
    · simp only [mN, Int.natAbs_neg, if_pos h, hm k]
    · simp only [mN, Int.natAbs_neg, if_neg h]
      ext i j; simp
  have hbN : ∀ N (k : ℤ) (v : Fin n ⊕ Fin n → ℂ),
      ∑ i, ‖(mN N k *ᵥ v) i‖ ^ 2 ≤ C * ∑ i, ‖v i‖ ^ 2 := by
    intro N k v
    by_cases h : k.natAbs ≤ N
    · simp only [mN, if_pos h]; exact hb k v
    · simp only [mN, if_neg h, zero_mulVec, Pi.zero_apply, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
      positivity
  choose TN hTN using fun N => ao6_mult (mN N) (hmN N) C hC (hbN N)
  -- each truncation has finite-dimensional range
  have hcomp : ∀ N, IsCompactOperator (TN N) := by
    intro N
    let V : Submodule ℝ (L2 n) :=
      { carrier := {f | ∀ k : ℤ, N < k.natAbs → coeff f k = 0}
        add_mem' := fun {f g} hf hg k hk => by
          rw [coeff_add, Pi.add_apply, hf k hk, hg k hk, add_zero]
        zero_mem' := fun k _ => by rw [coeff_zero]; rfl
        smul_mem' := fun c f hf k hk => by
          rw [coeff_smul, Pi.smul_apply, hf k hk, smul_zero] }
    have hV : ∀ g, TN N g ∈ V := fun g k hk => by
      rw [hTN]; simp [mN, not_le.2 hk]
    haveI : FiniteDimensional ℝ V := by
      let φ : V →ₗ[ℝ] (Finset.Icc (-(N : ℤ)) N → Fin n ⊕ Fin n → ℂ) :=
        { toFun := fun f k => coeff (f : L2 n) k
          map_add' := fun f g => by
            funext k
            simp only [Submodule.coe_add, coeff_add, Pi.add_apply]
          map_smul' := fun c f => by
            funext k
            simp only [Submodule.coe_smul, coeff_smul, Pi.smul_apply, RingHom.id_apply]
            rfl }
      refine Module.Finite.of_injective φ ?_
      intro f g hfg
      apply Subtype.ext
      apply ao6_ext
      intro k
      by_cases hk : k.natAbs ≤ N
      · exact congrFun hfg ⟨k, by simp only [Finset.mem_Icc]; omega⟩
      · rw [f.2 k (by omega), g.2 k (by omega)]
    have h1 : IsCompactOperator ((TN N).codRestrict V hV) :=
      isCompactOperator_of_locallyCompactSpace_dom _
    exact h1.continuous_comp continuous_subtype_val
  -- the truncations converge in operator norm
  have hlim : Tendsto TN atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    set ε := (δ / 2) ^ 2 with hε
    have hεpos : 0 < ε := by positivity
    have hfin : {k : ℤ | ¬ c k < ε}.Finite := by
      have : c ⁻¹' Set.Iio ε ∈ cofinite := hc (Iio_mem_nhds hεpos)
      rw [Filter.mem_cofinite] at this
      convert this using 1
      ext k; simp
    obtain ⟨N0, hN0⟩ := (hfin.image Int.natAbs).bddAbove
    refine ⟨N0, fun N hN => ?_⟩
    rw [dist_eq_norm]
    have hop : ‖TN N - T‖ ≤ Real.sqrt ε := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun g => ?_
      have h2 : ‖(TN N - T) g‖ ^ 2 ≤ (Real.sqrt ε * ‖g‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hεpos.le]
        refine ao6_norm_le _ _ ε fun k => ?_
        rw [ContinuousLinearMap.sub_apply, ao6_coeff_sub, hTN, hT]
        by_cases hk : k.natAbs ≤ N
        · simp only [mN, if_pos hk, sub_self, Pi.zero_apply, norm_zero]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            Finset.sum_const_zero]
          positivity
        · simp only [mN, if_neg hk, zero_mulVec, zero_sub, Pi.neg_apply, norm_neg]
          have hck : c k < ε := by
            by_contra hck
            have := hN0 ⟨k, hck, rfl⟩
            omega
          exact (hbound k _).trans (mul_le_mul_of_nonneg_right hck.le (by positivity))
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
    calc ‖TN N - T‖ ≤ Real.sqrt ε := hop
      _ = δ / 2 := by rw [hε, Real.sqrt_sq (by positivity)]
      _ < δ := by linarith
  exact ⟨T, isCompactOperator_of_tendsto hlim (Eventually.of_forall hcomp), hT⟩
