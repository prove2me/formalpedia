-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_weights_hasSum_poisson_rowElt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:52:37.123287+00:00
-- url     : https://prove2.me/submissions/59c35d63-aed8-4353-a1cc-923a1b3489ff

import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral
import Theorems.Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Mathlib

section
section
/-!
# L3P_Sfin: the finite places of `S`, combinatorially

`S` a finite type with `q v > 1`. For `j : S → ℤ`, `NN j = ∏ q_v^{j_v}`. The weight
`Om j = Σ_{e ⊆ S} (−1)^{|e|} 1[j + 1_e ≥ 0] / NN (j + 1_e)` is the profile of the Fourier transform
of `∏_v 1_{𝒪_v^×}` (self-dual normalisation), and
`Σ_j Om j · NN j^{1−z} = ∏_v (1 − q_v^{z−1}) / (1 − q_v^{−z})` for `Re z > 0`.
-/

namespace ArtinPrimitiveRoots.L3P

open scoped BigOperators Classical

set_option linter.unusedSectionVars false

/-! ### Products of geometric series over `S → ℕ` -/

theorem hasSum_prod_fin_geom (n : ℕ) : ∀ (x : Fin n → ℂ), (∀ k, ‖x k‖ < 1) →
    HasSum (fun i : Fin n → ℕ => ∏ k, x k ^ i k) (∏ k, (1 - x k)⁻¹) ∧
      Summable (fun i : Fin n → ℕ => ‖∏ k, x k ^ i k‖) := by
  induction n with
  | zero =>
    intro x _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
    exact ⟨hasSum_unique (fun _ : Fin 0 → ℕ => (1 : ℂ)),
      (hasSum_unique (fun _ : Fin 0 → ℕ => (1 : ℝ))).summable⟩
  | succ n ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih (fun k => x k.succ) fun k => hx _
    have hg := hasSum_geometric_of_norm_lt_one (hx 0)
    have hgn : Summable fun a : ℕ => ‖x 0 ^ a‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hx 0)
    have hprod := hg.mul h1 (summable_mul_of_summable_norm (f := fun a : ℕ => x 0 ^ a)
      (g := fun i : Fin n → ℕ => ∏ k : Fin n, x k.succ ^ i k) hgn h2)
    set e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    have hfe : ∀ p : ℕ × (Fin n → ℕ), ∏ k, x k ^ (e p) k = x 0 ^ p.1 * ∏ k : Fin n, x k.succ ^ p.2 k :=
      fun p => by
        rw [Fin.prod_univ_succ]
        simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rw [Fin.prod_univ_succ, ← e.hasSum_iff]
      exact hprod.congr_fun fun p => by rw [Function.comp_apply, hfe]
    · rw [← e.summable_iff]
      refine (summable_mul_of_summable_norm (f := fun a : ℕ => ‖x 0 ^ a‖)
        (g := fun b : Fin n → ℕ => ‖∏ k : Fin n, x k.succ ^ b k‖) (by simpa using hgn)
        (by simpa using h2)).congr fun p => ?_
      rw [Function.comp_apply, hfe, norm_mul]

theorem hasSum_prod_geom {S : Type*} [Fintype S] (x : S → ℂ) (hx : ∀ v, ‖x v‖ < 1) :
    HasSum (fun i : S → ℕ => ∏ v, x v ^ i v) (∏ v, (1 - x v)⁻¹) ∧
      Summable (fun i : S → ℕ => ‖∏ v, x v ^ i v‖) := by
  set σ := Fintype.equivFin S
  obtain ⟨h1, h2⟩ := hasSum_prod_fin_geom (Fintype.card S) (fun k => x (σ.symm k)) fun k => hx _
  set E : (Fin (Fintype.card S) → ℕ) ≃ (S → ℕ) := Equiv.arrowCongr σ.symm (Equiv.refl ℕ)
  have hE : ∀ i : Fin (Fintype.card S) → ℕ, ∏ v, x v ^ (E i) v = ∏ k, x (σ.symm k) ^ i k := by
    intro i
    rw [← σ.symm.prod_comp]
    simp [E, Equiv.arrowCongr]
  have hP : ∏ v, (1 - x v)⁻¹ = ∏ k, (1 - x (σ.symm k))⁻¹ := (σ.symm.prod_comp _).symm
  constructor
  · rw [← E.hasSum_iff, hP]
    exact h1.congr_fun fun i => by simp only [Function.comp_apply, hE]
  · rw [← E.summable_iff]
    exact h2.congr fun i => by simp only [Function.comp_apply, hE]

/-! ### The weight `Om` -/

section Om

variable {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)

/-- `log q_v`. -/
noncomputable def lq (v : S) : ℝ := Real.log (q v)

/-- `NN j = ∏ q_v^{j_v} = exp (Σ j_v log q_v)`. -/
noncomputable def NN (j : S → ℤ) : ℝ := Real.exp (∑ v, (j v : ℝ) * lq q v)

/-- `NN j ^ w`, as `exp (w Σ j_v log q_v)`. -/
noncomputable def Ncp (j : S → ℤ) (w : ℂ) : ℂ := Complex.exp (w * ∑ v, ((j v : ℝ) * lq q v : ℝ))

/-- The indicator vector of `e ⊆ S`. -/
def indE (e : Finset S) : S → ℤ := fun v => if v ∈ e then 1 else 0

/-- The dual weight `Om j = Σ_{e ⊆ S} (−1)^{|e|} 1[j + 1_e ≥ 0] / NN (j + 1_e)`. -/
noncomputable def Om (j : S → ℤ) : ℝ :=
  ∑ e : Finset S, (-1 : ℝ) ^ e.card * (if 0 ≤ j + indE e then (NN q (j + indE e))⁻¹ else 0)

/-- The local factor `W(z) = ∏_v (1 − q_v^{z−1}) / (1 − q_v^{−z})`. -/
noncomputable def Wf (z : ℂ) : ℂ :=
  (∏ v, (1 - Complex.exp ((z - 1) * lq q v))) * ∏ v, (1 - Complex.exp (-z * lq q v))⁻¹

theorem NN_pos (j : S → ℤ) : 0 < NN q j := Real.exp_pos _

theorem Ncp_add (j j' : S → ℤ) (w : ℂ) : Ncp q (j + j') w = Ncp q j w * Ncp q j' w := by
  simp only [Ncp, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add,
    mul_add, Complex.exp_add]

theorem Ncp_neg_one (j : S → ℤ) : Ncp q j (-1) = ((NN q j)⁻¹ : ℝ) := by
  rw [Ncp, NN, ← Real.exp_neg, Complex.ofReal_exp]
  congr 1; push_cast; ring

theorem Ncp_mul (j : S → ℤ) (w w' : ℂ) : Ncp q j (w + w') = Ncp q j w * Ncp q j w' := by
  simp only [Ncp, add_mul, Complex.exp_add]

theorem Ncp_nat (i : S → ℕ) (w : ℂ) :
    Ncp q (fun v => (i v : ℤ)) w = ∏ v, Complex.exp (w * lq q v) ^ i v := by
  rw [Ncp, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

variable (hq : ∀ v, 1 < q v)
include hq

theorem lq_pos (v : S) : 0 < lq q v := Real.log_pos (hq v)

/-- `Σ_{i ≥ 0} NN i ^ {−z} = ∏_v (1 − q_v^{−z})⁻¹` for `Re z > 0`. -/
theorem hasSum_Ncp_nonneg (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun i : S → ℤ => if 0 ≤ i then Ncp q i (-z) else 0)
      (∏ v, (1 - Complex.exp (-z * lq q v))⁻¹) ∧
    Summable (fun i : S → ℤ => ‖if 0 ≤ i then Ncp q i (-z) else 0‖) := by
  have hx : ∀ v, ‖Complex.exp (-z * lq q v)‖ < 1 := fun v => by
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Real.exp_lt_one_iff]
    nlinarith [lq_pos q hq v]
  obtain ⟨h1, h2⟩ := hasSum_prod_geom _ hx
  set g : (S → ℕ) → (S → ℤ) := fun i v => (i v : ℤ)
  have hg : Function.Injective g := fun a b h => funext fun v => by
    have := congrFun h v; simp only [g] at this; exact_mod_cast this
  have hzero : ∀ i ∉ Set.range g, (if 0 ≤ i then Ncp q i (-z) else 0) = 0 := by
    intro i hi
    rw [if_neg]
    intro h0
    exact hi ⟨fun v => (i v).toNat, funext fun v => by simp [g, Int.toNat_of_nonneg (h0 v)]⟩
  have hcomp : ∀ i : S → ℕ, (if 0 ≤ g i then Ncp q (g i) (-z) else 0) = ∏ v, Complex.exp (-z * lq q v) ^ i v := by
    intro i
    have h0 : (0 : S → ℤ) ≤ g i := fun v => by simp [g]
    rw [if_pos h0]
    exact Ncp_nat q i (-z)
  constructor
  · rw [← hg.hasSum_iff hzero]
    exact h1.congr_fun fun i => by simp only [Function.comp_apply, hcomp]
  · have hzero' : ∀ i ∉ Set.range g, ‖if 0 ≤ i then Ncp q i (-z) else 0‖ = 0 := fun i hi => by
      rw [hzero i hi, norm_zero]
    rw [← hg.summable_iff hzero']
    exact h2.congr fun i => by simp only [Function.comp_apply, hcomp]

/-- One inclusion–exclusion term of `Om j · NN j^{1−z}`. -/
noncomputable def Tm (z : ℂ) (e : Finset S) (j : S → ℤ) : ℂ :=
  (-1 : ℂ) ^ e.card * (if 0 ≤ j + indE e then Ncp q (j + indE e) (-1) * Ncp q j (1 - z) else 0)

omit hq in
theorem Om_mul_Ncp (z : ℂ) (j : S → ℤ) :
    (Om q j : ℂ) * Ncp q j (1 - z) = ∑ e : Finset S, Tm q z e j := by
  rw [Om, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Tm]
  split_ifs with h
  · rw [Ncp_neg_one]; push_cast; ring
  · push_cast; ring

omit hq in
theorem Tm_shift (z : ℂ) (e : Finset S) (i : S → ℤ) :
    Tm q z e (i - indE e) = ((-1 : ℂ) ^ e.card * Ncp q (-indE e) (1 - z)) *
      (if 0 ≤ i then Ncp q i (-z) else 0) := by
  rw [Tm, sub_add_cancel]
  split_ifs with h
  · rw [sub_eq_add_neg, Ncp_add, show -z = -1 + (1 - z) by ring, Ncp_mul]
    ring
  · ring

omit hq in
theorem Ncp_neg_indE (z : ℂ) (e : Finset S) :
    Ncp q (-indE e) (1 - z) = ∏ v ∈ e, Complex.exp ((z - 1) * lq q v) := by
  rw [Ncp, ← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ e)]
  · refine Finset.sum_congr rfl fun v hv => ?_
    simp only [indE, Pi.neg_apply, if_pos hv]
    push_cast; ring
  · intro v _ hv
    simp only [indE, Pi.neg_apply, if_neg hv]
    simp

theorem hasSum_Tm (z : ℂ) (hz : 0 < z.re) (e : Finset S) :
    HasSum (Tm q z e) (((-1 : ℂ) ^ e.card * ∏ v ∈ e, Complex.exp ((z - 1) * lq q v)) *
        ∏ v, (1 - Complex.exp (-z * lq q v))⁻¹) ∧
      Summable fun j => ‖Tm q z e j‖ := by
  obtain ⟨h1, h2⟩ := hasSum_Ncp_nonneg q hq z hz
  set E := Equiv.subRight (indE e : S → ℤ)
  constructor
  · rw [← E.hasSum_iff, ← Ncp_neg_indE]
    refine (h1.mul_left ((-1 : ℂ) ^ e.card * Ncp q (-indE e) (1 - z))).congr_fun fun i => ?_
    rw [Function.comp_apply, Equiv.subRight_apply, Tm_shift]
  · rw [← E.summable_iff]
    refine (h2.mul_left ‖(-1 : ℂ) ^ e.card * Ncp q (-indE e) (1 - z)‖).congr fun i => ?_
    rw [Function.comp_apply, Equiv.subRight_apply, Tm_shift]
    simp only [norm_mul]

omit hq in
theorem sum_neg_one_pow_prod (c : S → ℂ) :
    ∑ e : Finset S, (-1 : ℂ) ^ e.card * ∏ v ∈ e, c v = ∏ v, (1 - c v) := by
  have := Finset.prod_add (fun v => -c v) (fun _ => (1 : ℂ)) (Finset.univ : Finset S)
  rw [Finset.powerset_univ] at this
  simp only [Finset.prod_const_one, mul_one] at this
  rw [show (∏ v, (1 - c v)) = ∏ v, (-c v + 1) from Finset.prod_congr rfl fun v _ => by ring, this]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.prod_neg]

/-- `Σ_j Om j · NN j^{1−z} = W(z)` for `Re z > 0`, absolutely. -/
theorem hasSum_Om (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun j => (Om q j : ℂ) * Ncp q j (1 - z)) (Wf q z) ∧
      Summable fun j => ‖(Om q j : ℂ) * Ncp q j (1 - z)‖ := by
  have hT := fun e => hasSum_Tm q hq z hz e
  constructor
  · have := hasSum_sum (s := Finset.univ) fun e _ => (hT e).1
    rw [← Finset.sum_mul, sum_neg_one_pow_prod] at this
    refine this.congr_fun fun j => ?_
    rw [Om_mul_Ncp]
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      (summable_sum (s := Finset.univ) fun e _ => (hT e).2)
    rw [Om_mul_Ncp]
    exact norm_sum_le _ _

theorem norm_exp_mul_lq_lt_one {w : ℂ} (hw : w.re < 0) (v : S) :
    ‖Complex.exp (w * lq q v)‖ < 1 := by
  rw [Complex.norm_exp, Complex.re_mul_ofReal, Real.exp_lt_one_iff]
  nlinarith [lq_pos q hq v]

theorem one_sub_exp_ne_zero {w : ℂ} (hw : w.re < 0) (v : S) :
    1 - Complex.exp (w * lq q v) ≠ 0 := fun h => by
  have := norm_exp_mul_lq_lt_one q hq hw v
  rw [← sub_eq_zero.1 h, norm_one] at this
  exact lt_irrefl _ this

theorem differentiableOn_Wf : DifferentiableOn ℂ (Wf q) {z | 0 < z.re} := by
  intro z hz
  have hz' : (-z).re < 0 := by rw [Complex.neg_re]; linarith [show 0 < z.re from hz]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.mul ?_ ?_
  · exact DifferentiableAt.fun_finsetProd fun v _ =>
      (differentiableAt_const _).sub ((differentiableAt_id.sub_const 1).mul_const _).cexp
  · refine DifferentiableAt.fun_finsetProd fun v _ => ?_
    refine DifferentiableAt.inv ((differentiableAt_const _).sub (differentiableAt_id.neg.mul_const _).cexp)
      (one_sub_exp_ne_zero q hq hz' v)

theorem norm_Wf_le {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Wf q z‖ ≤ C := by
  refine ⟨(∏ v : S, (1 + Real.exp ((b - 1) * lq q v))) * ∏ v : S, (1 - Real.exp (-a * lq q v))⁻¹,
    fun z h1 h2 => ?_⟩
  rw [Wf, norm_mul, norm_prod, norm_prod]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun v _ => by linarith [Real.exp_pos ((b - 1) * lq q v)])
  · refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, Complex.norm_exp, Complex.re_mul_ofReal, Complex.sub_re, Complex.one_re]
    gcongr
    exact (lq_pos q hq v).le
  · refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
    have hlt : Real.exp (-a * lq q v) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [lq_pos q hq v]
    rw [norm_inv]
    refine inv_anti₀ (by linarith) ?_
    calc 1 - Real.exp (-a * lq q v) ≤ 1 - ‖Complex.exp (-z * lq q v)‖ := by
          rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
          gcongr
          nlinarith [lq_pos q hq v]
      _ ≤ ‖1 - Complex.exp (-z * lq q v)‖ := by
          have := norm_sub_norm_le (1 : ℂ) (Complex.exp (-z * lq q v))
          rwa [norm_one] at this

theorem Wf_ne_zero {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) : Wf q z ≠ 0 := by
  rw [Wf]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    (Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero ?_)
  · exact one_sub_exp_ne_zero q hq (w := z - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith) v
  · exact one_sub_exp_ne_zero q hq (w := -z) (by rw [Complex.neg_re]; linarith) v

end Om

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-- `count_v (x)`. -/
noncomputable def ordv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℤ :=
  FractionalIdeal.count F v (spanSingleton (𝓞 F)⁰ x)

theorem spanSingleton_ne_zero {x : F} (hx : x ≠ 0) : spanSingleton (𝓞 F)⁰ x ≠ 0 :=
  (spanSingleton_eq_zero_iff).not.2 hx

theorem ordv_algebraMap (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F} (hr : r ≠ 0) :
    ordv v (algebraMap (𝓞 F) F r) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors : ℤ) := by
  rw [ordv, ← coeIdeal_span_singleton, count_coe F v]
  rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]

theorem ordv_mul (v : HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordv v (x * y) = ordv v x + ordv v y := by
  rw [ordv, ← spanSingleton_mul_spanSingleton, count_mul F v (spanSingleton_ne_zero hx)
    (spanSingleton_ne_zero hy)]
  rfl

theorem ordv_inv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ordv v x⁻¹ = -ordv v x := by
  rw [ordv, ← spanSingleton_inv, count_inv]; rfl

theorem ordv_one (v : HeightOneSpectrum (𝓞 F)) : ordv v (1 : F) = 0 := by
  rw [ordv, spanSingleton_one, count_one]

theorem valuation_eq_exp_neg_ordv (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x = WithZero.exp (-ordv v x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl; simp at hx
  have hrK : algebraMap (𝓞 F) F r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  rw [div_eq_mul_inv, map_mul, map_inv₀, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_if_neg _ hr0, intValuation_if_neg _ hs0, ordv_mul v hrK (inv_ne_zero hsK),
    ordv_inv, ordv_algebraMap v hr0, ordv_algebraMap v hs0, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr 1; ring

theorem valuation_le_one_iff (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x ≤ 1 ↔ 0 ≤ ordv v x := by
  rw [valuation_eq_exp_neg_ordv v hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- For nonzero fractional ideals, `I ≤ J ↔ ∀ v, count_v J ≤ count_v I`. -/
theorem le_iff_count {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 F), count F v J ≤ count F v I := by
  constructor
  · intro h v; exact count_mono F v hI h
  · intro h
    set K := I * J⁻¹
    have hK : K ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
    have hcount : ∀ v, 0 ≤ count F v K := fun v => by
      rw [count_mul F v hI (inv_ne_zero hJ), count_inv]; linarith [h v]
    have hpow : ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v K =
        coeIdealHom (𝓞 F)⁰ F (v.asIdeal ^ (count F v K).toNat) := fun v => by
      rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hcount v)]; rfl
    have hKle : K ≤ 1 := by
      rw [← finprod_heightOneSpectrum_factorization' F hK]
      simp_rw [hpow]
      have e := MonoidHom.map_finprod_of_injective (coeIdealHom (𝓞 F)⁰ F).toMonoidHom
        coeIdeal_injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ (count F v K).toNat)
      calc _ = (coeIdealHom (𝓞 F)⁰ F) (∏ᶠ v : HeightOneSpectrum (𝓞 F),
            v.asIdeal ^ (count F v K).toNat) := e.symm
        _ ≤ 1 := coeIdeal_le_one
    have : I = K * J := by
      simp only [K]; rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    rw [this]
    calc K * J ≤ 1 * J := mul_le_mul_left hKle J
      _ = J := one_mul J

theorem eq_of_count_eq {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), count F v I = count F v J) : I = J :=
  le_antisymm ((le_iff_count hI hJ).2 fun v => (h v).ge) ((le_iff_count hJ hI).2 fun v => (h v).le)

theorem mem_iff_count {x : F} (hx : x ≠ 0) {J : FractionalIdeal (𝓞 F)⁰ F} (hJ : J ≠ 0) :
    x ∈ J ↔ ∀ v : HeightOneSpectrum (𝓞 F), count F v J ≤ ordv v x := by
  rw [← spanSingleton_le_iff_mem, le_iff_count (spanSingleton_ne_zero hx) hJ]; rfl

theorem ordv_add_ge (v : HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (ordv v x) (ordv v y) ≤ ordv v (x + y) := by
  have h := Valuation.map_add (v.valuation F) x y
  rw [valuation_eq_exp_neg_ordv v hx, valuation_eq_exp_neg_ordv v hy,
    valuation_eq_exp_neg_ordv v hxy] at h
  rcases le_total (ordv v x) (ordv v y) with hle | hle
  · rw [min_eq_left hle]
    rw [max_eq_left (WithZero.exp_le_exp.2 (neg_le_neg hle))] at h
    have := WithZero.exp_le_exp.1 h; linarith
  · rw [min_eq_right hle]
    rw [max_eq_right (WithZero.exp_le_exp.2 (neg_le_neg hle))] at h
    have := WithZero.exp_le_exp.1 h; linarith

/-- In a nonzero fractional ideal, the count is attained. -/
theorem exists_mem_ordv_eq {J : FractionalIdeal (𝓞 F)⁰ F} (hJ : J ≠ 0)
    (w : HeightOneSpectrum (𝓞 F)) : ∃ x ∈ J, x ≠ 0 ∧ ordv w x = count F w J := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 w.ne_bot
  have hJw : J * w.asIdeal ≠ 0 := mul_ne_zero hJ hw0
  have hne : ¬ J ≤ J * w.asIdeal := by
    intro h
    have := count_mono F w hJ h
    rw [count_mul F w hJ hw0, count_self] at this
    linarith
  rw [SetLike.not_le_iff_exists] at hne
  obtain ⟨x, hxJ, hxJw⟩ := hne
  have hx0 : x ≠ 0 := by rintro rfl; exact hxJw (zero_mem _)
  refine ⟨x, hxJ, hx0, le_antisymm ?_ (((mem_iff_count hx0 hJ).1 hxJ) w)⟩
  by_contra hlt
  push Not at hlt
  apply hxJw
  rw [mem_iff_count hx0 hJw]
  intro v
  rw [count_mul F v hJ hw0, count_maximal]
  split_ifs with hvw
  · subst hvw; linarith
  · rw [add_zero]; exact (mem_iff_count hx0 hJ).1 hxJ v

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

/-- The finite places of `S`, as a type. -/
abbrev SP (𝔪 : Ideal (𝓞 F)) : Type _ := ↥(placesOf 𝔪)

theorem mem_SInt_iff {x : F} (hx : x ≠ 0) :
    x ∈ (placesOf 𝔪).integer F ↔ ∀ v ∉ placesOf 𝔪, 0 ≤ ordv v x := by
  change (∀ v ∉ placesOf 𝔪, v.valuation F x ≤ 1) ↔ _
  simp only [valuation_le_one_iff _ hx]

/-- The prime `v` as a unit fractional ideal. -/
noncomputable def primeU (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) (coeIdeal_ne_zero.2 v.ne_bot)

/-- The valuation vector at `S`. -/
noncomputable def valS (x : F) : SP 𝔪 → ℤ := fun v => ordv v.1 x

variable [Fintype (SP 𝔪)]

/-- `P^k = ∏_{v ∈ S} 𝔭_v^{k_v}`. -/
noncomputable def Pk (k : SP 𝔪 → ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := ∏ v : SP 𝔪, primeU v.1 ^ k v

theorem coe_Pk (k : SP 𝔪 → ℤ) :
    ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ v : SP 𝔪, (v.1.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ k v := by
  rw [Pk, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem Pk_ne_zero (k : SP 𝔪 → ℤ) :
    ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := (Pk k).ne_zero

theorem count_Pk (k : SP 𝔪 → ℤ) (w : HeightOneSpectrum (𝓞 F)) :
    count F w ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      if h : w ∈ placesOf 𝔪 then k ⟨w, h⟩ else 0 := by
  rw [coe_Pk, count_prod F w _ _ fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.2 v.1.ne_bot)]
  simp_rw [count_zpow, count_maximal]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨w, h⟩]
    · simp
    · intro v _ hv
      have : v.1 ≠ w := fun e => hv (Subtype.ext e)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun v _ => ?_
    have : v.1 ≠ w := fun e => h (e ▸ v.2)
    simp [this]

theorem Pk_add (k k' : SP 𝔪 → ℤ) : Pk (k + k') = Pk k * Pk k' := by
  rw [Pk, Pk, Pk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.add_apply, zpow_add]

theorem Pk_neg (k : SP 𝔪 → ℤ) : Pk (-k) = (Pk k)⁻¹ := by
  rw [Pk, Pk, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.neg_apply, zpow_neg]

theorem Pk_zero : Pk (0 : SP 𝔪 → ℤ) = 1 := by simp [Pk]

/-- Membership in `P^k`: `x ∈ P^k ↔ x ∈ R ∧ k ≤ val_S x`. -/
theorem mem_Pk_iff {x : F} (hx : x ≠ 0) (k : SP 𝔪 → ℤ) :
    x ∈ ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ↔
      x ∈ (placesOf 𝔪).integer F ∧ k ≤ valS x := by
  rw [mem_iff_count hx (Pk_ne_zero k), mem_SInt_iff hx]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have := h v; rwa [count_Pk, dif_neg hv] at this
    · have := h v.1; rwa [count_Pk, dif_pos v.2] at this
  · rintro ⟨h1, h2⟩ v
    rw [count_Pk]
    split_ifs with hv
    · exact h2 ⟨v, hv⟩
    · exact h1 v hv

theorem Pk_subset_SInt (k : SP 𝔪 → ℤ) {x : F}
    (hx : x ∈ ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
    x ∈ (placesOf 𝔪).integer F := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_mem _
  · exact ((mem_Pk_iff h0 k).1 hx).1

omit [Fintype (SP 𝔪)] in
/-- Elements of `𝔟 R` have `w`-adic order at least `count_w 𝔟` outside `S`. -/
theorem ordv_ge_of_mem_map (𝔟 : Ideal (𝓞 F)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ placesOf 𝔪)
    {y : SInt 𝔪} (hy : y ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) (hy0 : (y : F) ≠ 0) :
    count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ ordv w (y : F) := by
  suffices h : ∀ y ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪)), (y : F) = 0 ∨
      count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ ordv w (y : F) from (h y hy).resolve_left hy0
  intro y hy
  rw [Ideal.map, Ideal.span] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    by_cases hb0 : b = 0
    · left; simp [hb0]
    · right
      have hbK : algebraMap (𝓞 F) F b ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      have h1 : spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F b) ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [spanSingleton_le_iff_mem]; exact mem_coeIdeal_of_mem _ hb
      have h2 := count_mono F w (spanSingleton_ne_zero hbK) h1
      exact h2
  | zero => left; rfl
  | add x y _ _ hx hy =>
    by_cases hx0 : (x : F) = 0
    · have : ((x + y : SInt 𝔪) : F) = (y : F) := by simp [hx0]
      rw [this]; exact hy
    by_cases hy0 : (y : F) = 0
    · have : ((x + y : SInt 𝔪) : F) = (x : F) := by simp [hy0]
      rw [this]; exact hx
    by_cases hxy : ((x + y : SInt 𝔪) : F) = 0
    · left; exact hxy
    right
    have h1 := hx.resolve_left hx0
    have h2 := hy.resolve_left hy0
    have hxy' : (x : F) + (y : F) ≠ 0 := by simpa using hxy
    have := ordv_add_ge w hx0 hy0 hxy'
    simp only [Subalgebra.coe_add]
    exact (le_min h1 h2).trans this
  | smul r x _ hx =>
    by_cases h0 : ((r • x : SInt 𝔪) : F) = 0
    · left; exact h0
    right
    have hrx : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [hrx] at h0 ⊢
    have hr0 : (r : F) ≠ 0 := left_ne_zero_of_mul h0
    have hx0 : (x : F) ≠ 0 := right_ne_zero_of_mul h0
    rw [ordv_mul w hr0 hx0]
    have hr : 0 ≤ ordv w (r : F) := (mem_SInt_iff hr0).1 r.2 w hw
    linarith [hx.resolve_left hx0]

omit [Fintype (SP 𝔪)] in
theorem count_eq_zero_of_exterior {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ placesOf 𝔪) : count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
  rw [count_coe F w h𝔟.1, Nat.cast_eq_zero]
  by_contra hc
  have hdvd := (Associates.count_ne_zero_iff_dvd h𝔟.1 w.irreducible).1 hc
  have h1 : 𝔟 ≤ w.asIdeal := Ideal.le_of_dvd hdvd
  have h2 : 𝔟 ⊔ 𝔪 ≤ w.asIdeal := sup_le h1 hw
  rw [h𝔟.2, top_le_iff] at h2
  exact w.isPrime.ne_top h2

omit [Fintype (SP 𝔪)] in
theorem ne_zero_of_span_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) : (m : F) ≠ 0 := by
  intro h0
  have hm0 : m = 0 := Subtype.ext h0
  rw [hm0, Ideal.span_singleton_eq_bot.2 rfl] at hm
  apply h𝔟.1
  rw [eq_bot_iff]
  intro b hb
  have : algebraMap (𝓞 F) (SInt 𝔪) b ∈ (⊥ : Ideal (SInt 𝔪)) := hm ▸ Ideal.mem_map_of_mem _ hb
  rw [Ideal.mem_bot] at this
  have h2 : algebraMap (𝓞 F) F b = 0 := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) this
    simpa using this
  rw [Ideal.mem_bot]
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2

/-- `m R = 𝔟 R` with `𝔟` exterior gives `(m) = 𝔟 · P^{val_S m}` as fractional ideals of `𝓞`. -/
theorem spanSingleton_eq_mul_Pk {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    spanSingleton (𝓞 F)⁰ (m : F) =
      (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((Pk (valS (𝔪 := 𝔪) (m : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
  have hm0 := ne_zero_of_span_eq h𝔟 hm
  have h𝔟0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔟.1
  refine eq_of_count_eq (spanSingleton_ne_zero hm0) (mul_ne_zero h𝔟0 (Pk_ne_zero _)) fun w => ?_
  rw [count_mul F w h𝔟0 (Pk_ne_zero _), count_Pk]
  change ordv w (m : F) = _
  split_ifs with hw
  · rw [count_eq_zero_of_exterior h𝔟 hw, zero_add]; rfl
  · rw [add_zero]
    refine le_antisymm ?_ (ordv_ge_of_mem_map 𝔟 hw (hm ▸ Ideal.mem_span_singleton_self m) hm0)
    obtain ⟨x, hx, hx0, hxo⟩ := exists_mem_ordv_eq h𝔟0 w
    obtain ⟨b, hb, rfl⟩ := (mem_coeIdeal _).1 hx
    have hbm : algebraMap (𝓞 F) (SInt 𝔪) b ∈ Ideal.span {m} := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hbm
    have hrF : (r : F) * (m : F) = algebraMap (𝓞 F) F b := by
      have := congrArg (fun z : SInt 𝔪 => (z : F)) hr
      simpa using this
    have hr0 : (r : F) ≠ 0 := by
      intro h; rw [h, zero_mul] at hrF; exact hx0 hrF.symm
    rw [← hxo, ← hrF, ordv_mul w hr0 hm0]
    have := (mem_SInt_iff hr0).1 r.2 w hw
    linarith

/-- `q_v = N 𝔭_v`. -/
noncomputable def qS (v : SP 𝔪) : ℝ := (Ideal.absNorm v.1.asIdeal : ℝ)

omit [Fintype (SP 𝔪)] in
theorem one_lt_qS (v : SP 𝔪) : 1 < qS v := by
  rw [qS]
  have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
  have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by
    rw [ne_eq, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.1.asIdeal := by omega
  exact_mod_cast this

theorem NN_eq_prod {S : Type*} [Fintype S] (q : S → ℝ) (hq : ∀ v, 0 < q v) (k : S → ℤ) :
    NN q k = ∏ v, q v ^ k v := by
  rw [NN, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [lq, mul_comm, ← Real.rpow_intCast, Real.rpow_def_of_pos (hq v)]

theorem absNorm_Pk (k : SP 𝔪 → ℤ) :
    ((FractionalIdeal.absNorm ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) = NN (qS (𝔪 := 𝔪)) k := by
  rw [coe_Pk, map_prod, NN_eq_prod qS (fun v => (one_lt_qS v).trans' one_pos)]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, coeIdeal_absNorm]
  push_cast; rfl

/-- `|N m| = N 𝔟 · N(P^{val_S m})`. -/
theorem abs_norm_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (m : F)) := by
  rw [← absNorm_span_singleton (R := 𝓞 F), spanSingleton_eq_mul_Pk h𝔟 hm, map_mul,
    coeIdeal_absNorm, Rat.cast_mul, absNorm_Pk]
  push_cast; rfl

/-! ### Units, the different, and the trace dual -/

theorem valS_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    valS (𝔪 := 𝔪) (x * y) = valS x + valS y := funext fun v => ordv_mul v.1 hx hy

theorem isExterior_top : IsExterior 𝔪 (⊤ : Ideal (𝓞 F)) := ⟨top_ne_bot, top_sup_eq _⟩

theorem spanSingleton_unit (ε : (SInt 𝔪)ˣ) :
    spanSingleton (𝓞 F)⁰ ((ε : SInt 𝔪) : F) =
      ((Pk (valS (𝔪 := 𝔪) ((ε : SInt 𝔪) : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
  have h : Ideal.span {(ε : SInt 𝔪)} = (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_top, Ideal.span_singleton_eq_top]; exact ε.isUnit
  rw [spanSingleton_eq_mul_Pk isExterior_top h, coeIdeal_top, one_mul]

theorem unit_ne_zero (ε : (SInt 𝔪)ˣ) : ((ε : SInt 𝔪) : F) ≠ 0 := by
  intro h; exact ε.ne_zero (Subtype.ext h)

theorem abs_norm_unit (ε : (SInt 𝔪)ˣ) :
    ((|Algebra.norm ℚ ((ε : SInt 𝔪) : F)| : ℚ) : ℝ) = NN (qS (𝔪 := 𝔪)) (valS ((ε : SInt 𝔪) : F)) := by
  rw [← absNorm_span_singleton (R := 𝓞 F), spanSingleton_unit, absNorm_Pk]

/-- The different is supported on `S`. -/
def DiffInS (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ∣ differentIdeal ℤ (𝓞 F) → w ∈ placesOf 𝔪

/-- The exponent vector of the different. -/
noncomputable def delta : SP 𝔪 → ℤ := fun v =>
  count F v.1 ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)

theorem differentIdeal_ne_bot : differentIdeal ℤ (𝓞 F) ≠ ⊥ := by
  intro h
  have := absNorm_differentIdeal (K := F) (𝒪 := 𝓞 F)
  rw [h, Ideal.absNorm_bot] at this
  exact (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero F)) this.symm

theorem coe_different_eq_Pk (h : DiffInS 𝔪) :
    ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      ((Pk (delta (𝔪 := 𝔪)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
  have h0 : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    coeIdeal_ne_zero.2 differentIdeal_ne_bot
  refine eq_of_count_eq h0 (Pk_ne_zero _) fun w => ?_
  rw [count_Pk]
  split_ifs with hw
  · rfl
  · rw [count_coe F w differentIdeal_ne_bot, Nat.cast_eq_zero]
    by_contra hc
    exact hw (h w ((Associates.count_ne_zero_iff_dvd differentIdeal_ne_bot w.irreducible).1 hc))

theorem NN_delta (h : DiffInS 𝔪) : NN (qS (𝔪 := 𝔪)) delta = |(discr F : ℝ)| := by
  rw [← absNorm_Pk, ← coe_different_eq_Pk h, coeIdeal_absNorm, absNorm_differentIdeal F (𝓞 F)]
  push_cast
  rw [Nat.cast_natAbs]
  push_cast; rfl

/-- The trace dual of `𝔫 P^k`, through a generator `ν` of `𝔫 R`. -/
theorem mem_dual_iff (h : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (k : SP 𝔪 → ℤ) (η : F) :
    η ∈ FractionalIdeal.dual ℤ ℚ ((𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
        ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) ↔
      (ν : F) * η ∈ ((Pk (valS (ν : F) - k - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  have h𝔫0 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔫.1
  have hspan := spanSingleton_eq_mul_Pk h𝔫 hν
  have hPinv : ∀ k : SP 𝔪 → ℤ, ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F)⁻¹ = ((Pk (-k) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) := fun k => by
    rw [← Units.val_inv_eq_inv_val, Pk_neg]
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) =
      ((Pk (-delta (𝔪 := 𝔪)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    have := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
    rw [coe_different_eq_Pk h] at this
    rw [← hPinv, this, inv_inv]
  have h𝔫 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) = spanSingleton (𝓞 F)⁰ (ν : F) *
      ((Pk (-valS (𝔪 := 𝔪) (ν : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hspan, mul_assoc, ← Units.val_mul, ← Pk_add, add_neg_cancel, Pk_zero, Units.val_one,
      mul_one]
  have hdual : FractionalIdeal.dual ℤ ℚ ((𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) =
      spanSingleton (𝓞 F)⁰ ((ν : F)⁻¹) *
        ((Pk (valS (ν : F) - k - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
          FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.dual_eq_mul_inv, hd1, h𝔫, mul_assoc, ← Units.val_mul, ← Pk_add, mul_inv,
      spanSingleton_inv, hPinv]
    rw [show valS (𝔪 := 𝔪) (ν : F) - k - delta = -delta + -(-valS (ν : F) + k) by ring, Pk_add,
      Units.val_mul, ← hPinv (-valS (ν : F) + k)]
    ring
  rw [hdual, mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, mul_inv_cancel₀ hν0, one_mul]
  · intro hη
    exact ⟨(ν : F) * η, hη, by rw [← mul_assoc, inv_mul_cancel₀ hν0, one_mul]⟩

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

lemma le_of_mul_le_mul_ne {a b c : ℤᵐ⁰} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  have := mul_le_mul_right h c⁻¹
  rwa [mul_comm c⁻¹, mul_comm c⁻¹, mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at this

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `x` has a witness in the definition of `sAddChar`. -/
def HasWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1

lemma hasWit_of_mem {x : F} (hx : x ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x :=
  ⟨0, by simpa using hx, fun v _ => by simp⟩

/-- The value of `e` through any witness. -/
lemma sAddChar_eq_of_wit {x y : F} (h1 : x - y ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) :
    sAddChar 𝔪 x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 := ⟨y, h1, h2⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  set y' := hex.choose
  have hd : y' - y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem h1 k1
    rwa [show x - y - (x - y') = y' - y by ring] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y' - y) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact (Valuation.map_sub _ _ _).trans (max_le (k2 v hv) (h2 v hv))
    · exact hd v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  have htr : Algebra.trace ℚ F y' = Algebra.trace ℚ F y + ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [Algebra.coe_trace_int, show ((z : 𝓞 F) : F) = algebraMap (𝓞 F) F z from rfl, hz, map_sub]
    ring
  rw [htr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℂ) =
      ((-(Algebra.trace ℤ (𝓞 F) z) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring, this,
    mul_one]

/-- `e` is additive on elements with witnesses. -/
lemma sAddChar_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') :
    sAddChar 𝔪 (x + x') = sAddChar 𝔪 x * sAddChar 𝔪 x' := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  have hs1 : x + x' - (y + y') ∈ (placesOf 𝔪).integer F := by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1'
  have hs2 : ∀ v ∈ placesOf 𝔪, v.valuation F (y + y') ≤ 1 :=
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))
  rw [sAddChar_eq_of_wit hs1 hs2, sAddChar_eq_of_wit hy1 hy2, sAddChar_eq_of_wit hy1' hy2',
    ← Complex.exp_add, map_add]
  push_cast
  ring_nf

/-- A witness exists when `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
lemma hasWit_of_mul_mem (x : F) (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤)
    (hx : ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨i, hi, w, hw, hiw⟩ := hcop.exists
  refine ⟨x * algebraMap (𝓞 F) F w, ?_, fun v hv => ?_⟩
  · have hw' : algebraMap (𝓞 F) F w = 1 - algebraMap (𝓞 F) F i := by
      rw [← map_one (algebraMap (𝓞 F) F), ← hiw, map_add]; ring
    have : x - x * algebraMap (𝓞 F) F w = x * algebraMap (𝓞 F) F i := by
      rw [hw']; ring
    rw [this]; exact hx i hi
  · have hvm : 𝔪 ≤ v.asIdeal := hv
    -- `d ∉ v^N`
    have hdN : d ∉ v.asIdeal ^ N := by
      intro hmem
      have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
      have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [map_pow] at hdvd
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
      have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
        have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
        have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
        omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
      have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
      have h4 : N < 2 ^ N := Nat.lt_two_pow_self
      omega
    have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
    have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
      rw [val_alg, v.intValuation_le_pow_iff_mem]
      exact Ideal.pow_right_mono hvm N hw
    have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
    have hxd : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
      rw [← hbd, div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    have key : v.valuation F (x * algebraMap (𝓞 F) F w) * v.valuation F (algebraMap (𝓞 F) F d) ≤
        1 * v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [← map_mul, show x * algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [← hxd]; ring, map_mul]
      calc v.valuation F (algebraMap (𝓞 F) F b) * v.valuation F (algebraMap (𝓞 F) F w)
          ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) :=
            mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
        _ = _ := rfl
    exact le_of_mul_le_mul_ne key hdpos

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3P_Char: the archimedean phase is the `S`-character

For `z` in the trace dual of an exterior ideal `𝔫` (and `S ⊇` the primes of the different),
`exp(2πi Tr z) = e(−z)` with `e = sAddChar 𝔪`: write `z = y + r` with `y ∈ 𝔫⁻¹` integral at `S` and
`r ∈ 𝔇⁻¹`, so `Tr r ∈ ℤ` and `r ∈ R`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical Real

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

theorem different_sup_eq_top (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) :
    differentIdeal ℤ (𝓞 F) ⊔ 𝔫 = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hP0 : P ≠ ⊥ := fun h => differentIdeal_ne_bot (le_bot_iff.1 (h ▸ le_sup_left.trans hle))
  set w : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, hP0⟩
  have hw : w ∈ placesOf 𝔪 := hD w (Ideal.dvd_iff_le.2 (le_sup_left.trans hle))
  have h2 : 𝔫 ⊔ 𝔪 ≤ P := sup_le (le_sup_right.trans hle) hw
  rw [h𝔫.2, top_le_iff] at h2
  exact hP.ne_top h2

theorem dual_le_add (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) :
    FractionalIdeal.dual ℤ ℚ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≤
      (𝔫 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ + FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  have h𝔫0 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔫.1
  have hD0 : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    coeIdeal_ne_zero.2 differentIdeal_ne_bot
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) =
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv]
  have hsum : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) +
      (𝔫 : FractionalIdeal (𝓞 F)⁰ F) = 1 := by
    rw [← coeIdeal_sup, different_sup_eq_top hD h𝔫, coeIdeal_top]
  rw [FractionalIdeal.dual_eq_mul_inv, hd1]
  set D := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  set N := (𝔫 : FractionalIdeal (𝓞 F)⁰ F)
  calc D⁻¹ * N⁻¹ = D⁻¹ * N⁻¹ * (D + N) := by rw [hsum, mul_one]
    _ = N⁻¹ * (D⁻¹ * D) + D⁻¹ * (N⁻¹ * N) := by ring
    _ = N⁻¹ + D⁻¹ := by rw [inv_mul_cancel₀ hD0, inv_mul_cancel₀ h𝔫0, mul_one, mul_one]
    _ ≤ _ := le_rfl

/-- The archimedean phase of a trace-dual element is the `S`-character. -/
theorem fourierChar_trace_eq (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) {z : F}
    (hz : z ∈ FractionalIdeal.dual ℤ ℚ (𝔫 : FractionalIdeal (𝓞 F)⁰ F)) :
    (Real.fourierChar ((Algebra.trace ℚ F z : ℚ) : ℝ) : ℂ) = sAddChar 𝔪 (-z) := by
  obtain ⟨y, hy, r, hr, rfl⟩ := (mem_add _ _ _).1 (dual_le_add hD h𝔫 hz)
  have h𝔫0 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔫.1
  -- `y` is integral at `S`
  have hyS : ∀ v ∈ placesOf 𝔪, v.valuation F (-y) ≤ 1 := by
    intro v hv
    rw [Valuation.map_neg]
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]; exact _root_.zero_le
    rw [valuation_le_one_iff v hy0]
    have := (mem_iff_count hy0 (inv_ne_zero h𝔫0)).1 hy v
    rw [count_inv, count_eq_zero_of_exterior h𝔫 hv, neg_zero] at this
    exact this
  -- `r ∈ R` and `Tr r ∈ ℤ`
  have hrR : r ∈ (placesOf 𝔪).integer F := by
    have hdd := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
    rw [coe_different_eq_Pk hD] at hdd
    have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) =
        ((Pk (-delta (𝔪 := 𝔪)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [Pk_neg, Units.val_inv_eq_inv_val, hdd, inv_inv]
    exact Pk_subset_SInt _ (hd1 ▸ hr)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (Algebra.trace ℚ F r : ℚ) = n := by
    have := (FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0)).1 hr 1
      (one_mem_one _)
    obtain ⟨n, hn⟩ := this
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, mul_one] at hn
    rw [← hn]; simp
  have h1 : -(y + r) - (-y) ∈ (placesOf 𝔪).integer F := by
    rw [show -(y + r) - -y = -r by ring]; exact neg_mem hrR
  rw [C3I.sAddChar_eq_of_wit h1 hyS, Real.fourierChar_apply, map_add, hn, map_neg]
  push_cast
  rw [show 2 * (π : ℂ) * ((Algebra.trace ℚ F y : ℚ) + (n : ℂ)) * Complex.I =
      -(2 * π * Complex.I) * -((Algebra.trace ℚ F y : ℚ) : ℂ) + n * (2 * π * Complex.I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Dil: positive dilations of the mixed space

For `x : realSpace K`, `dilV x = mixedSpaceOfRealSpace (expMap x)` has coordinates
`exp(x_w / mult w) > 0`. Multiplication by it is a linear automorphism of determinant
`exp (∑ w, x w)` (for `K` totally complex), and it rescales the Fourier transform.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- The positive point `(exp(x_w / mult w))_w` of the mixed space. -/
noncomputable def dilV (x : realSpace K) : mixedSpace K := mixedSpaceOfRealSpace (expMap x)

theorem dilV_fst (x : realSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (dilV x).1 w = Real.exp ((w.1.mult : ℝ)⁻¹ * x w) := by
  simp [dilV, mixedSpaceOfRealSpace_apply, expMap_apply]

theorem dilV_snd (x : realSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (dilV x).2 w = (Real.exp ((w.1.mult : ℝ)⁻¹ * x w) : ℂ) := by
  simp [dilV, mixedSpaceOfRealSpace_apply, expMap_apply]

theorem dilV_add (x x' : realSpace K) : dilV (x + x') = dilV x * dilV x' := by
  ext w
  · simp only [dilV_fst, Prod.fst_mul, Pi.mul_apply, Pi.add_apply, mul_add, Real.exp_add]
  · simp only [dilV_snd, Prod.snd_mul, Pi.mul_apply, Pi.add_apply, mul_add, Real.exp_add,
      Complex.ofReal_mul]

theorem dilV_zero : dilV (0 : realSpace K) = 1 := by
  ext w
  · simp [dilV_fst]
  · simp [dilV_snd]

theorem dilV_mul_neg (x : realSpace K) : dilV x * dilV (-x) = 1 := by
  rw [← dilV_add, add_neg_cancel, dilV_zero]

theorem dilV_neg_mul (x : realSpace K) : dilV (-x) * dilV x = 1 := by
  rw [mul_comm, dilV_mul_neg]

theorem normAtPlace_dilV_mul (x : realSpace K) (z : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (dilV x * z) = Real.exp ((w.mult : ℝ)⁻¹ * x w) * normAtPlace w z := by
  rw [map_mul]
  congr 1
  rw [dilV, normAtPlace_mixedSpaceOfRealSpace (expMap_pos x w).le, expMap_apply]

/-- Multiplication by `a`, as a linear map. -/
noncomputable def mulL (a : mixedSpace K) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.mulLeft ℝ a

@[simp] theorem mulL_apply (a z : mixedSpace K) : mulL a z = a * z := rfl

theorem mulL_eq_prodMap (a : mixedSpace K) :
    mulL a = LinearMap.prodMap (LinearMap.mulLeft ℝ a.1)
      (LinearMap.pi fun w : {w : InfinitePlace K // IsComplex w} =>
        (LinearMap.mulLeft ℝ (a.2 w)) ∘ₗ LinearMap.proj w) := by
  ext z w <;> simp

theorem isEmpty_isReal [IsTotallyComplex K] : IsEmpty {w : InfinitePlace K // IsReal w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩

theorem det_mulL [IsTotallyComplex K] (a : mixedSpace K) :
    LinearMap.det (mulL a) = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖a.2 w‖ ^ 2 := by
  have : IsEmpty {w : InfinitePlace K // IsReal w} := isEmpty_isReal
  rw [mulL_eq_prodMap, LinearMap.det_prodMap, LinearMap.det_eq_one_of_subsingleton, one_mul,
    LinearMap.det_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [show LinearMap.mulLeft ℝ (a.2 w) = Algebra.lmul ℝ ℂ (a.2 w) from rfl,
    ← Algebra.norm_apply ℝ (a.2 w), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem det_mulL_dilV [IsTotallyComplex K] (x : realSpace K) :
    LinearMap.det (mulL (dilV x)) = Real.exp (∑ w, x w) := by
  rw [det_mulL]
  simp only [dilV_snd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mult_isComplex, Nat.cast_ofNat]
  simp_rw [← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _
    fun w => ?_
  simp only [Equiv.subtypeUnivEquiv_apply]
  push_cast
  ring

/-- The change of variables for multiplication by an invertible `a`. -/
theorem integral_comp_mul [IsTotallyComplex K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : mixedSpace K → E) (a b : mixedSpace K) (hab : a * b = 1) :
    ∫ v, g (a * v) = (LinearMap.det (mulL a))⁻¹ • ∫ v, g v := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hdet : LinearMap.det (mulL a) ≠ 0 := by
    intro h
    have : LinearMap.det (mulL a) * LinearMap.det (mulL b) = 1 := by
      rw [← LinearMap.det_comp]
      have : mulL a ∘ₗ mulL b = LinearMap.id := by ext z <;> simp [← mul_assoc, hab]
      rw [this, LinearMap.det_id]
    rw [h, zero_mul] at this; exact zero_ne_one this
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (mixedSpace K)) hdet
  let eL : mixedSpace K ≃ₗ[ℝ] mixedSpace K :=
    { mulL a with
      invFun := fun z => b * z
      left_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hba,
          one_mul]
      right_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hab,
          one_mul] }
  let e : mixedSpace K ≃ᵐ mixedSpace K :=
    (LinearEquiv.toContinuousLinearEquiv eL).toHomeomorph.toMeasurableEquiv
  have he : (e : mixedSpace K → mixedSpace K) = mulL a := rfl
  have h1 := integral_map_equiv (μ := (volume : Measure (mixedSpace K))) e g
  rw [he, hmap, integral_smul_measure] at h1
  rw [← he] at h1
  change ∫ v, g (e v) = _
  rw [← h1, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hpos : 0 < LinearMap.det (mulL a) := by
    refine lt_of_le_of_ne ?_ (Ne.symm hdet)
    rw [det_mulL]; positivity
  rw [abs_of_pos (inv_pos.2 hpos)]

/-- Multiplication by an invertible `a`, as a continuous linear equivalence. -/
noncomputable def mulE (a b : mixedSpace K) (hab : a * b = 1) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  LinearEquiv.toContinuousLinearEquiv
    { mulL a with
      invFun := fun z => b * z
      left_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc,
          mul_comm b a, hab, one_mul]
      right_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hab,
          one_mul] }

@[simp] theorem mulE_apply (a b : mixedSpace K) (hab : a * b = 1) (z : mixedSpace K) :
    mulE a b hab z = a * z := rfl

/-- Multiplication by `dilV x`, as a continuous linear equivalence. -/
noncomputable def dilE (x : realSpace K) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  mulE (dilV x) (dilV (-x)) (dilV_mul_neg x)

@[simp] theorem dilE_apply (x : realSpace K) (z : mixedSpace K) : dilE x z = dilV x * z := rfl

/-- The change of variables for a positive dilation. -/
theorem integral_comp_dilV [IsTotallyComplex K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : mixedSpace K → E) (x : realSpace K) :
    ∫ v, g (dilV x * v) = Real.exp (-(∑ w, x w)) • ∫ v, g v := by
  rw [integral_comp_mul g _ _ (dilV_mul_neg x), det_mulL_dilV, Real.exp_neg]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Pois: Poisson summation over a fractional ideal, dilated and translated

From the library's lattice Poisson formula (4bf11d4c) and the trace dual of an ideal lattice
(9fd5cbc5): for a fractional ideal `I`, a Schwartz function `φ` on the mixed space, a positive
dilation `x` and a translation `t ∈ K`,
`∑_{a ∈ I} φ(y_x (t + a)) = (covol I · e^{Σx})⁻¹ ∑_{η ∈ I^∨} φ̂(y_x⁻¹ η) e(Tr(t η))`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The Fourier transform on the mixed space for the trace pairing. -/
noncomputable def fourierM (φ : mixedSpace K → ℂ) (η : mixedSpace K) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (Algebra.traceForm ℝ (mixedSpace K)) φ η

theorem fourierM_dil [IsTotallyComplex K] (φ : mixedSpace K → ℂ) (x : realSpace K)
    (η : mixedSpace K) :
    fourierM (fun v => φ (dilV x * v)) η =
      Real.exp (-(∑ w, x w)) • fourierM φ (dilV (-x) * η) := by
  simp only [fourierM, VectorFourier.fourierIntegral]
  have key : ∀ v : mixedSpace K, Algebra.traceForm ℝ (mixedSpace K) v η =
      Algebra.traceForm ℝ (mixedSpace K) (dilV x * v) (dilV (-x) * η) := by
    intro v
    simp only [Algebra.traceForm_apply]
    congr 1
    calc v * η = (dilV (-x) * dilV x) * (v * η) := by rw [dilV_neg_mul, one_mul]
      _ = dilV x * v * (dilV (-x) * η) := by ring
  simp_rw [key]
  exact integral_comp_dilV (fun u => Real.fourierChar (-(Algebra.traceForm ℝ (mixedSpace K) u
    (dilV (-x) * η))) • φ u) x

/-- The elements of a fractional ideal, embedded, are the ideal lattice. -/
noncomputable def latEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) ≃ idealLattice K I :=
  Equiv.ofBijective (fun a => ⟨mixedEmbedding K a, (mem_idealLattice K I).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (mixedEmbedding_injective K (congrArg Subtype.val h)), fun z => by
      obtain ⟨a, ha, h⟩ := (mem_idealLattice K I).1 z.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩

/-- The trace dual, embedded, is the dual lattice. -/
noncomputable def dualEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) ≃
    LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
      (idealLattice K I) :=
  Equiv.ofBijective (fun a => ⟨mixedEmbedding K a, by
      have h := coe_dualSubmodule_flip_traceForm_idealLattice K I
      have : mixedEmbedding K a ∈ (LinearMap.BilinForm.dualSubmodule
          (Algebra.traceForm ℝ (mixedSpace K)).flip (idealLattice K I) : Set (mixedSpace K)) := by
        rw [h]; exact ⟨a, a.2, rfl⟩
      exact this⟩)
    ⟨fun a b h => Subtype.ext (mixedEmbedding_injective K (congrArg Subtype.val h)), fun z => by
      have h := coe_dualSubmodule_flip_traceForm_idealLattice K I
      have hz : (z : mixedSpace K) ∈ (LinearMap.BilinForm.dualSubmodule
          (Algebra.traceForm ℝ (mixedSpace K)).flip (idealLattice K I) : Set (mixedSpace K)) := z.2
      rw [h] at hz
      obtain ⟨a, ha, h⟩ := hz
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩

theorem traceForm_mixedEmbedding (t η : K) :
    Algebra.traceForm ℝ (mixedSpace K) (mixedEmbedding K t) (mixedEmbedding K η) =
      (Algebra.trace ℚ K (t * η) : ℝ) := by
  rw [Algebra.traceForm_apply, ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding]

/-- **Poisson summation over a fractional ideal**, dilated by `dilV x` and translated by `t`. -/
theorem tsum_dil_eq [IsTotallyComplex K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (φ : 𝓢(mixedSpace K, ℂ)) (x : realSpace K) (t : K) :
    ∑' a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K),
        φ (dilV x * mixedEmbedding K (t + a)) =
      ((ZLattice.covolume (idealLattice K I) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
        ∑' η : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
            FractionalIdeal (𝓞 K)⁰ K) : Set K),
          fourierM φ (dilV (-x) * mixedEmbedding K η) *
            (Real.fourierChar (Algebra.trace ℚ K (t * η) : ℝ) : ℂ) := by
  set φx : 𝓢(mixedSpace K, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilE x) φ
  have hφx : ∀ v, φx v = φ (dilV x * v) := fun v => rfl
  have h := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral volume
    (Algebra.traceForm ℝ (mixedSpace K)) (traceForm_mixedSpace_nondegenerate K) (idealLattice K I)
    φx (mixedEmbedding K t)
  rw [← (latEquiv I).tsum_eq, ← (dualEquiv I).tsum_eq] at h
  simp only [hφx] at h
  have hL : ∀ a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K),
      φ (dilV x * mixedEmbedding K (t + a)) =
        φ (dilV x * (mixedEmbedding K t + ((latEquiv I a : idealLattice K I) : mixedSpace K))) := by
    intro a; rw [map_add]; rfl
  simp_rw [hL, h]
  rw [Complex.ofReal_mul, mul_inv, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun η => ?_
  change VectorFourier.fourierIntegral Real.fourierChar volume (Algebra.traceForm ℝ (mixedSpace K))
      (fun v => φ (dilV x * v)) (mixedEmbedding K η) *
      (Real.fourierChar (Algebra.traceForm ℝ (mixedSpace K) (mixedEmbedding K t)
        (mixedEmbedding K η)) : ℂ) = _
  have := fourierM_dil (φ := fun v => φ v) x (mixedEmbedding K η)
  simp only [fourierM] at this
  rw [this, traceForm_mixedEmbedding, Real.exp_neg, Complex.real_smul]
  push_cast
  simp only [fourierM]
  ring

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L2B_Quot: exterior ideals of `𝓞 F` and of `R` (copied from L2A_FSQuot, prover A, to decouple)

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,

-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Every `r ∈ R` has `𝔪^N r ⊆ 𝓞` for some `N`. -/
lemma exists_pow_mul_mem (r : SInt 𝔪) : ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ c : 𝓞 F,
    algebraMap (𝓞 F) (SInt 𝔪) w * r = algebraMap (𝓞 F) (SInt 𝔪) c := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (r : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  refine ⟨N, fun w hw => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      v.valuation F (algebraMap (𝓞 F) F w * (r : F)) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · have hvm : 𝔪 ≤ v.asIdeal := hv
      have hdN : d ∉ v.asIdeal ^ N := by
        intro hmem
        have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
        have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
        rw [map_pow] at hdvd
        have hN0 : N ≠ 0 := by
          rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
        have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
          have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
            rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
          have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
            rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
          omega
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
        have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
        have h4 : N < 2 ^ N := Nat.lt_two_pow_self
        omega
      have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [C3I.val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
      have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
        rw [C3I.val_alg, v.intValuation_le_pow_iff_mem]
        exact Ideal.pow_right_mono hvm N hw
      have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
      have hxd : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
        rw [← hbd, div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
      have key : v.valuation F (algebraMap (𝓞 F) F w * (r : F)) *
          v.valuation F (algebraMap (𝓞 F) F d) ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [← map_mul, show algebraMap (𝓞 F) F w * (r : F) * algebraMap (𝓞 F) F d =
          algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [mul_assoc, hxd]; ring, map_mul]
        exact mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
      exact C3I.le_of_mul_le_mul_ne key hdpos
    · rw [map_mul]
      exact mul_le_one' (v.valuation_le_one w) (r.2 v hv)
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint
  refine ⟨c, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, C3I.coe_alg, C3I.coe_alg, hc]

/-- `𝓞 → R / I R` is onto for `I` coprime to `𝔪`. -/
lemma exists_sub_mem_map (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (r : SInt 𝔪) :
    ∃ c : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) c ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨c, hc⟩ := hN w hw
  refine ⟨c, ?_⟩
  have : r - algebraMap (𝓞 F) (SInt 𝔪) c = algebraMap (𝓞 F) (SInt 𝔪) u * r := by
    rw [← hc]
    have : algebraMap (𝓞 F) (SInt 𝔪) u + algebraMap (𝓞 F) (SInt 𝔪) w = 1 := by
      rw [← map_add, huw, map_one]
    linear_combination (-r) * this
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

lemma quotHom_surjective (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) :
    Function.Surjective (C3I.quotHom 𝔪 I) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_map I hI r
  exact ⟨Ideal.Quotient.mk _ c, by rw [C3I.quotHom_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩

lemma finite_quot_map (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Finite (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_surjective _ (quotHom_surjective I hI)

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-!
# L3P_Lat: the lattices `P^k`, their cosets mod `𝔫`, and summability

* `summable_schwartz_lattice`: a Schwartz function is summable over a translated ideal lattice.
* `exists_rep`: every class of `R / 𝔫R` has a representative in `P^k`.
* `sub_mem_mul_Pk`, `mem_map_of_mem_mul_Pk`: `P^k ∩ 𝔫R = 𝔫 P^k`.
* `tsum_Pk_eq_sum_cosets`: a lattice sum over `P^k` splits over the classes of `R / 𝔫R`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  FractionalIdeal
open scoped nonZeroDivisors Classical Real SchwartzMap

set_option linter.unusedSectionVars false

/-! ### Summability over ideal lattices -/

section summ

variable {K : Type*} [Field K] [NumberField K]

theorem summable_schwartz_idealLattice (f : 𝓢(mixedSpace K, ℂ)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : mixedSpace K) : Summable fun z : idealLattice K I => ‖f (t + z)‖ := by
  set N : ℕ := Module.finrank ℤ (idealLattice K I) + 1
  set C := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hb : ∀ x : mixedSpace K, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ (-(N : ℝ)) := by
    intro x hx
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at h1
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h2 : ‖x‖ ^ N * ‖f x‖ ≤ C := by
      refine le_trans ?_ h1
      gcongr
      linarith
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
      mul_comm]
    exact h2
  refine Summable.of_norm_bounded_eventually
    ((ZLattice.summable_norm_sub_rpow (L := idealLattice K I) (-(N : ℝ))
      (by simp [N]) (-t)).mul_left C) ?_
  have hfin : {z : idealLattice K I | t + (z : mixedSpace K) = 0}.Subsingleton := by
    intro a ha b hb
    exact Subtype.ext (by have := ha.trans hb.symm; simpa using this)
  refine (hfin.finite.subset fun z hz => ?_)
  by_contra h
  apply hz
  simp only [Set.mem_ofPred_eq, norm_norm]
  rw [sub_neg_eq_add, add_comm]
  exact hb _ fun h0 => h (by simpa [add_comm] using h0)

theorem summable_schwartz_fractionalIdeal (f : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : mixedSpace K) :
    Summable fun a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) => ‖f (t + mixedEmbedding K a)‖ := by
  have := summable_schwartz_idealLattice f I t
  rw [← (latEquiv I).summable_iff] at this
  exact this

end summ

/-! ### Coset representatives -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

omit [Fintype (SP 𝔪)] in
theorem count_pos_of_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ placesOf 𝔪) (h𝔪 : 𝔪 ≠ ⊥) :
    1 ≤ count F v (𝔪 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [count_coe F v h𝔪]
  have : (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd h𝔪 v.irreducible).2 (Ideal.dvd_iff_le.2 hv)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/-- Every class of `R / 𝔫 R` has a representative in `P^k`. -/
theorem exists_rep (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (k : SP 𝔪 → ℤ)
    (x : SInt 𝔪) : ∃ x₀ : SInt 𝔪, (x₀ : F) ∈ ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) ∧ x₀ - x ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  by_cases hx0 : (x : F) = 0
  · refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := Subtype.ext hx0
    rw [this, sub_zero]; exact zero_mem _
  set N : ℕ := ∑ v : SP 𝔪, (k v - ordv v.1 (x : F)).toNat
  have hcop : 𝔫 ⊔ 𝔪 ^ N = ⊤ := by
    have h1 : IsCoprime 𝔫 𝔪 := Ideal.isCoprime_iff_sup_eq.2 h𝔫.2
    exact Ideal.isCoprime_iff_sup_eq.1 (h1.pow_right)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top (x := (1 : 𝓞 F)))
  refine ⟨x * algebraMap (𝓞 F) (SInt 𝔪) b, ?_, ?_⟩
  · by_cases hb0 : b = 0
    · simp only [hb0, map_zero, mul_zero, ZeroMemClass.coe_zero]; exact zero_mem _
    have hbK : algebraMap (𝓞 F) F b ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    have hprod : ((x * algebraMap (𝓞 F) (SInt 𝔪) b : SInt 𝔪) : F) = (x : F) * algebraMap (𝓞 F) F b :=
      rfl
    rw [hprod, mem_Pk_iff (mul_ne_zero hx0 hbK)]
    refine ⟨?_, fun v => ?_⟩
    · rw [← hprod]; exact (x * algebraMap (𝓞 F) (SInt 𝔪) b).2
    · simp only [valS, ordv_mul v.1 hx0 hbK]
      have h1 : count F v.1 ((𝔪 ^ N : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≤
          ordv v.1 (algebraMap (𝓞 F) F b) := by
        have : spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F b) ≤
            ((𝔪 ^ N : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
          rw [spanSingleton_le_iff_mem]; exact mem_coeIdeal_of_mem _ hb
        exact count_mono F v.1 (spanSingleton_ne_zero hbK) this
      rw [coeIdeal_pow, count_pow] at h1
      have h2 := count_pos_of_mem v.2 h𝔪
      have h3 : (k v - ordv v.1 (x : F)).toNat ≤ N :=
        Finset.single_le_sum (f := fun v : SP 𝔪 => (k v - ordv v.1 (x : F)).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      have h4 : k v - ordv v.1 (x : F) ≤ (N : ℤ) := by
        have := Int.self_le_toNat (k v - ordv v.1 (x : F)); omega
      nlinarith
  · have : x * algebraMap (𝓞 F) (SInt 𝔪) b - x = -(x * algebraMap (𝓞 F) (SInt 𝔪) a) := by
      have hab' : algebraMap (𝓞 F) (SInt 𝔪) a + algebraMap (𝓞 F) (SInt 𝔪) b = 1 := by
        rw [← map_add, hab, map_one]
      linear_combination x * hab'
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha))

/-- `P^k ∩ 𝔫R ⊆ 𝔫 P^k`. -/
theorem mem_mul_Pk_of_mem {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (k : SP 𝔪 → ℤ) {z : SInt 𝔪}
    (hz : (z : F) ∈ ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F))
    (hz' : z ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    (z : F) ∈ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
  by_cases hz0 : (z : F) = 0
  · rw [hz0]; exact zero_mem _
  have h𝔫0 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔫.1
  rw [mem_iff_count hz0 (mul_ne_zero h𝔫0 (Pk_ne_zero k))]
  intro w
  rw [count_mul F w h𝔫0 (Pk_ne_zero k), count_Pk]
  split_ifs with hw
  · rw [count_eq_zero_of_exterior h𝔫 hw, zero_add]
    exact ((mem_Pk_iff hz0 k).1 hz).2 ⟨w, hw⟩
  · rw [add_zero]
    exact ordv_ge_of_mem_map 𝔫 hw hz' hz0

/-- `𝔫 P^k ⊆ P^k ∩ 𝔫R`. -/
theorem mem_map_of_mem_mul_Pk {𝔫 : Ideal (𝓞 F)} (k : SP 𝔪 → ℤ) {y : F}
    (hy : y ∈ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
    y ∈ ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
      ∃ hyR : y ∈ (placesOf 𝔪).integer F,
        (⟨y, hyR⟩ : SInt 𝔪) ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have hle : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≤
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    calc _ ≤ 1 * ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left coeIdeal_le_one _
      _ = _ := one_mul _
  have hyJ := hle hy
  refine ⟨hyJ, Pk_subset_SInt k hyJ, ?_⟩
  -- induction on the product
  suffices H : ∀ y ∈ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      ∃ hyR : y ∈ (placesOf 𝔪).integer F,
        (⟨y, hyR⟩ : SInt 𝔪) ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) from (H y hy).2
  intro y hy
  refine FractionalIdeal.mul_induction_on hy ?_ ?_
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := (mem_coeIdeal _).1 ha
    have hbR := Pk_subset_SInt k hb
    set z : SInt 𝔪 := algebraMap (𝓞 F) (SInt 𝔪) a' * ⟨b, hbR⟩
    have e : (z : F) = algebraMap (𝓞 F) F a' * b := by
      simp only [z, Subalgebra.coe_mul]
      rfl
    refine ⟨e ▸ z.2, ?_⟩
    have : (⟨algebraMap (𝓞 F) F a' * b, e ▸ z.2⟩ : SInt 𝔪) = z := Subtype.ext e.symm
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha')
  · rintro x y ⟨hxR, hx⟩ ⟨hyR, hy⟩
    refine ⟨add_mem hxR hyR, ?_⟩
    have : (⟨x + y, add_mem hxR hyR⟩ : SInt 𝔪) = ⟨x, hxR⟩ + ⟨y, hyR⟩ := rfl
    rw [this]
    exact add_mem hx hy

omit [Fintype (SP 𝔪)] in
theorem fi_add_mem {I : FractionalIdeal (𝓞 F)⁰ F} {a b : F} (ha : a ∈ I) (hb : b ∈ I) :
    a + b ∈ I := Submodule.add_mem (I : Submodule (𝓞 F) F) ha hb

omit [Fintype (SP 𝔪)] in
theorem fi_sub_mem {I : FractionalIdeal (𝓞 F)⁰ F} {a b : F} (ha : a ∈ I) (hb : b ∈ I) :
    a - b ∈ I := Submodule.sub_mem (I : Submodule (𝓞 F) F) ha hb

/-- The quotient `R / 𝔫 R`. -/
abbrev Qn (𝔪 𝔫 : Ideal (𝓞 F)) : Type _ := SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))

/-- A representative in `P^k` of a class of `R / 𝔫R`. -/
noncomputable def repPk (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (k : SP 𝔪 → ℤ)
    (x : Qn 𝔪 𝔫) : SInt 𝔪 := (exists_rep h𝔪 h𝔫 k (quotLift x)).choose

theorem repPk_mem (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (k : SP 𝔪 → ℤ)
    (x : Qn 𝔪 𝔫) : ((repPk h𝔪 h𝔫 k x : SInt 𝔪) : F) ∈
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :=
  (exists_rep h𝔪 h𝔫 k (quotLift x)).choose_spec.1

theorem mk_repPk (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (k : SP 𝔪 → ℤ)
    (x : Qn 𝔪 𝔫) : Ideal.Quotient.mk _ (repPk h𝔪 h𝔫 k x) = x := by
  have h := (exists_rep h𝔪 h𝔫 k (quotLift x)).choose_spec.2
  rw [← Ideal.Quotient.eq] at h
  rw [repPk, h]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective x

/-- The class in `R / 𝔫 R` of an element of `P^k`. -/
noncomputable def clsPk {𝔫 : Ideal (𝓞 F)} (k : SP 𝔪 → ℤ)
    (m : (((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F)) :
    Qn 𝔪 𝔫 := Ideal.Quotient.mk _ ⟨m, Pk_subset_SInt k m.2⟩

/-- A fiber of `clsPk` is a translate of `𝔫 P^k`. -/
noncomputable def fiberEquiv (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    (k : SP 𝔪 → ℤ) (x : Qn 𝔪 𝔫) :
    ((((𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) : FractionalIdeal (𝓞 F)⁰ F) :
        Set F) ≃ (clsPk (𝔫 := 𝔫) k ⁻¹' {x}) where
  toFun a := ⟨⟨(repPk h𝔪 h𝔫 k x : F) + a, fi_add_mem (repPk_mem h𝔪 h𝔫 k x)
      (mem_map_of_mem_mul_Pk k a.2).1⟩, by
    obtain ⟨_, haR, ham⟩ := mem_map_of_mem_mul_Pk k a.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff, clsPk]
    have : (⟨(repPk h𝔪 h𝔫 k x : F) + a, _⟩ : SInt 𝔪) = repPk h𝔪 h𝔫 k x + ⟨a, haR⟩ := rfl
    rw [this, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 ham, add_zero, mk_repPk]⟩
  invFun m := ⟨(m : F) - (repPk h𝔪 h𝔫 k x : F), by
    have hm := m.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff, clsPk] at hm
    have hsub : (⟨(m : F), Pk_subset_SInt k m.1.2⟩ : SInt 𝔪) - repPk h𝔪 h𝔫 k x ∈
        𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, hm, mk_repPk]
    exact mem_mul_Pk_of_mem h𝔫 k (fi_sub_mem m.1.2 (repPk_mem h𝔪 h𝔫 k x)) hsub⟩
  left_inv a := by ext; simp
  right_inv m := by ext; simp

theorem bounded_of_periodic {𝔫 : Ideal (𝓞 F)} (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    [Finite (Qn 𝔪 𝔫)] : ∃ B : ℝ, ∀ x, ‖c x‖ ≤ B := by
  have : Fintype (Qn 𝔪 𝔫) := Fintype.ofFinite _
  refine ⟨∑ q : Qn 𝔪 𝔫, ‖c (quotLift q)‖, fun x => ?_⟩
  have hx : c x = c (quotLift (Ideal.Quotient.mk _ x : Qn 𝔪 𝔫)) := by
    have h : quotLift (Ideal.Quotient.mk _ x : Qn 𝔪 𝔫) - x ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq]
      exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
    have := hc x _ h
    rw [add_sub_cancel] at this
    exact this.symm
  rw [hx]
  exact Finset.single_le_sum (f := fun q : Qn 𝔪 𝔫 => ‖c (quotLift q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

/-- A lattice sum over `P^k` of a `𝔫R`-periodic coefficient splits over the classes of
`R / 𝔫 R`. -/
theorem tsum_Pk_eq_sum (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (k : SP 𝔪 → ℤ)
    (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    [Fintype (Qn 𝔪 𝔫)] (G : F → ℂ)
    (hG : Summable fun m : (((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
      Set F) => ‖G m‖) :
    ∑' m : (((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F),
        c ⟨m, Pk_subset_SInt k m.2⟩ * G m =
      ∑ x : Qn 𝔪 𝔫, c (quotLift x) * ∑' a : ((((𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
        ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
          FractionalIdeal (𝓞 F)⁰ F) : Set F), G ((repPk h𝔪 h𝔫 k x : F) + a) := by
  obtain ⟨B, hB⟩ := bounded_of_periodic c hc
  have hs : Summable fun m : (((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
      Set F) => c ⟨m, Pk_subset_SInt k m.2⟩ * G m :=
    Summable.of_norm_bounded (hG.mul_left B) fun m => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have h := hs.hasSum.tsum_fiberwise (clsPk (𝔫 := 𝔫) k)
  rw [← h.tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcx : ∀ m : (clsPk (𝔫 := 𝔫) k ⁻¹' {x}), c ⟨(m : F), Pk_subset_SInt k m.1.2⟩ = c (quotLift x) := by
    intro m
    have hm := m.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff, clsPk] at hm
    have h1 : quotLift x - ⟨(m : F), Pk_subset_SInt k m.1.2⟩ ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, hm]
      exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
    have := hc ⟨(m : F), Pk_subset_SInt k m.1.2⟩ _ h1
    rw [add_sub_cancel] at this
    exact this.symm
  simp_rw [hcx]
  rw [tsum_mul_left]
  congr 1
  rw [← (fiberEquiv h𝔪 h𝔫 k x).tsum_eq]
  rfl

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Test: radial test functions on the mixed space

A smooth compactly supported `Φ` on `realSpace K` (log coordinates `mult w · log ‖z_w‖`) gives the
radial test function `phiF Φ` on the mixed space: smooth, compactly supported, vanishing near the
coordinate hyperplanes. Its Fourier transform is radial as well, `fourierM (phiF Φ) z = PhiHat Φ
(logM z)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- Log coordinates of a point of the mixed space. -/
noncomputable def logM (z : mixedSpace K) : realSpace K :=
  fun w => (w.mult : ℝ) * Real.log (normAtPlace w z)

/-- Log coordinates of an element of `K`. -/
noncomputable def logK (m : K) : realSpace K := logM (mixedEmbedding K m)

theorem logK_apply (m : K) (w : InfinitePlace K) : logK m w = (w.mult : ℝ) * Real.log (w m) := by
  simp [logK, logM, normAtPlace_apply]

theorem logM_mul (z z' : mixedSpace K) (hz : ∀ w, normAtPlace w z ≠ 0)
    (hz' : ∀ w, normAtPlace w z' ≠ 0) : logM (z * z') = logM z + logM z' := by
  funext w
  simp only [logM, map_mul, Pi.add_apply]
  rw [Real.log_mul (hz w) (hz' w), mul_add]

theorem normAtPlace_dilV (x : realSpace K) (w : InfinitePlace K) :
    normAtPlace w (dilV x) = Real.exp ((w.mult : ℝ)⁻¹ * x w) := by
  have := normAtPlace_dilV_mul x 1 w
  rwa [mul_one, map_one, mul_one] at this

theorem normAtPlace_dilV_ne_zero (x : realSpace K) (w : InfinitePlace K) :
    normAtPlace w (dilV x) ≠ 0 := by
  rw [normAtPlace_dilV]; exact (Real.exp_pos _).ne'

theorem logM_dilV (x : realSpace K) : logM (dilV x) = x := by
  funext w
  simp only [logM, normAtPlace_dilV, Real.log_exp]
  have : (w.mult : ℝ) ≠ 0 := by have := w.mult_pos; positivity
  field_simp

theorem logM_dilV_mul (x : realSpace K) (z : mixedSpace K) (hz : ∀ w, normAtPlace w z ≠ 0) :
    logM (dilV x * z) = x + logM z := by
  rw [logM_mul _ _ (normAtPlace_dilV_ne_zero x) hz, logM_dilV]

theorem normAtPlace_mixedEmbedding_ne_zero {m : K} (hm : m ≠ 0) (w : InfinitePlace K) :
    normAtPlace w (mixedEmbedding K m) ≠ 0 := by
  rw [normAtPlace_apply]; exact (map_ne_zero w).2 hm

/-- The radial test function attached to `Φ`. -/
noncomputable def phiF (Φ : realSpace K → ℝ) (z : mixedSpace K) : ℂ :=
  if ∀ w, normAtPlace w z ≠ 0 then (Φ (logM z) : ℂ) else 0

theorem phiF_of_ne {Φ : realSpace K → ℝ} {z : mixedSpace K} (hz : ∀ w, normAtPlace w z ≠ 0) :
    phiF Φ z = Φ (logM z) := if_pos hz

theorem phiF_zero (Φ : realSpace K → ℝ) [Nonempty (InfinitePlace K)] :
    phiF Φ (0 : mixedSpace K) = 0 := by
  rw [phiF, if_neg]
  push Not
  exact ⟨Classical.arbitrary _, map_zero _⟩

theorem phiF_dilV_mul (Φ : realSpace K → ℝ) (x : realSpace K) {z : mixedSpace K}
    (hz : ∀ w, normAtPlace w z ≠ 0) : phiF Φ (dilV x * z) = Φ (x + logM z) := by
  have hz' : ∀ w, normAtPlace w (dilV x * z) ≠ 0 := fun w => by
    rw [map_mul]; exact mul_ne_zero (normAtPlace_dilV_ne_zero x w) (hz w)
  rw [phiF_of_ne hz', logM_dilV_mul x z hz]

theorem phiF_dilV_mul_emb (Φ : realSpace K → ℝ) (x : realSpace K) {m : K} (hm : m ≠ 0) :
    phiF Φ (dilV x * mixedEmbedding K m) = Φ (x + logK m) :=
  phiF_dilV_mul Φ x (normAtPlace_mixedEmbedding_ne_zero hm)

/-- `phiF` is radial. -/
theorem phiF_mul_of_norm_eq_one (Φ : realSpace K → ℝ) (u z : mixedSpace K)
    (hu : ∀ w, normAtPlace w u = 1) : phiF Φ (u * z) = phiF Φ z := by
  have h : ∀ w, normAtPlace w (u * z) = normAtPlace w z := fun w => by
    rw [map_mul, hu, one_mul]
  have hl : logM (u * z) = logM z := by funext w; simp only [logM, h]
  simp only [phiF, h, hl]

section smooth

variable [IsTotallyComplex K]

theorem normAtPlace_eq_norm_snd (w : InfinitePlace K) (z : mixedSpace K) :
    normAtPlace w z = ‖z.2 ⟨w, IsTotallyComplex.isComplex w⟩‖ :=
  normAtPlace_apply_of_isComplex (IsTotallyComplex.isComplex w) z

theorem contDiffAt_logM {z : mixedSpace K} (hz : ∀ w, normAtPlace w z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (logM (K := K)) z := by
  refine contDiffAt_pi.2 fun w => ?_
  have hw := hz w
  rw [normAtPlace_eq_norm_snd] at hw
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : mixedSpace K => ‖z.2 ⟨w, IsTotallyComplex.isComplex w⟩‖)
      z := by
    have hn := contDiffAt_norm ℝ (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (norm_ne_zero_iff.1 hw)
    have hp : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : mixedSpace K => z.2 ⟨w, IsTotallyComplex.isComplex w⟩) :=
      (contDiff_apply ℝ ℂ _).comp contDiff_snd
    exact hn.comp z hp.contDiffAt
  have h2 := (Real.contDiffAt_log.2 hw).comp z h1
  have h3 := contDiffAt_const (c := (w.mult : ℝ)).mul h2
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
  simp only [logM, normAtPlace_eq_norm_snd, Function.comp_apply]

variable {Φ : realSpace K → ℝ}

theorem exists_bound_of_hasCompactSupport (hΦ : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ b, R < ‖b‖ → Φ b = 0 := by
  obtain ⟨R, hR⟩ := hΦ.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun b hb => ?_⟩
  by_contra h
  have := hR (subset_tsupport _ h)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 1]

theorem phiF_eventually_zero (hΦ : HasCompactSupport Φ) {z : mixedSpace K}
    (hz : ¬ ∀ w, normAtPlace w z ≠ 0) : phiF Φ =ᶠ[nhds z] 0 := by
  push Not at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hΦ
  have hm : (1 : ℝ) ≤ w.mult := by exact_mod_cast w.mult_pos
  set ε := Real.exp (-(R + 1))
  have hε : 0 < ε := Real.exp_pos _
  have hcont : Continuous (normAtPlace w : mixedSpace K → ℝ) := continuous_normAtPlace w
  have hU : ∀ᶠ z' in nhds z, normAtPlace w z' < ε :=
    hcont.continuousAt.eventually (gt_mem_nhds (by rw [hw]; exact hε))
  filter_upwards [hU] with z' hz'
  simp only [Pi.zero_apply, phiF]
  split_ifs with h
  · have hpos : 0 < normAtPlace w z' := lt_of_le_of_ne (normAtPlace_nonneg w z') (Ne.symm (h w))
    have hlog : Real.log (normAtPlace w z') < -(R + 1) := by
      rw [Real.log_lt_iff_lt_exp hpos]; exact hz'
    have hb : R < ‖logM z'‖ := by
      have h1 : |logM z' w| ≤ ‖logM z'‖ := by
        have := norm_le_pi_norm (logM z') w
        rwa [Real.norm_eq_abs] at this
      have h2 : R < |logM z' w| := by
        rw [abs_of_neg]
        · simp only [logM]; nlinarith
        · simp only [logM]; nlinarith
      linarith
    rw [hR _ hb]; simp
  · rfl

theorem contDiff_phiF (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (phiF (K := K) Φ) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : ∀ w, normAtPlace w z ≠ 0
  · have hU : ∀ᶠ z' in nhds z, ∀ w, normAtPlace w z' ≠ 0 := by
      refine Filter.eventually_all.2 fun w => ?_
      exact (continuous_normAtPlace w).continuousAt.eventually_ne (hz w)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => ((Φ (logM z') : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z (hΦs.contDiffAt.comp z (contDiffAt_logM hz))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with z' hz'
    exact phiF_of_ne hz'
  · exact contDiffAt_const.congr_of_eventuallyEq (phiF_eventually_zero hΦ hz)

theorem hasCompactSupport_phiF (hΦ : HasCompactSupport Φ) :
    HasCompactSupport (phiF (K := K) Φ) := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hΦ
  have hm : ∀ w : InfinitePlace K, (1 : ℝ) ≤ w.mult := fun w => by exact_mod_cast w.mult_pos
  refine HasCompactSupport.intro (isCompact_closedBall (0 : mixedSpace K) (Real.exp R))
    fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  simp only [phiF]
  split_ifs with h
  · rw [norm_eq_sup'_normAtPlace] at hz
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun w => normAtPlace w z)
    rw [hw] at hz
    have hpos : 0 < normAtPlace w z := lt_of_le_of_ne (normAtPlace_nonneg w z) (Ne.symm (h w))
    have hlog : R < Real.log (normAtPlace w z) := by
      rw [Real.lt_log_iff_exp_lt hpos]; exact hz
    have hb : R < ‖logM z‖ := by
      have h1 : |logM z w| ≤ ‖logM z‖ := by
        have := norm_le_pi_norm (logM z) w
        rwa [Real.norm_eq_abs] at this
      have h2 : R < |logM z w| := by
        rw [abs_of_pos]
        · simp only [logM]; nlinarith [hm w]
        · simp only [logM]; nlinarith [hm w]
      linarith
    rw [hR _ hb]; simp
  · rfl

/-- The radial test function as a Schwartz function. -/
noncomputable def phiS (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ) :
    𝓢(mixedSpace K, ℂ) :=
  (hasCompactSupport_phiF hΦ).toSchwartzMap (contDiff_phiF hΦs hΦ)

@[simp] theorem phiS_apply (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ)
    (z : mixedSpace K) : phiS hΦs hΦ z = phiF Φ z := rfl

end smooth

/-! ### The Fourier transform is radial -/

/-- The radial profile of the Fourier transform. -/
noncomputable def PhiHat (Φ : realSpace K → ℝ) (b : realSpace K) : ℂ :=
  fourierM (phiF Φ) (dilV b)

theorem fourierM_mul_of_norm_eq_one [IsTotallyComplex K] (Φ : realSpace K → ℝ)
    (u u' z : mixedSpace K) (huu' : u * u' = 1) (hu : ∀ w, normAtPlace w u = 1) :
    fourierM (phiF Φ) (u * z) = fourierM (phiF Φ) z := by
  simp only [fourierM, VectorFourier.fourierIntegral]
  have hdet : LinearMap.det (mulL u) = 1 := by
    rw [det_mulL]
    refine Finset.prod_eq_one fun w _ => ?_
    have := hu w.1
    rw [normAtPlace_apply_of_isComplex w.2] at this
    rw [this, one_pow]
  have key := integral_comp_mul (fun v => Real.fourierChar (-(Algebra.traceForm ℝ (mixedSpace K)
    v z)) • phiF Φ v) u u' huu'
  rw [hdet, inv_one, one_smul] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Algebra.traceForm_apply, phiF_mul_of_norm_eq_one Φ u v hu]
  congr 3
  ring

theorem fourierM_eq_PhiHat [IsTotallyComplex K] (Φ : realSpace K → ℝ) {z : mixedSpace K}
    (hz : ∀ w, normAtPlace w z ≠ 0) : fourierM (phiF Φ) z = PhiHat Φ (logM z) := by
  -- `z = u * dilV (logM z)` with `u` of modulus one at every place
  have hd : ∀ w, normAtPlace w (dilV (logM z)) = normAtPlace w z := fun w => by
    rw [normAtPlace_dilV]
    simp only [logM]
    have : (w.mult : ℝ) ≠ 0 := by have := w.mult_pos; positivity
    rw [← mul_assoc, inv_mul_cancel₀ this, one_mul,
      Real.exp_log (lt_of_le_of_ne (normAtPlace_nonneg w z) (Ne.symm (hz w)))]
  have : IsEmpty {w : InfinitePlace K // IsReal w} := isEmpty_isReal
  set u : mixedSpace K := z * dilV (-logM z)
  set zinv : mixedSpace K := (fun w => (z.1 w)⁻¹, fun w => (z.2 w)⁻¹)
  have hz2 : ∀ w : {w : InfinitePlace K // IsComplex w}, z.2 w ≠ 0 := fun w => by
    have := hz w.1
    rw [normAtPlace_apply_of_isComplex w.2] at this
    exact norm_ne_zero_iff.1 this
  have hzz : z * zinv = 1 := by
    ext w
    · exact isEmptyElim w
    · simp only [Prod.snd_mul, Pi.mul_apply, zinv, Prod.snd_one, Pi.one_apply]
      exact mul_inv_cancel₀ (hz2 w)
  have huu : u * (zinv * dilV (logM z)) = 1 := by
    calc u * (zinv * dilV (logM z)) = (z * zinv) * (dilV (-logM z) * dilV (logM z)) := by
          simp only [u]; ring
      _ = 1 := by rw [hzz, dilV_neg_mul, one_mul]
  have hu : ∀ w, normAtPlace w u = 1 := fun w => by
    simp only [u, map_mul, normAtPlace_dilV]
    rw [← hd w, normAtPlace_dilV, ← Real.exp_add]
    simp
  have hzu : z = u * dilV (logM z) := by
    simp only [u]; rw [mul_assoc, dilV_neg_mul, mul_one]
  rw [PhiHat]
  conv_lhs => rw [hzu]
  exact fourierM_mul_of_norm_eq_one Φ u _ _ huu hu

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Radial: integrals of radial functions in log coordinates

For `K` totally complex and `f z = F (logM z)` off the coordinate hyperplanes,
`∫ f = π^{r₂} ∫ e^{Σ b} F(b) db` (polar coordinates, then `r_w = exp (b_w / 2)`).
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

theorem prod_complex_eq {M : Type*} [CommMonoid M] (g : InfinitePlace K → M) :
    ∏ w : {w : InfinitePlace K // IsComplex w}, g w.1 = ∏ w, g w :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _
    fun _ => rfl

theorem mult_eq_two (w : InfinitePlace K) : w.mult = 2 :=
  mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩

theorem expMap_image_univ :
    (expMap : OpenPartialHomeomorph (realSpace K) (realSpace K)) '' Set.univ =
      Set.univ.pi fun w : InfinitePlace K => if w.IsReal then Set.univ else Set.Ioi 0 := by
  rw [← expMap_source K, OpenPartialHomeomorph.image_source_eq_target, expMap_target]
  congr 1
  funext w
  rw [if_neg (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]

theorem abs_det_fderiv_expMap (b : realSpace K) :
    |(fderiv_expMap b).det| = (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.exp (2⁻¹ * ∑ w, b w) := by
  rw [ContinuousLinearMap.det, fderiv_expMap]
  simp_rw [ContinuousLinearMap.coe_pi, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_proj, LinearMap.det_pi, LinearMap.det_ring,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul, deriv_expMap_single, expMap_single_apply]
  rw [← prod_complex_eq (fun w => Real.exp ((w.mult : ℝ)⁻¹ * b w) * (w.mult : ℝ)⁻¹)]
  simp only [mult_isComplex, Nat.cast_ofNat]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
    ← Finset.mul_sum, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_of_pos (by norm_num),
    mul_comm]
  congr 3
  exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _
      fun _ => rfl

theorem normAtPlace_polarSpaceCoord_symm (x : polarSpace K) (hx : ∀ w, 0 < x.1 w)
    (w : InfinitePlace K) : normAtPlace w ((polarSpaceCoord K).symm x) = x.1 w := by
  have hw := IsTotallyComplex.isComplex w
  have h := congrFun (normAtComplexPlaces_polarSpaceCoord_symm (K := K) x) w
  rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, normAtComplexPlaces_apply_isComplex ⟨w, hw⟩]
    at h
  rw [normAtPlace_apply_of_isComplex hw, h, ← normAtPlace_apply_of_isComplex hw,
    normAtPlace_mixedSpaceOfRealSpace (hx w).le]

theorem volume_real_angles :
    (volume : Measure ({w : InfinitePlace K // IsComplex w} → ℝ)).real
      (Set.univ.pi fun _ => Set.Ioo (-π) π) = (2 * π) ^ nrComplexPlaces K := by
  rw [measureReal_def, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ioo, sub_neg_eq_add, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  congr 1; ring

/-- Integration of radial functions. -/
theorem integral_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) (F : realSpace K → E)
    (hf : ∀ z, (∀ w, normAtPlace w z ≠ 0) → f z = F (logM z)) :
    ∫ z, f z = (π ^ nrComplexPlaces K : ℝ) • ∫ b, Real.exp (∑ w, b w) • F b := by
  set H : realSpace K → E := fun r =>
    (∏ w : {w : InfinitePlace K // IsComplex w}, r w.1) • F (fun w => (w.mult : ℝ) * Real.log (r w))
  set A : Set (realSpace K) :=
    Set.univ.pi fun w : InfinitePlace K => if w.IsReal then Set.univ else Set.Ioi 0
  set B : Set ({w : InfinitePlace K // IsComplex w} → ℝ) := Set.univ.pi fun _ => Set.Ioo (-π) π
  have hA : ∀ r ∈ A, ∀ w, 0 < r w := fun r hr w => by
    have := hr w (Set.mem_univ w)
    simp only at this
    rwa [if_neg (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))] at this
  have hmeas : MeasurableSet (A ×ˢ B) := by
    refine (MeasurableSet.univ_pi fun w => ?_).prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    split_ifs
    · exact MeasurableSet.univ
    · exact measurableSet_Ioi
  rw [← integral_comp_polarSpaceCoord_symm, polarSpaceCoord_target']
  rw [setIntegral_congr_fun hmeas (g := fun x => H x.1) fun x hx => by
    have hx1 := hA x.1 hx.1
    have hn := normAtPlace_polarSpaceCoord_symm x hx1
    simp only [H]
    rw [hf _ fun w => by rw [hn]; exact (hx1 w).ne']
    congr 2
    funext w
    simp only [logM, hn]]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_fst,
    measureReal_restrict_apply_univ, volume_real_angles]
  rw [show A = expMap '' Set.univ from expMap_image_univ.symm, integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x _ => (hasFDerivAt_expMap x).hasFDerivWithinAt) (injective_expMap K).injOn,
    Measure.restrict_univ, ← integral_smul, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [H, abs_det_fderiv_expMap, smul_smul]
  have hlog : (fun w => (w.mult : ℝ) * Real.log (expMap b w)) = b := by
    funext w
    rw [expMap_apply, Real.log_exp, ← mul_assoc, mul_inv_cancel₀ mult_coe_ne_zero, one_mul]
  rw [hlog]
  congr 1
  rw [prod_complex_eq (fun w => expMap b w)]
  simp only [expMap_apply]
  rw [← Real.exp_sum]
  simp only [mult_eq_two, Nat.cast_ofNat, ← Finset.mul_sum]
  rw [mul_assoc, ← Real.exp_add, ← add_mul, show (2⁻¹ : ℝ) + 2⁻¹ = 1 by norm_num, one_mul,
    ← mul_assoc, ← mul_pow, mul_comm (2 : ℝ) π, mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Zeta: log-profiles of Schwartz functions and their zeta integrals

For `h` Schwartz on the mixed space, `prof h b = h (dilV b)` decays like `∏_w (1 + e^{b_w/2})^{-N}`
for every `N`, so `Zm h s = ∫ prof h b · e^{s Σ b} db` converges and is holomorphic on `Re s > 0`,
bounded on vertical strips.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- The log-profile of a function on the mixed space. -/
noncomputable def prof (h : mixedSpace K → ℂ) (b : realSpace K) : ℂ := h (dilV b)

/-- The zeta integral of the log-profile. -/
noncomputable def Zm (h : mixedSpace K → ℂ) (s : ℂ) : ℂ :=
  ∫ b, prof h b * Complex.exp (s * ∑ w, (b w : ℂ))

theorem continuous_dilV : Continuous (dilV (K := K)) :=
  mixedSpaceOfRealSpace.continuous.comp (continuous_expMap K)

/-- The one-dimensional majorant `((1 + e^{t/2})^N)⁻¹ e^{σ t}`. -/
noncomputable def maj1 (N : ℕ) (σ t : ℝ) : ℝ := ((1 + Real.exp (t / 2)) ^ N)⁻¹ * Real.exp (σ * t)

theorem maj1_nonneg (N : ℕ) (σ t : ℝ) : 0 ≤ maj1 N σ t := by unfold maj1; positivity

theorem integrable_maj1 {N : ℕ} {σ : ℝ} (hσ : 0 < σ) (hN : 2 * σ < N) :
    Integrable (maj1 N σ) := by
  have hcont : Continuous (maj1 N σ) := by
    unfold maj1
    exact ((continuous_const.add (Real.continuous_exp.comp (continuous_id.div_const 2 : Continuous fun t : ℝ => t / 2))).pow N).inv₀
      (fun t => pow_ne_zero _ (by positivity : (0:ℝ) < 1 + Real.exp (t / 2)).ne') |>.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic hσ 0).mono' hcont.aestronglyMeasurable.restrict ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (maj1_nonneg _ _ _)]
    unfold maj1
    have : 1 ≤ (1 + Real.exp (t / 2)) ^ N := one_le_pow₀ (by linarith [Real.exp_pos (t / 2)])
    calc ((1 + Real.exp (t / 2)) ^ N)⁻¹ * Real.exp (σ * t) ≤ 1 * Real.exp (σ * t) := by
          gcongr; exact inv_le_one_of_one_le₀ this
      _ = _ := one_mul _
  · have ha : σ - N / 2 < 0 := by linarith
    refine (integrableOn_exp_mul_Ioi ha 0).mono' hcont.aestronglyMeasurable.restrict ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (maj1_nonneg _ _ _)]
    unfold maj1
    have h1 : Real.exp (N * (t / 2)) ≤ (1 + Real.exp (t / 2)) ^ N := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) N
    calc ((1 + Real.exp (t / 2)) ^ N)⁻¹ * Real.exp (σ * t)
        ≤ (Real.exp (N * (t / 2)))⁻¹ * Real.exp (σ * t) := by
          gcongr
      _ = Real.exp ((σ - N / 2) * t) := by
          rw [← Real.exp_neg, ← Real.exp_add]; ring_nf

/-- The majorant on `realSpace K`. -/
noncomputable def maj (N : ℕ) (σ : ℝ) (b : realSpace K) : ℝ := ∏ w, maj1 N σ (b w)

theorem integrable_maj {N : ℕ} {σ : ℝ} (hσ : 0 < σ) (hN : 2 * σ < N) :
    Integrable (maj (K := K) N σ) := by
  have := Integrable.fintype_prod (ι := InfinitePlace K) (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ => maj1 N σ) fun _ => integrable_maj1 hσ hN
  rw [volume_pi]
  exact this

theorem maj_eq (N : ℕ) (σ : ℝ) (b : realSpace K) :
    maj N σ b = (∏ w, ((1 + Real.exp (b w / 2)) ^ N)⁻¹) * Real.exp (σ * ∑ w, b w) := by
  simp only [maj, maj1, Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]

variable [IsTotallyComplex K]

theorem normAtPlace_dilV_le_norm (b : realSpace K) (w : InfinitePlace K) :
    Real.exp (b w / 2) ≤ ‖dilV b‖ := by
  have h := normAtPlace_dilV b w
  rw [mult_eq_two] at h
  rw [norm_eq_sup'_normAtPlace]
  refine le_trans ?_ (Finset.le_sup' (fun w => normAtPlace w (dilV b)) (Finset.mem_univ w))
  rw [h]; simp [div_eq_inv_mul]

/-- Schwartz decay in log coordinates. -/
theorem exists_bound_prof (h : 𝓢(mixedSpace K, ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b, ‖prof h b‖ ≤ C * ∏ w, ((1 + Real.exp (b w / 2)) ^ N)⁻¹ := by
  set k := N * Fintype.card (InfinitePlace K)
  set C := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h
  refine ⟨C, by positivity, fun b => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl h
    (dilV b)
  rw [norm_iteratedFDeriv_zero] at h1
  have hprod : ∏ w, (1 + Real.exp (b w / 2)) ^ N ≤ (1 + ‖dilV b‖) ^ k := by
    rw [Finset.prod_pow, show k = Fintype.card (InfinitePlace K) * N by ring, pow_mul]
    gcongr
    calc ∏ w, (1 + Real.exp (b w / 2)) ≤ ∏ _w : InfinitePlace K, (1 + ‖dilV b‖) :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            fun w _ => by linarith [normAtPlace_dilV_le_norm b w]
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hpos : 0 < ∏ w, (1 + Real.exp (b w / 2)) ^ N := by positivity
  rw [Finset.prod_inv_distrib, prof, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h (dilV b)‖ * ∏ w, (1 + Real.exp (b w / 2)) ^ N ≤ ‖h (dilV b)‖ * (1 + ‖dilV b‖) ^ k := by
        gcongr
    _ ≤ C := by rw [mul_comm]; exact h1

theorem continuous_prof (h : 𝓢(mixedSpace K, ℂ)) : Continuous (prof (⇑h)) :=
  h.continuous.comp continuous_dilV

/-- `‖prof h b‖ e^{σ Σ b}` is dominated by a multiple of `maj N σ`. -/
theorem exists_bound_prof_exp (h : 𝓢(mixedSpace K, ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ b, ‖prof h b‖ * Real.exp (σ * ∑ w, b w) ≤ C * maj N σ b := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_prof h N
  refine ⟨C, hC0, fun σ b => ?_⟩
  rw [maj_eq, ← mul_assoc]
  gcongr
  exact hC b

theorem integrable_prof_exp (h : 𝓢(mixedSpace K, ℂ)) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun b : realSpace K => ‖prof h b‖ * Real.exp (σ * ∑ w, b w)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * σ)
  obtain ⟨C, -, hC⟩ := exists_bound_prof_exp h N
  refine ((integrable_maj (K := K) hσ hN).const_mul C).mono' ?_ ?_
  · exact ((continuous_prof h).norm.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_finsetSum _ fun w _ => continuous_apply w)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun b => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hC σ b

theorem norm_cexp_sum (s : ℂ) (b : realSpace K) :
    ‖Complex.exp (s * ∑ w, (b w : ℂ))‖ = Real.exp (s.re * ∑ w, b w) := by
  rw [Complex.norm_exp]
  congr 1
  rw [← Complex.ofReal_sum, Complex.re_mul_ofReal]

theorem integrable_Zm (h : 𝓢(mixedSpace K, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun b : realSpace K => prof h b * Complex.exp (s * ∑ w, (b w : ℂ))) := by
  refine (integrable_prof_exp h hs).mono' ?_ ?_
  · exact ((continuous_prof h).mul (Complex.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun w _ => Complex.continuous_ofReal.comp (continuous_apply w)))))
      |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun b => by rw [norm_mul, norm_cexp_sum]

/-- The zeta integral is bounded on vertical strips. -/
theorem norm_Zm_le (h : 𝓢(mixedSpace K, ℂ)) {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Zm h s‖ ≤ C := by
  refine ⟨∫ x, ‖prof h x‖ * Real.exp (a * ∑ w, x w) + ‖prof h x‖ * Real.exp (b * ∑ w, x w),
    fun s h1 h2 => ?_⟩
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((integrable_prof_exp h ha).add (integrable_prof_exp h (ha.trans_le (h1.trans h2)))) ?_)
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [norm_mul, norm_cexp_sum]
  rw [← mul_add]
  gcongr
  rcases le_or_gt 0 (∑ w, x w) with hx | hx
  · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 hx)
    linarith [Real.exp_pos (a * ∑ w, x w)]
  · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 hx.le)
    linarith [Real.exp_pos (b * ∑ w, x w)]

theorem abs_mul_exp_le {σ σ₀ δ t : ℝ} (hδ : 0 < δ) (h1 : σ₀ - δ < σ) (h2 : σ < σ₀ + δ) :
    |t| * Real.exp (σ * t) ≤ δ⁻¹ * (Real.exp ((σ₀ + 2 * δ) * t) + Real.exp ((σ₀ - 2 * δ) * t)) := by
  have ht : |t| ≤ δ⁻¹ * Real.exp (δ * |t|) := by
    rw [le_inv_mul_iff₀ hδ]
    linarith [Real.add_one_le_exp (δ * |t|)]
  calc |t| * Real.exp (σ * t) ≤ δ⁻¹ * Real.exp (δ * |t|) * Real.exp (σ * t) := by gcongr
    _ = δ⁻¹ * Real.exp (δ * |t| + σ * t) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := by
      gcongr
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
        have : Real.exp (δ * t + σ * t) ≤ Real.exp ((σ₀ + 2 * δ) * t) := Real.exp_le_exp.2 (by nlinarith)
        linarith [Real.exp_pos ((σ₀ - 2 * δ) * t)]
      · rw [abs_of_neg ht]
        have : Real.exp (δ * -t + σ * t) ≤ Real.exp ((σ₀ - 2 * δ) * t) := Real.exp_le_exp.2 (by nlinarith)
        linarith [Real.exp_pos ((σ₀ + 2 * δ) * t)]

theorem differentiableOn_Zm (h : 𝓢(mixedSpace K, ℂ)) :
    DifferentiableOn ℂ (Zm h) {s | 0 < s.re} := by
  intro s₀ hs₀
  have hσ : 0 < s₀.re := hs₀
  set δ := s₀.re / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hcs : ∀ s : ℂ, Continuous fun b : realSpace K => Complex.exp (s * ∑ w, (b w : ℂ)) :=
    fun s => Complex.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun w _ => Complex.continuous_ofReal.comp (continuous_apply w)))
  have hsum : Continuous fun b : realSpace K => ∑ w, (b w : ℂ) :=
    continuous_finsetSum _ fun w _ => Complex.continuous_ofReal.comp (continuous_apply w)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (realSpace K)))
    (x₀ := s₀) (F := fun s b => prof h b * Complex.exp (s * ∑ w, (b w : ℂ)))
    (F' := fun s b => prof h b * ((∑ w, (b w : ℂ)) * Complex.exp (s * ∑ w, (b w : ℂ))))
    (bound := fun b => δ⁻¹ * (‖prof h b‖ * Real.exp ((s₀.re + 2 * δ) * ∑ w, b w) +
      ‖prof h b‖ * Real.exp ((s₀.re - 2 * δ) * ∑ w, b w)))
    (Metric.ball_mem_nhds s₀ hδ0)
    (Filter.Eventually.of_forall fun s => ((continuous_prof h).mul (hcs s)).aestronglyMeasurable)
    (integrable_Zm h hσ)
    (((continuous_prof h).mul (hsum.mul (hcs s₀))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b s hs => by
      rw [Metric.mem_ball, Complex.dist_eq] at hs
      have hre : |s.re - s₀.re| < δ := by
        have := Complex.abs_re_le_norm (s - s₀)
        rw [Complex.sub_re] at this; linarith
      rw [abs_lt] at hre
      rw [norm_mul, norm_mul, norm_cexp_sum, ← Complex.ofReal_sum, Complex.norm_real,
        Real.norm_eq_abs]
      have := abs_mul_exp_le (σ := s.re) (σ₀ := s₀.re) (t := ∑ w, b w) hδ0 (by linarith) (by linarith)
      calc ‖prof h b‖ * (|∑ w, b w| * Real.exp (s.re * ∑ w, b w))
          ≤ ‖prof h b‖ * (δ⁻¹ * (Real.exp ((s₀.re + 2 * δ) * ∑ w, b w) +
            Real.exp ((s₀.re - 2 * δ) * ∑ w, b w))) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring)
    (((integrable_prof_exp h (by linarith)).add (integrable_prof_exp h (by linarith))).const_mul _)
    (Filter.Eventually.of_forall fun b s _ => by
      have := ((hasDerivAt_id s).mul_const (∑ w, (b w : ℂ))).cexp
      simp only [id, one_mul] at this
      have := this.const_mul (prof h b)
      rw [show (∑ w, (b w : ℂ)) * Complex.exp (s * ∑ w, (b w : ℂ)) =
        Complex.exp (s * ∑ w, (b w : ℂ)) * ∑ w, (b w : ℂ) from mul_comm _ _]
      exact this)
  exact key.2.differentiableAt.differentiableWithinAt

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Exch: the exchange identity and `Z(φ̂, 1/6) ≠ 0`

For the radial test function `φ = phiF Φ`, Fubini and Fourier inversion (a79f4737) give
`∫ φ̂(y_b v) φ̂(v) dv = c ∫ φ(u) φ(y_b u) du` with `c > 0`; integrating against `e^{s Σ b}` in log
coordinates gives `Z(φ̂, s) Z(φ̂, 1 − s) = c Z(φ, s) Z(φ, 1 − s)` for `0 < s < 1`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

/-- The Fourier transform of a Schwartz function on the mixed space, as a Schwartz function. -/
noncomputable def fourierS (f : 𝓢(mixedSpace K, ℂ)) : 𝓢(mixedSpace K, ℂ) :=
  (SchwartzMap.exists_coe_eq_vectorFourierIntegral volume (Algebra.traceForm ℝ (mixedSpace K))
    (traceForm_mixedSpace_nondegenerate K) f).choose

theorem coe_fourierS (f : 𝓢(mixedSpace K, ℂ)) : ⇑(fourierS f) = fourierM f :=
  (SchwartzMap.exists_coe_eq_vectorFourierIntegral volume (Algebra.traceForm ℝ (mixedSpace K))
    (traceForm_mixedSpace_nondegenerate K) f).choose_spec

theorem traceForm_flip :
    (Algebra.traceForm ℝ (mixedSpace K)).flip = Algebra.traceForm ℝ (mixedSpace K) := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change Algebra.traceForm ℝ (mixedSpace K) y x = _
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]

/-- The constant of Fourier inversion on the mixed space. -/
noncomputable def invC (K : Type*) [Field K] [NumberField K] : ℝ :=
  let b := Module.finBasis ℝ (mixedSpace K)
  (volume.real (ZSpan.fundamentalDomain b)) ^ 2 /
    |(Matrix.of fun i j => Algebra.traceForm ℝ (mixedSpace K) (b i) (b j)).det|

theorem invC_ne_zero : invC K ≠ 0 := by
  unfold invC
  set b := Module.finBasis ℝ (mixedSpace K)
  have h1 : (Matrix.of fun i j => Algebra.traceForm ℝ (mixedSpace K) (b i) (b j)).det ≠ 0 := by
    have := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
      (traceForm_mixedSpace_nondegenerate K)
    convert this using 2
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply]
  have h2 : volume.real (ZSpan.fundamentalDomain b) ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨ZSpan.measure_fundamentalDomain_ne_zero b,
      (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne⟩
  exact div_ne_zero (pow_ne_zero 2 h2) (abs_ne_zero.2 h1)

theorem fourierM_fourierM (f : 𝓢(mixedSpace K, ℂ)) (x : mixedSpace K) :
    fourierM (fourierM f) x = invC K * f (-x) := by
  have := VectorFourier.fourierIntegral_flip_fourierIntegral_eq volume
    (Algebra.traceForm ℝ (mixedSpace K)) (traceForm_mixedSpace_nondegenerate K)
    (Module.finBasis ℝ (mixedSpace K)) f x
  rw [traceForm_flip] at this
  exact this

/-- Fubini: the pairing of `φ̂(y ·)` with `φ̂` equals the pairing of `φ` with `φ̂̂(y ·)`. -/
theorem integral_fourierM_mul_fourierS (f : 𝓢(mixedSpace K, ℂ)) (y : mixedSpace K) :
    ∫ v, fourierM f (y * v) * fourierS f v = ∫ u, f u * fourierM (fourierS f) (y * u) := by
  set B := Algebra.traceForm ℝ (mixedSpace K)
  set g := fourierS f
  have hB : Continuous fun p : mixedSpace K × mixedSpace K => B p.2 (y * p.1) := by
    have ht : Continuous (Algebra.trace ℝ (mixedSpace K)) :=
      LinearMap.continuous_of_finiteDimensional _
    exact ht.comp (continuous_snd.mul (continuous_const.mul continuous_fst))
  have hint : Integrable (fun p : mixedSpace K × mixedSpace K =>
      (Real.fourierChar (-(B p.2 (y * p.1))) : ℂ) • f p.2 * g p.1)
      ((volume : Measure (mixedSpace K)).prod volume) := by
    refine ((g.integrable (μ := volume)).mul_prod (f.integrable (μ := volume))).norm.mono' ?_ ?_
    · exact (((continuous_subtype_val.comp Real.continuous_fourierChar).comp hB.neg).smul
        (f.continuous.comp continuous_snd)).mul (g.continuous.comp continuous_fst)
        |>.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      rw [mul_comm]
  simp only [fourierM, VectorFourier.fourierIntegral]
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hsym : Algebra.traceForm ℝ (mixedSpace K) u (y * v) =
      Algebra.traceForm ℝ (mixedSpace K) v (y * u) := by
    simp only [Algebra.traceForm_apply]; congr 1; ring
  beta_reduce
  rw [hsym]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- `E s b = e^{s Σ b}`. -/
noncomputable def Ex (s : ℂ) (b : realSpace K) : ℂ := Complex.exp (s * ∑ w, (b w : ℂ))

theorem Ex_add (s : ℂ) (b b' : realSpace K) : Ex s (b + b') = Ex s b * Ex s b' := by
  simp only [Ex, Pi.add_apply, Complex.ofReal_add, Finset.sum_add_distrib, mul_add,
    Complex.exp_add]

theorem Ex_mul_Ex (s t : ℂ) (b : realSpace K) : Ex s b * Ex t b = Ex (s + t) b := by
  simp only [Ex, ← Complex.exp_add, add_mul]

theorem Ex_one (b : realSpace K) : Ex 1 b = (Real.exp (∑ w, b w) : ℂ) := by
  simp [Ex, Complex.ofReal_exp]

/-- The shear identity: `∫_b e^{sΣb} ∫_{b'} e^{Σb'} P(b+b') Q(b') = Z(P, s) Z(Q, 1 − s)`. -/
theorem integral_shear (P Q : realSpace K → ℂ) (s : ℂ)
    (hP : Integrable fun c => P c * Ex s c) (hQ : Integrable fun b => Q b * Ex (1 - s) b) :
    ∫ b, Ex s b * ∫ b', (Real.exp (∑ w, b' w) : ℂ) * (P (b + b') * Q b') =
      (∫ c, P c * Ex s c) * ∫ b, Q b * Ex (1 - s) b := by
  set H : realSpace K × realSpace K → ℂ := fun z => (Q z.1 * Ex (1 - s) z.1) * (P z.2 * Ex s z.2)
  have hH : Integrable H ((volume : Measure (realSpace K)).prod volume) := hQ.mul_prod hP
  have hmp := measurePreserving_prod_add (volume : Measure (realSpace K)) (volume : Measure (realSpace K))
  set e := MeasurableEquiv.shearAddRight (realSpace K)
  have hmp' : MeasurePreserving e ((volume : Measure (realSpace K)).prod volume)
      ((volume : Measure (realSpace K)).prod volume) := hmp
  have hG : ∀ z : realSpace K × realSpace K, H (e z) =
      Ex s z.2 * ((Real.exp (∑ w, z.1 w) : ℂ) * (P (z.2 + z.1) * Q z.1)) := by
    intro z
    simp only [H, e, MeasurableEquiv.shearAddRight, MeasurableEquiv.coe_mk, Equiv.prodShear_apply,
      Equiv.coe_refl, id, Equiv.coe_addLeft]
    rw [Ex_add, ← Ex_one, add_comm z.1 z.2]
    have := Ex_mul_Ex (1 - s) s z.1
    rw [sub_add_cancel] at this
    rw [← this]
    ring
  have hGint : Integrable (fun z : realSpace K × realSpace K =>
      Ex s z.2 * ((Real.exp (∑ w, z.1 w) : ℂ) * (P (z.2 + z.1) * Q z.1)))
      ((volume : Measure (realSpace K)).prod volume) := by
    have := (hmp'.integrable_comp_emb e.measurableEmbedding).2 hH
    simpa only [Function.comp_def, hG] using this
  rw [mul_comm, ← integral_prod_mul (fun b => Q b * Ex (1 - s) b) (fun c => P c * Ex s c),
    show (fun z : realSpace K × realSpace K => Q z.1 * Ex (1 - s) z.1 * (P z.2 * Ex s z.2)) = H
      from rfl, ← hmp'.integral_comp', funext hG, integral_prod_symm _ hGint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only []
  rw [← integral_const_mul]

section exchange

variable {Φ : realSpace K → ℝ} (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ)

theorem prof_phiF (b : realSpace K) : prof (phiF Φ) b = Φ b := by
  rw [prof, phiF_of_ne (normAtPlace_dilV_ne_zero b), logM_dilV]

theorem prof_fourierM_phiF (b : realSpace K) : prof (fourierM (phiF Φ)) b = PhiHat Φ b := rfl

include hΦs hΦ in
theorem integral_phi_mul_phi_dil (b : realSpace K) :
    ∫ u, phiF Φ u * phiF Φ (dilV b * u) =
      (π ^ nrComplexPlaces K : ℝ) • ∫ b', Real.exp (∑ w, b' w) • ((Φ (b + b') : ℂ) * Φ b') := by
  refine integral_radial _ _ fun u hu => ?_
  rw [phiF_of_ne hu, phiF_dilV_mul Φ b hu]
  ring

include hΦs hΦ in
theorem integral_fourier_mul_fourier_dil (b : realSpace K) :
    ∫ v, fourierM (phiF Φ) (dilV b * v) * fourierM (phiF Φ) v =
      (π ^ nrComplexPlaces K : ℝ) • ∫ b', Real.exp (∑ w, b' w) • (PhiHat Φ (b + b') * PhiHat Φ b') := by
  refine integral_radial _ _ fun v hv => ?_
  have hv' : ∀ w, normAtPlace w (dilV b * v) ≠ 0 := fun w => by
    rw [map_mul]; exact mul_ne_zero (normAtPlace_dilV_ne_zero b w) (hv w)
  rw [fourierM_eq_PhiHat Φ hv', fourierM_eq_PhiHat Φ hv, logM_dilV_mul b v hv]

include hΦs hΦ in
theorem integral_fourier_pair (b : realSpace K) :
    ∫ v, fourierM (phiF Φ) (dilV b * v) * fourierM (phiF Φ) v =
      invC K * ∫ u, phiF Φ u * phiF Φ (dilV b * u) := by
  set φ := phiS hΦs hΦ
  have h1 := integral_fourierM_mul_fourierS φ (dilV b)
  rw [coe_fourierS] at h1
  have hφ : (⇑φ : mixedSpace K → ℂ) = phiF Φ := rfl
  rw [hφ] at h1
  rw [h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  have hff := fourierM_fourierM φ (dilV b * u)
  rw [hφ] at hff
  rw [hff]
  have hneg : phiF Φ (-(dilV b * u)) = phiF Φ (dilV b * u) := by
    rw [show -(dilV b * u) = (-1) * (dilV b * u) by ring]
    exact phiF_mul_of_norm_eq_one Φ (-1) _ fun w => by rw [normAtPlace_neg, map_one]
  rw [hneg]; ring

include hΦs hΦ in
/-- The exchange identity `Z(φ̂, s) Z(φ̂, 1 − s) = c Z(φ, s) Z(φ, 1 − s)`. -/
theorem Zm_exchange (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Zm (fourierM (phiF Φ)) s * Zm (fourierM (phiF Φ)) (1 - s) =
      invC K * (Zm (phiF Φ) s * Zm (phiF Φ) (1 - s)) := by
  set φ := phiS hΦs hΦ
  have hφ : (⇑φ : mixedSpace K → ℂ) = phiF Φ := rfl
  have hs1' : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hZ : ∀ (h : mixedSpace K → ℂ) (t : ℂ), Zm h t = ∫ c, prof h c * Ex t c := fun _ _ => rfl
  have intF : ∀ t : ℂ, 0 < t.re → Integrable fun c => PhiHat Φ c * Ex t c := fun t ht => by
    have := integrable_Zm (fourierS φ) ht
    rw [coe_fourierS, hφ] at this
    exact this
  have intP : ∀ t : ℂ, 0 < t.re → Integrable fun c => (Φ c : ℂ) * Ex t c := fun t ht => by
    have := integrable_Zm φ ht
    rw [hφ] at this
    have e : (fun c => (Φ c : ℂ) * Ex t c) =
        fun b => prof (phiF Φ) b * Complex.exp (t * ∑ w, (b w : ℂ)) := by
      funext c; rw [prof_phiF]; rfl
    rw [e]; exact this
  have key1 := integral_shear (PhiHat Φ) (PhiHat Φ) s (intF s hs0) (by simpa using intF _ hs1')
  have key2 := integral_shear (fun c => (Φ c : ℂ)) (fun c => (Φ c : ℂ)) s (intP s hs0)
    (by simpa using intP _ hs1')
  have hpi : ((π ^ nrComplexPlaces K : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ Real.pi_ne_zero
  have hA : ∀ b : realSpace K, ∫ b', (Real.exp (∑ w, b' w) : ℂ) * (PhiHat Φ (b + b') * PhiHat Φ b') =
      invC K * ∫ b', (Real.exp (∑ w, b' w) : ℂ) * ((Φ (b + b') : ℂ) * Φ b') := by
    intro b
    have e1 := integral_fourier_mul_fourier_dil hΦs hΦ b
    have e2 := integral_phi_mul_phi_dil hΦs hΦ b
    rw [integral_fourier_pair hΦs hΦ b, e2] at e1
    simp only [Complex.real_smul] at e1
    apply mul_left_cancel₀ hpi
    rw [← e1]; ring
  simp only [hZ, prof_fourierM_phiF, prof_phiF]
  rw [← key1, ← key2]
  simp_rw [hA]
  rw [← integral_const_mul]
  congr 1
  funext b
  ring

end exchange

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L2B_Bound: crude norm bounds for the arithmetic factors

`|e| ≤ 1`, `|χ_𝔞| ≤ 1`, `|g_𝔞(k)| ≤ q_𝔞`, `|γ_j(𝔠)| ≤ q_𝔠^{1/2}`, `|F(𝔰,𝔄,h)| ≤ q_𝔰 q_𝔄`,
`|Λ(𝔞)|, |G(𝔞)| ≤ q_𝔞^{1/2}`, `|ϑ(𝔞)| ≤ q_𝔞`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F]

/-! ### Generic lemmas -/

/-! ### Characters -/

theorem norm_sAddChar_le (𝔪 : Ideal (𝓞 F)) (x : F) : ‖sAddChar 𝔪 x‖ ≤ 1 := by
  unfold sAddChar
  split_ifs
  · rw [Complex.norm_exp]
    simp
  · simp

/-! ### Quotients -/

variable {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-!
# L3P_Theta: Poisson summation over `P^k` with a periodic coefficient

For `c` periodic modulo `𝔫R`,
`Σ_{m ∈ P^j} c(m) φ(y_x m) = (covol(𝔫 P^j) e^{Σx})⁻¹ Σ_{h ∈ P^{val ν − j − δ}} ĉ⁻(h) φ̂(y_x⁻¹ h/ν)`
with `ĉ⁻(h) = Σ_{x mod 𝔫R} c(x) e(−h x / ν)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  FractionalIdeal
open scoped nonZeroDivisors Classical Real SchwartzMap

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- `𝔫 P^j` as a unit fractional ideal. -/
noncomputable def nPk {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (j : SP 𝔪 → ℤ) :
    (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (𝔫 : FractionalIdeal (𝓞 F)⁰ F) (coeIdeal_ne_zero.2 h𝔫.1) * Pk j

theorem coe_nPk {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (j : SP 𝔪 → ℤ) :
    ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      (𝔫 : FractionalIdeal (𝓞 F)⁰ F) * ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
  rw [nPk, Units.val_mul]; rfl

/-- `e` vanishes on `R`. -/
theorem sAddChar_of_mem {r : F} (hr : r ∈ (placesOf 𝔪).integer F) : sAddChar 𝔪 r = 1 := by
  rw [C3I.sAddChar_eq_of_wit (y := 0) (by simpa using hr) (fun v _ => by simp)]
  simp

theorem hasWit_div {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (a : SInt 𝔪) :
    C3I.HasWit 𝔪 ((a : F) / (ν : F)) := by
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  refine C3I.hasWit_of_mul_mem _ 𝔫 h𝔫.2 fun n hn => ?_
  have hn' : algebraMap (𝓞 F) (SInt 𝔪) n ∈ Ideal.span {ν} := hν ▸ Ideal.mem_map_of_mem _ hn
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hn'
  have htF : (t : F) * (ν : F) = algebraMap (𝓞 F) F n := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) ht
    simpa using this
  rw [← htF, show (a : F) / (ν : F) * ((t : F) * (ν : F)) = (a : F) * (t : F) by field_simp]
  exact (a * t).2

theorem mem_dual_mul_rep {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (j : SP 𝔪 → ℤ) {x₀ : F}
    (hx₀ : x₀ ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) {η : F}
    (hη : η ∈ FractionalIdeal.dual ℤ ℚ
      ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
    x₀ * η ∈ FractionalIdeal.dual ℤ ℚ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) := by
  have h𝔫0 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔫.1
  rw [FractionalIdeal.mem_dual h𝔫0]
  intro a ha
  have hmul : a * x₀ ∈ ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [coe_nPk]; exact mul_mem_mul ha hx₀
  have := (FractionalIdeal.mem_dual (nPk h𝔫 j).ne_zero).1 hη (a * x₀) hmul
  rw [Algebra.traceForm_apply] at this ⊢
  rwa [show x₀ * η * a = η * (a * x₀) by ring]

theorem phase_eq (h𝔪 : 𝔪 ≠ ⊥) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (j : SP 𝔪 → ℤ)
    (xc : Qn 𝔪 𝔫) {η : F}
    (hη : η ∈ FractionalIdeal.dual ℤ ℚ
      ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
    (Real.fourierChar ((Algebra.trace ℚ F ((repPk h𝔪 h𝔫 j xc : F) * η) : ℚ) : ℝ) : ℂ) =
      sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) * η) := by
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  rw [fourierChar_trace_eq hD h𝔫 (mem_dual_mul_rep h𝔫 j (repPk_mem h𝔪 h𝔫 j xc) hη)]
  -- `νη ∈ R`
  have hηR : (ν : F) * η ∈ (placesOf 𝔪).integer F := by
    have := (mem_dual_iff hD h𝔫 hν j η).1 (by rw [← coe_nPk]; exact hη)
    exact Pk_subset_SInt _ this
  set h : SInt 𝔪 := ⟨(ν : F) * η, hηR⟩
  have hηh : η = (h : F) / (ν : F) := by
    simp only [h]; field_simp
  -- `rep − ql = ν s`
  have hsub := (exists_rep h𝔪 h𝔫 j (quotLift xc)).choose_spec.2
  have hsub' : quotLift xc - repPk h𝔪 h𝔫 j xc ∈ Ideal.span {ν} := by
    rw [hν, show quotLift xc - repPk h𝔪 h𝔫 j xc = -(repPk h𝔪 h𝔫 j xc - quotLift xc) by ring]
    exact neg_mem hsub
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hsub'
  have hsF : (s : F) * (ν : F) = ((quotLift xc : SInt 𝔪) : F) - (repPk h𝔪 h𝔫 j xc : F) := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hs
    simpa using this
  have hsplit : -((repPk h𝔪 h𝔫 j xc : F) * η) =
      -((quotLift xc : SInt 𝔪) : F) * η + (s : F) * (h : F) := by
    simp only [h]
    have : (s : F) * ((ν : F) * η) = ((quotLift xc : SInt 𝔪) : F) * η - (repPk h𝔪 h𝔫 j xc : F) * η := by
      rw [← mul_assoc, hsF]; ring
    rw [this]; ring
  have hw1 : C3I.HasWit 𝔪 (-((quotLift xc : SInt 𝔪) : F) * η) := by
    have := hasWit_div h𝔫 hν (-(quotLift xc) * h)
    convert this using 1
    rw [hηh]; push_cast; ring
  have hr : (s : F) * (h : F) ∈ (placesOf 𝔪).integer F := (s * h).2
  rw [hsplit, C3I.sAddChar_add hw1 (C3I.hasWit_of_mem hr), sAddChar_of_mem hr, mul_one]

/-- The dual of `𝔫 P^j` as the lattice `P^{val ν − j − δ}`, by `η ↦ ν η`. -/
noncomputable def dualEquivPk (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (j : SP 𝔪 → ℤ) :
    ((FractionalIdeal.dual ℤ ℚ ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) : Set F) ≃
    (((Pk (valS (ν : F) - j - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : Set F) where
  toFun η := ⟨(ν : F) * η, (mem_dual_iff hD h𝔫 hν j η).1 (by rw [← coe_nPk]; exact η.2)⟩
  invFun h := ⟨(h : F) / (ν : F), by
    have hν0 := ne_zero_of_span_eq h𝔫 hν
    have := (mem_dual_iff hD h𝔫 hν j ((h : F) / (ν : F))).2 (by
      rw [mul_div_cancel₀ _ hν0]; exact h.2)
    rw [← coe_nPk] at this; exact this⟩
  left_inv η := by
    have hν0 := ne_zero_of_span_eq h𝔫 hν
    ext; simp only; field_simp
  right_inv h := by
    have hν0 := ne_zero_of_span_eq h𝔫 hν
    ext; simp only; field_simp

variable [IsTotallyComplex F]

/-- **Poisson summation over `P^j`** with an `𝔫R`-periodic coefficient. -/
theorem lattice_poisson (h𝔪 : 𝔪 ≠ ⊥) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    [Fintype (Qn 𝔪 𝔫)] (φ : 𝓢(mixedSpace F, ℂ)) (x : realSpace F) (j : SP 𝔪 → ℤ) :
    ∑' m : (((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F),
        c ⟨m, Pk_subset_SInt j m.2⟩ * φ (dilV x * mixedEmbedding F m) =
      ((ZLattice.covolume (idealLattice F (nPk h𝔫 j)) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
        ∑' h : (((Pk (valS (ν : F) - j - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
            FractionalIdeal (𝓞 F)⁰ F) : Set F),
          (∑ xc : Qn 𝔪 𝔫, c (quotLift xc) *
              sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) * ((h : F) / (ν : F)))) *
            fourierM φ (dilV (-x) * mixedEmbedding F ((h : F) / (ν : F))) := by
  set φx : 𝓢(mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilE x) φ
  have hG : Summable fun m : (((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : Set F) => ‖φ (dilV x * mixedEmbedding F m)‖ := by
    have := summable_schwartz_fractionalIdeal φx (Pk j) 0
    refine this.congr fun m => ?_
    rw [zero_add]
    rfl
  rw [tsum_Pk_eq_sum h𝔪 h𝔫 j c hc (fun m => φ (dilV x * mixedEmbedding F m)) hG]
  -- Poisson for each class
  have hP : ∀ xc : Qn 𝔪 𝔫, ∑' a : ((((𝔫 : FractionalIdeal (𝓞 F)⁰ F) *
      ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
        FractionalIdeal (𝓞 F)⁰ F) : Set F),
        φ (dilV x * mixedEmbedding F ((repPk h𝔪 h𝔫 j xc : F) + a)) =
      ((ZLattice.covolume (idealLattice F (nPk h𝔫 j)) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
        ∑' η : ((FractionalIdeal.dual ℤ ℚ ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
            FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) : Set F),
          fourierM φ (dilV (-x) * mixedEmbedding F η) *
            sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) * η) := by
    intro xc
    have := tsum_dil_eq (nPk h𝔫 j) φ x (repPk h𝔪 h𝔫 j xc : F)
    rw [coe_nPk] at this
    rw [this]
    congr 1
    refine tsum_congr fun η => ?_
    rw [phase_eq h𝔪 hD h𝔫 hν j xc (by rw [coe_nPk]; exact η.2)]
  simp_rw [hP]
  set K0 : ℂ := ((ZLattice.covolume (idealLattice F (nPk h𝔫 j)) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹
  set U : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (FractionalIdeal.dual ℤ ℚ
    ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F))
    (FractionalIdeal.dual_ne_zero ℤ ℚ (nPk h𝔫 j).ne_zero)
  set ψ : 𝓢(mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilE (-x))
    (fourierS φ)
  have hA : Summable fun η : ((FractionalIdeal.dual ℤ ℚ ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) : Set F) =>
      ‖fourierM φ (dilV (-x) * mixedEmbedding F η)‖ := by
    have := summable_schwartz_fractionalIdeal ψ U 0
    refine this.congr fun η => ?_
    rw [zero_add]
    simp only [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      dilE_apply, coe_fourierS]
  have hAB : ∀ xc : Qn 𝔪 𝔫, Summable fun η : ((FractionalIdeal.dual ℤ ℚ
      ((nPk h𝔫 j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
        FractionalIdeal (𝓞 F)⁰ F) : Set F) =>
      c (quotLift xc) * (fourierM φ (dilV (-x) * mixedEmbedding F η) *
        sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) * η)) := by
    intro xc
    refine Summable.of_norm_bounded (hA.mul_left ‖c (quotLift xc)‖) fun η => ?_
    rw [norm_mul, norm_mul]
    have := L2B.norm_sAddChar_le 𝔪 (-((quotLift xc : SInt 𝔪) : F) * η)
    gcongr
    calc ‖fourierM φ (dilV (-x) * mixedEmbedding F η)‖ * ‖sAddChar 𝔪 _‖ ≤
        ‖fourierM φ (dilV (-x) * mixedEmbedding F η)‖ * 1 := by gcongr
      _ = _ := mul_one _
  simp_rw [← mul_assoc (c _) K0, mul_comm (c _) K0, mul_assoc K0]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun xc _ => hAB xc]
  rw [← (dualEquivPk hD h𝔫 hν j).tsum_eq]
  refine tsum_congr fun η => ?_
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  have hdiv : ((dualEquivPk hD h𝔫 hν j η : F)) / (ν : F) = η := by
    simp only [dualEquivPk, Equiv.coe_fn_mk]; field_simp
  rw [hdiv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun xc _ => ?_
  ring

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Phi: the concrete test function

`Φ(b) = χ(Σ_w b_w) · ∏_{w ≠ w₀} β(b_w)` with `β` a bump at `0` and `χ(t) = β(t) − e^{−1} β(t − 1)`.
Then `∫ Φ(b) G(Σ b) db = c_β ∫ χ(t) G(t) dt`, so `Z(φ, s) = c_β (1 − e^{s−1}) ∫ β(t) e^{st} dt`:
it vanishes at `s = 1` (`∫ φ = 0`, hence `φ̂(0) = 0`) and not at `s = 1/6, 5/6`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

/-- The bump at `0` with radii `1/2 < 1`. -/
noncomputable def bump0 : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The bump function `β`. -/
noncomputable def bb (t : ℝ) : ℝ := bump0 t

theorem bb_nonneg (t : ℝ) : 0 ≤ bb t := bump0.nonneg

theorem contDiff_bb : ContDiff ℝ (⊤ : ℕ∞) bb := bump0.contDiff

theorem continuous_bb : Continuous bb := bump0.continuous

theorem hasCompactSupport_bb : HasCompactSupport bb := bump0.hasCompactSupport

theorem bb_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : bb t = 0 :=
  bump0.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)

theorem bb_zero : bb 0 = 1 := bump0.one_of_mem_closedBall (by simp [bump0])

/-- `χ(t) = β(t) − e^{−1} β(t − 1)`. -/
noncomputable def chi (t : ℝ) : ℝ := bb t - Real.exp (-1) * bb (t - 1)

theorem contDiff_chi : ContDiff ℝ (⊤ : ℕ∞) chi :=
  contDiff_bb.sub (contDiff_const.mul (contDiff_bb.comp (contDiff_id.sub contDiff_const)))

theorem continuous_chi : Continuous chi := contDiff_chi.continuous

theorem chi_eq_zero {t : ℝ} (ht : t ≤ -1 ∨ 2 ≤ t) : chi t = 0 := by
  unfold chi
  rcases ht with ht | ht
  · rw [bb_eq_zero (by rw [abs_of_neg (by linarith)]; linarith),
      bb_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)]; ring
  · rw [bb_eq_zero (by rw [abs_of_pos (by linarith)]; linarith),
      bb_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)]; ring

/-- `B(s) = ∫ β(t) e^{st} dt`. -/
noncomputable def Bint (s : ℂ) : ℂ := ∫ t : ℝ, (bb t : ℂ) * Complex.exp (s * t)

theorem integrable_bb_exp (s : ℂ) : Integrable fun t : ℝ => (bb t : ℂ) * Complex.exp (s * t) := by
  refine Continuous.integrable_of_hasCompactSupport ((Complex.continuous_ofReal.comp continuous_bb).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) ?_
  exact (hasCompactSupport_bb.comp_left Complex.ofReal_zero).mul_right

theorem integral_chi_exp (s : ℂ) :
    ∫ t : ℝ, (chi t : ℂ) * Complex.exp (s * t) = (1 - Complex.exp (s - 1)) * Bint s := by
  have h1 : ∫ t : ℝ, (bb (t - 1) : ℂ) * Complex.exp (s * t) = Complex.exp s * Bint s := by
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => (bb t : ℂ) * Complex.exp (s * ((t : ℂ) + 1))) 1
    have e : (fun t : ℝ => (bb (t - 1) : ℂ) * Complex.exp (s * t)) =
        fun t : ℝ => (fun t : ℝ => (bb t : ℂ) * Complex.exp (s * ((t : ℂ) + 1))) (t - 1) := by
      funext t; simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_add_cancel]
    rw [e, this, Bint, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [mul_add, mul_one, Complex.exp_add]
    ring
  simp only [chi, Complex.ofReal_sub, Complex.ofReal_mul, sub_mul]
  rw [integral_sub (integrable_bb_exp s), ← Bint]
  · simp_rw [mul_assoc]
    rw [integral_const_mul, h1, Complex.exp_sub, Complex.ofReal_exp]
    push_cast
    rw [Complex.exp_neg]
    field_simp
  · have := (integrable_bb_exp s).comp_sub_right 1
    have h2 := this.const_mul ((Real.exp (-1) : ℂ) * Complex.exp s)
    refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    rw [show s * ((t : ℂ) - 1) = s * t - s by ring, Complex.exp_sub]
    field_simp

theorem Bint_ofReal_pos (σ : ℝ) : 0 < (Bint σ).re ∧ (Bint σ).im = 0 := by
  have hB : Bint σ = ((∫ t : ℝ, bb t * Real.exp (σ * t) : ℝ) : ℂ) := by
    rw [Bint, ← integral_complex_ofReal]
    congr 1; funext t; push_cast; rfl
  rw [hB, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (continuous_bb.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    hasCompactSupport_bb.mul_right (fun t => mul_nonneg (bb_nonneg t) (Real.exp_pos _).le)
    (x := 0) (by rw [bb_zero]; simp)

theorem Bint_ofReal_ne_zero (σ : ℝ) : Bint σ ≠ 0 := fun h => by
  have := (Bint_ofReal_pos σ).1; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this

section split

variable {K : Type*} [Field K] [NumberField K]

/-- A fixed infinite place. -/
noncomputable def w0 (K : Type*) [Field K] [NumberField K] : InfinitePlace K :=
  Classical.arbitrary _

/-- The test function `Φ(b) = χ(Σ b) ∏_{w ≠ w₀} β(b_w)`. -/
noncomputable def PhiT (b : realSpace K) : ℝ :=
  chi (∑ w, b w) * ∏ w : {w : InfinitePlace K // w ≠ w0 K}, bb (b w)

theorem contDiff_PhiT : ContDiff ℝ (⊤ : ℕ∞) (PhiT (K := K)) := by
  refine (contDiff_chi.comp (ContDiff.sum fun w _ => contDiff_apply ℝ ℝ w)).mul ?_
  exact contDiff_prod fun w _ => contDiff_bb.comp (contDiff_apply ℝ ℝ w.1)

theorem hasCompactSupport_PhiT : HasCompactSupport (PhiT (K := K)) := by
  set R : ℝ := Fintype.card (InfinitePlace K) + 2
  refine HasCompactSupport.intro (isCompact_closedBall (0 : realSpace K) R) fun b hb => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hb
  by_contra h
  have h1 : ∀ w : {w : InfinitePlace K // w ≠ w0 K}, |b w| < 1 := fun w => by
    by_contra hw
    apply h; rw [PhiT, Finset.prod_eq_zero (Finset.mem_univ w) (bb_eq_zero (not_lt.1 hw)), mul_zero]
  have h2 : -1 < ∑ w, b w ∧ ∑ w, b w < 2 := by
    by_contra hw
    apply h
    rw [not_and_or, not_lt, not_lt] at hw
    rw [PhiT, chi_eq_zero hw, zero_mul]
  have hS : |∑ w : {w : InfinitePlace K // w ≠ w0 K}, b w| ≤ Fintype.card (InfinitePlace K) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : {w : InfinitePlace K // w ≠ w0 K}, |b w| ≤ ∑ _w : {w : InfinitePlace K // w ≠ w0 K}, (1 : ℝ) :=
          Finset.sum_le_sum fun w _ => (h1 w).le
      _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact_mod_cast Fintype.card_subtype_le _
  have h3 := Fintype.sum_eq_add_sum_subtype_ne b (w0 K)
  have hle : ‖b‖ ≤ R := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
    rw [Real.norm_eq_abs]
    by_cases hw : w = w0 K
    · subst hw
      rw [abs_le] at hS ⊢
      constructor <;> linarith [hS.1, hS.2, h2.1, h2.2]
    · have := h1 ⟨w, hw⟩
      simp only [R]
      linarith
  linarith

/-- `c_β = ∫ β`. -/
noncomputable def cB : ℝ := ∫ t, bb t

theorem cB_pos : 0 < cB :=
  Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero continuous_bb hasCompactSupport_bb
    bb_nonneg (x := 0) (by rw [bb_zero]; simp)

/-- The split: `∫ Φ(b) G(Σ b) db = c_β^{r−1} ∫ χ(t) G(t) dt`. -/
theorem integral_PhiT_mul (G : ℝ → ℂ) (hG : Continuous G) :
    ∫ b : realSpace K, (PhiT b : ℂ) * G (∑ w, b w) =
      (cB : ℂ) ^ Fintype.card {w : InfinitePlace K // w ≠ w0 K} * ∫ t, (chi t : ℂ) * G t := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w0 K)
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w0 K)
  set F : realSpace K → ℂ := fun b => (PhiT b : ℂ) * G (∑ w, b w)
  have hF : Integrable F := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp contDiff_PhiT.continuous).mul
        (hG.comp (continuous_finsetSum _ fun w _ => continuous_apply w))
    · exact (hasCompactSupport_PhiT.comp_left Complex.ofReal_zero).mul_right
  have hsum : ∀ z : ({w : InfinitePlace K // w = w0 K} → ℝ) × ({w : InfinitePlace K // ¬ w = w0 K} → ℝ),
      ∑ w, e.symm z w = z.1 ⟨w0 K, rfl⟩ + ∑ w : {w : InfinitePlace K // w ≠ w0 K}, z.2 w := by
    intro z
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w0 K)]
    congr 1
    · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
    · refine Finset.sum_congr rfl fun w _ => ?_
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, w.2]
  have hprod : ∀ z : ({w : InfinitePlace K // w = w0 K} → ℝ) × ({w : InfinitePlace K // ¬ w = w0 K} → ℝ),
      ∏ w : {w : InfinitePlace K // w ≠ w0 K}, bb (e.symm z w) = ∏ w : {w : InfinitePlace K // w ≠ w0 K}, bb (z.2 w) := by
    intro z
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, w.2]
  rw [← he.symm.integral_comp' F]
  have hint := (he.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod] at hint ⊢
  have hps := integral_prod_symm _ hint
  simp only [Function.comp_def] at hps
  rw [hps]
  let _ : Unique {w : InfinitePlace K // w = w0 K} := ⟨⟨⟨w0 K, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  have hu := volume_preserving_funUnique {w : InfinitePlace K // w = w0 K} ℝ
  refine (integral_congr_ae (g := fun y : {w : InfinitePlace K // ¬ w = w0 K} → ℝ =>
    (∏ w : {w : InfinitePlace K // w ≠ w0 K}, (bb (y w) : ℂ)) * ∫ t, (chi t : ℂ) * G t)
    (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · set S := ∑ w : {w : InfinitePlace K // w ≠ w0 K}, y w
    have h1 : ∀ x : {w : InfinitePlace K // w = w0 K} → ℝ, F (e.symm (x, y)) =
        (∏ w : {w : InfinitePlace K // w ≠ w0 K}, (bb (y w) : ℂ)) *
          ((chi (MeasurableEquiv.funUnique _ ℝ x + S) : ℂ) * G (MeasurableEquiv.funUnique _ ℝ x + S)) := by
      intro x
      have hx : MeasurableEquiv.funUnique {w : InfinitePlace K // w = w0 K} ℝ x = x ⟨w0 K, rfl⟩ := rfl
      simp only [F, PhiT, hsum, hprod, hx]
      push_cast
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall fun x => h1 x)).trans ?_
    rw [integral_const_mul]
    congr 1
    rw [← integral_add_right_eq_self (fun t => (chi t : ℂ) * G t) S]
    convert hu.integral_comp' (fun t => (chi (t + S) : ℂ) * G (t + S)) using 3 <;>
      first | rfl | exact Subsingleton.elim _ _ | (congr 1; exact Subsingleton.elim _ _)
  rw [integral_mul_const]
  congr 1
  have := integral_fintype_prod_eq_pow (ι := {w : InfinitePlace K // ¬ w = w0 K})
    (fun t : ℝ => (bb t : ℂ)) (μ := volume)
  rw [← volume_pi] at this
  rw [this, integral_complex_ofReal]
  rfl

variable [IsTotallyComplex K]

theorem Zm_phiF_PhiT (s : ℂ) :
    Zm (phiF (PhiT (K := K))) s = (cB : ℂ) ^ Fintype.card {w : InfinitePlace K // w ≠ w0 K} *
      ((1 - Complex.exp (s - 1)) * Bint s) := by
  rw [← integral_chi_exp, ← integral_PhiT_mul (fun t => Complex.exp (s * t))
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  beta_reduce
  rw [prof_phiF, Complex.ofReal_sum]

theorem Zm_phiF_PhiT_one : Zm (phiF (PhiT (K := K))) 1 = 0 := by
  rw [Zm_phiF_PhiT, sub_self, Complex.exp_zero, sub_self, zero_mul, mul_zero]

theorem Zm_phiF_PhiT_ne_zero (σ : ℝ) (hσ : σ ≠ 1) : Zm (phiF (PhiT (K := K))) σ ≠ 0 := by
  rw [Zm_phiF_PhiT]
  refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast cB_pos.ne')) (mul_ne_zero ?_ (Bint_ofReal_ne_zero σ))
  rw [sub_ne_zero, ne_comm, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_exp]
  intro h
  have := Complex.ofReal_injective h
  rw [Real.exp_eq_one_iff, sub_eq_zero] at this
  exact hσ this

end split

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_ThetaS: the theta identity with exact valuations at `S`

For `x : realSpace F` and `k : S → ℤ`,
`Σ_{m ≠ 0, val m = k} c(m) Φ(x + ℓ(m)) =
  Σ_{e ⊆ S} (−1)^{|e|} (covol(𝔫 P^{k+e}) e^{Σx})⁻¹ Σ_{h ≠ 0, h ∈ P^{val ν − k − e − δ}} ĉ⁻(h) Φ̂(ℓ(h) − ℓ(ν) − x)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical Real SchwartzMap

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]

theorem fourierM_phiF_PhiT_zero : fourierM (phiF (PhiT (K := F))) 0 = 0 := by
  have h1 : fourierM (phiF (PhiT (K := F))) 0 = ∫ v, phiF (PhiT (K := F)) v := by
    simp [fourierM, VectorFourier.fourierIntegral]
  have h2 := integral_radial (K := F) (phiF (PhiT (K := F))) (fun b => (PhiT b : ℂ))
    (fun z hz => phiF_of_ne hz)
  have h3 : Zm (phiF (PhiT (K := F))) 1 =
      ∫ b : realSpace F, (Real.exp (∑ w, b w) : ℝ) • (PhiT b : ℂ) := by
    rw [Zm]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [prof_phiF, one_mul, Complex.real_smul, ← Complex.ofReal_sum, ← Complex.ofReal_exp]
    ring
  rw [h1, h2, ← h3, Zm_phiF_PhiT_one, smul_zero]

theorem logK_div {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : logK (a / b) = logK a - logK b := by
  funext w
  simp only [logK_apply, Pi.sub_apply, map_div₀]
  rw [Real.log_div ((map_ne_zero w).2 ha) ((map_ne_zero w).2 hb)]
  ring

theorem fourierM_eq_PhiHat_div {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (x : realSpace F) :
    fourierM (phiF (PhiT (K := F))) (dilV (-x) * mixedEmbedding F (a / b)) =
      PhiHat (PhiT (K := F)) (logK a - logK b - x) := by
  have hab : a / b ≠ 0 := div_ne_zero ha hb
  have hz : ∀ w, normAtPlace w (dilV (-x) * mixedEmbedding F (a / b)) ≠ 0 := fun w => by
    rw [map_mul]
    exact mul_ne_zero (normAtPlace_dilV_ne_zero _ w) (normAtPlace_mixedEmbedding_ne_zero hab w)
  rw [fourierM_eq_PhiHat (PhiT (K := F)) hz, logM_dilV_mul _ _ (normAtPlace_mixedEmbedding_ne_zero hab)]
  congr 1
  rw [show logM (mixedEmbedding F (a / b)) = logK (a / b) from rfl, logK_div ha hb]
  ring

/-! ### Inclusion–exclusion at `S` -/

theorem sum_indE_le {S : Type*} [Fintype S] [DecidableEq S] (j : S → ℤ) :
    ∑ e : Finset S, (-1 : ℂ) ^ e.card * (if indE e ≤ j then 1 else 0) = if j = 0 then 1 else 0 := by
  by_cases hj : 0 ≤ j
  · have h1 : ∀ e : Finset S, (if indE e ≤ j then (1 : ℂ) else 0) =
        ∏ v ∈ e, (if 1 ≤ j v then (1 : ℂ) else 0) := by
      intro e
      by_cases he : indE e ≤ j
      · rw [if_pos he, eq_comm]
        refine Finset.prod_eq_one fun v hv => ?_
        have := he v; simp only [indE, if_pos hv] at this
        rw [if_pos this]
      · rw [if_neg he, eq_comm]
        rw [Pi.le_def] at he
        push Not at he
        obtain ⟨v, hv⟩ := he
        by_cases hve : v ∈ e
        · refine Finset.prod_eq_zero hve ?_
          simp only [indE, if_pos hve] at hv
          rw [if_neg (by omega)]
        · simp only [indE, if_neg hve] at hv
          exact absurd (hj v) (by simpa using hv)
    simp_rw [h1]
    rw [sum_neg_one_pow_prod]
    by_cases h0 : j = 0
    · rw [if_pos h0]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [h0]; simp
    · rw [if_neg h0]
      have : ∃ v, j v ≠ 0 := by
        by_contra h; push Not at h; exact h0 (funext h)
      obtain ⟨v, hv⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      have := hj v
      rw [if_pos (by simp at this; omega)]; ring
  · rw [if_neg (fun h : j = 0 => hj (by rw [h]))]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg, mul_zero]
    intro he
    apply hj
    intro v
    have := he v
    simp only [indE] at this
    split_ifs at this <;> simp <;> omega

/-! ### The theta identity -/

variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- `ĉ⁻(h) = Σ_{x mod 𝔫R} c(x) e(−x h / ν)`. -/
noncomputable def chm {𝔫 : Ideal (𝓞 F)} [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (ν : SInt 𝔪)
    (h : F) : ℂ :=
  ∑ xc : Qn 𝔪 𝔫, c (quotLift xc) * sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) * (h / (ν : F)))

/-- The covolume of `𝔫 P^j`. -/
noncomputable def covN {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (j : SP 𝔪 → ℤ) : ℝ :=
  ZLattice.covolume (idealLattice F (nPk h𝔫 j))

theorem tsum_SInt_ite_mem (j : SP 𝔪 → ℤ) (f : SInt 𝔪 → ℂ) :
    ∑' m : SInt 𝔪, (if (m : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) then f m else 0) =
      ∑' m : (((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F),
        f ⟨m, Pk_subset_SInt j m.2⟩ := by
  set g : (((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F) → SInt 𝔪 :=
    fun m => ⟨m, Pk_subset_SInt j m.2⟩
  have hg : Function.Injective g := fun a b h => Subtype.ext (by
    have := congrArg Subtype.val h; simpa [g] using this)
  rw [← hg.tsum_eq]
  · refine tsum_congr fun m => ?_
    have : ((g m : SInt 𝔪) : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := m.2
    rw [if_pos this]
  · intro m hm
    rw [Function.mem_support] at hm
    by_cases hmJ : (m : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
    · exact ⟨⟨m, hmJ⟩, rfl⟩
    · exact absurd (if_neg hmJ) hm

theorem summable_SInt_ite_mem (j : SP 𝔪 → ℤ) (f : SInt 𝔪 → ℂ)
    (hf : Summable fun m : (((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
      Set F) => f ⟨m, Pk_subset_SInt j m.2⟩) :
    Summable fun m : SInt 𝔪 => (if (m : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) then f m else 0) := by
  set g : (((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F) → SInt 𝔪 :=
    fun m => ⟨m, Pk_subset_SInt j m.2⟩
  have hg : Function.Injective g := fun a b h => Subtype.ext (by
    have := congrArg Subtype.val h; simpa [g] using this)
  rw [← hg.summable_iff]
  · refine hf.congr fun m => ?_
    have : ((g m : SInt 𝔪) : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := m.2
    simp only [Function.comp_apply, if_pos this]
    rfl
  · intro m hm
    by_cases hmJ : (m : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
    · exact absurd ⟨⟨m, hmJ⟩, rfl⟩ hm
    · exact if_neg hmJ

/-- **The theta identity** at `(x, k)`. -/
theorem theta_identity (h𝔪 : 𝔪 ≠ ⊥) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    [Fintype (Qn 𝔪 𝔫)] (x : realSpace F) (k : SP 𝔪 → ℤ) :
    ∑' m : SInt 𝔪, (if (m : F) ≠ 0 ∧ valS (m : F) = k then
        c m * (PhiT (x + logK (m : F)) : ℂ) else 0) =
      ∑ e : Finset (SP 𝔪), (-1 : ℂ) ^ e.card *
        (((covN h𝔫 (k + indE e) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
          ∑' h : SInt 𝔪, (if (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
              (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
            chm (𝔫 := 𝔫) c ν (h : F) * PhiHat PhiT (logK (h : F) - logK (ν : F) - x) else 0)) := by
  set φS : 𝓢(mixedSpace F, ℂ) := phiS contDiff_PhiT hasCompactSupport_PhiT
  have hφS : ⇑φS = phiF (PhiT (K := F)) := rfl
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  obtain ⟨B, hB⟩ := bounded_of_periodic c hc
  -- termwise inclusion–exclusion
  have hterm : ∀ m : SInt 𝔪, (if (m : F) ≠ 0 ∧ valS (m : F) = k then
      c m * (PhiT (x + logK (m : F)) : ℂ) else 0) =
      ∑ e : Finset (SP 𝔪), (-1 : ℂ) ^ e.card *
        (if (m : F) ∈ ((Pk (k + indE e) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
          FractionalIdeal (𝓞 F)⁰ F) then c m * phiF PhiT (dilV x * mixedEmbedding F (m : F))
          else 0) := by
    intro m
    by_cases hm0 : (m : F) = 0
    · rw [if_neg (fun h => h.1 hm0)]
      refine (Finset.sum_eq_zero fun e _ => ?_).symm
      rw [hm0, map_zero, mul_zero, phiF_zero]
      simp
    · have hmem : ∀ e : Finset (SP 𝔪), ((m : F) ∈ ((Pk (k + indE e) :
          (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) ↔
          indE e ≤ valS (m : F) - k := fun e => by
        rw [mem_Pk_iff hm0]
        constructor
        · rintro ⟨-, h⟩ v; have := h v; simp only [Pi.add_apply] at this; simp; omega
        · intro h; refine ⟨m.2, fun v => ?_⟩; have := h v; simp only [Pi.add_apply]
          simp at this; omega
      have hval : ∀ e : Finset (SP 𝔪), (if (m : F) ∈ ((Pk (k + indE e) :
          (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
          c m * phiF PhiT (dilV x * mixedEmbedding F (m : F)) else 0) =
          (if indE e ≤ valS (m : F) - k then 1 else 0) * (c m * (PhiT (x + logK (m : F)) : ℂ)) := by
        intro e
        rw [phiF_dilV_mul_emb PhiT x hm0]
        by_cases he : indE e ≤ valS (m : F) - k
        · rw [if_pos ((hmem e).2 he), if_pos he, one_mul]
        · rw [if_neg (fun h => he ((hmem e).1 h)), if_neg he, zero_mul]
      simp_rw [hval, ← mul_assoc, ← Finset.sum_mul, sum_indE_le, sub_eq_zero]
      by_cases hk : valS (m : F) = k
      · rw [if_pos hk, if_pos ⟨hm0, hk⟩]; ring
      · rw [if_neg hk, if_neg (fun h => hk h.2)]; ring
  simp_rw [hterm]
  have hsum : ∀ e : Finset (SP 𝔪), Summable fun m : SInt 𝔪 => (-1 : ℂ) ^ e.card *
      (if (m : F) ∈ ((Pk (k + indE e) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) then c m * phiF PhiT (dilV x * mixedEmbedding F (m : F))
        else 0) := by
    intro e
    refine Summable.mul_left _ (summable_SInt_ite_mem _ _ ?_)
    set φx : 𝓢(mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilE x) φS
    have h1 := summable_schwartz_fractionalIdeal φx (Pk (k + indE e)) 0
    refine Summable.of_norm_bounded (h1.mul_left B) fun m => ?_
    rw [norm_mul]
    refine mul_le_mul (hB _) (le_of_eq ?_) (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    simp [φx, hφS]
  rw [Summable.tsum_finsetSum fun e _ => hsum e]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [tsum_mul_left]
  congr 1
  rw [tsum_SInt_ite_mem, ← hφS]
  rw [lattice_poisson h𝔪 hD h𝔫 hν c hc φS x (k + indE e)]
  rw [covN]
  congr 1
  have hite : ∀ h : SInt 𝔪, (if (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
      (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
      chm (𝔫 := 𝔫) c ν (h : F) * PhiHat PhiT (logK (h : F) - logK (ν : F) - x) else 0) =
      (if (h : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
      (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
      chm (𝔫 := 𝔫) c ν (h : F) * fourierM φS (dilV (-x) * mixedEmbedding F ((h : F) / (ν : F)))
        else 0) := by
    intro h
    by_cases hh0 : (h : F) = 0
    · rw [if_neg (fun hh => hh.1 hh0)]
      split_ifs
      · rw [hh0, zero_div, map_zero, mul_zero, hφS, fourierM_phiF_PhiT_zero, mul_zero]
      · rfl
    · by_cases hJ : (h : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
          (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
      · rw [if_pos ⟨hh0, hJ⟩, if_pos hJ, hφS, fourierM_eq_PhiHat_div hh0 hν0]
      · rw [if_neg (fun hh => hJ hh.2), if_neg hJ]
  simp_rw [hite]
  rw [tsum_SInt_ite_mem]
  rfl

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Dom: a fundamental domain for the units acting on log coordinates

`D₀ = {x : realSpace | coordinates of x along the fundamental units lie in [0, 1)}`. For every
`x`, exactly `|μ_F|` units `η ∈ 𝓞ˣ` have `x − ℓ(η) ∈ D₀` (Dirichlet: `η = ζ ∏ f_i^{n_i}`,
`ℓ(η) = Σ n_i ℓ(f_i)`, and `n` is the floor of the coordinates of `x`).
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

theorem logK_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : logK (a * b) = logK a + logK b := by
  funext w
  simp only [logK_apply, Pi.add_apply, map_mul]
  rw [Real.log_mul ((map_ne_zero w).2 ha) ((map_ne_zero w).2 hb)]
  ring

theorem logK_one : logK (1 : F) = 0 := by
  funext w; simp [logK_apply]

theorem logK_eq_expMap_symm (x : F) :
    logK x = expMap.symm (normAtAllPlaces (mixedEmbedding F x)) := by
  funext w; simp [logK_apply, normAtAllPlaces_apply, normAtPlace_apply]

/-- `ℓ` on the units of `𝓞`. -/
noncomputable def logU (η : (𝓞 F)ˣ) : realSpace F := logK ((η : 𝓞 F) : F)

theorem unit_coe_ne_zero (η : (𝓞 F)ˣ) : ((η : 𝓞 F) : F) ≠ 0 := by
  simp

theorem logU_mul (η η' : (𝓞 F)ˣ) : logU (η * η') = logU η + logU η' := by
  rw [logU, logU, logU, Units.val_mul]
  push_cast
  exact logK_mul (unit_coe_ne_zero η) (unit_coe_ne_zero η')

theorem logU_one : logU (1 : (𝓞 F)ˣ) = 0 := by
  simp [logU, logK_one]

/-- `ℓ` as an additive homomorphism. -/
noncomputable def logUHom : Additive (𝓞 F)ˣ →+ realSpace F where
  toFun η := logU (Additive.toMul η)
  map_zero' := logU_one
  map_add' _ _ := logU_mul _ _

theorem logU_zpow (η : (𝓞 F)ˣ) (n : ℤ) : logU (η ^ n) = n • logU η := by
  change logUHom (Additive.ofMul (η ^ n)) = _
  rw [ofMul_zpow, map_zsmul]
  rfl

theorem logU_prod {ι : Type*} (s : Finset ι) (f : ι → (𝓞 F)ˣ) :
    logU (∏ i ∈ s, f i) = ∑ i ∈ s, logU (f i) := by
  change logUHom (Additive.ofMul (∏ i ∈ s, f i)) = _
  rw [ofMul_prod, map_sum]
  rfl

theorem logU_torsion {ζ : (𝓞 F)ˣ} (hζ : ζ ∈ torsion F) : logU ζ = 0 := by
  funext w
  rw [logU, logK_apply, (mem_torsion F).1 hζ w, Real.log_one, mul_zero]
  rfl

/-- The decomposition `η = ζ ∏ f_i^{e_i}` of Dirichlet's unit theorem. -/
noncomputable def decomp (η : (𝓞 F)ˣ) : torsion F × (Fin (rank F) → ℤ) :=
  (exist_unique_eq_mul_prod F η).exists.choose

/-- The exponents of a unit along the fundamental system. -/
noncomputable def expo (η : (𝓞 F)ˣ) : Fin (rank F) → ℤ := (decomp η).2

theorem decomp_spec (η : (𝓞 F)ˣ) :
    η = ((decomp η).1 : (𝓞 F)ˣ) * ∏ i, (fundSystem F i) ^ (expo η i) :=
  (exist_unique_eq_mul_prod F η).exists.choose_spec

theorem expo_eq {η ζ : (𝓞 F)ˣ} (hζ : ζ ∈ torsion F) {e : Fin (rank F) → ℤ}
    (h : η = ζ * ∏ i, (fundSystem F i) ^ (e i)) : e = expo η := by
  have := (exist_unique_eq_mul_prod F η).unique (y₁ := (⟨ζ, hζ⟩, e)) (y₂ := decomp η) h
    (decomp_spec η)
  exact congrArg Prod.snd this

theorem logU_fundSystem (i : Fin (rank F)) :
    logU (fundSystem F i) = completeBasis F (equivFinRank i) := by
  rw [completeBasis_apply_of_ne, Equiv.symm_apply_apply, logU, logK_eq_expMap_symm]

theorem logU_eq_sum (η : (𝓞 F)ˣ) :
    logU η = ∑ i, (expo η i : ℝ) •
      completeBasis F (equivFinRank i) := by
  conv_lhs => rw [decomp_spec η]
  rw [logU_mul, logU_torsion (decomp η).1.2, zero_add, logU_prod]
  simp_rw [logU_zpow, logU_fundSystem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]

/-- The fundamental domain for `𝓞ˣ` acting on `realSpace` by translation by `ℓ`. -/
def D0 (F : Type*) [Field F] [NumberField F] : Set (realSpace F) :=
  {x | ∀ i : Fin (rank F), (completeBasis F).repr x (equivFinRank i) ∈ Set.Ico (0 : ℝ) 1}

theorem repr_sub_logU (x : realSpace F) (η : (𝓞 F)ˣ) (i : Fin (rank F)) :
    (completeBasis F).repr (x - logU η) (equivFinRank i) =
      (completeBasis F).repr x (equivFinRank i) - (expo η i) := by
  rw [map_sub, logU_eq_sum, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg (fun h => hj (equivFinRank.injective (Subtype.ext h))), mul_zero]
  · simp

/-- Exactly `|μ|` units translate `x` into `D₀`. -/
theorem hasSum_D0 (x : realSpace F) :
    HasSum (fun η : (𝓞 F)ˣ => (D0 F).indicator (fun _ => (1 : ℝ)) (x - logU η))
      (torsionOrder F : ℝ) := by
  have : Fintype (torsion F) := Fintype.ofFinite _
  set n : Fin (rank F) → ℤ := fun i => ⌊(completeBasis F).repr x (equivFinRank i)⌋
  set g : torsion F → (𝓞 F)ˣ := fun ζ => ζ * ∏ i, (fundSystem F i) ^ (n i)
  have hrepr : ∀ ζ : torsion F, expo (g ζ) = n := fun ζ => (expo_eq ζ.2 rfl).symm
  have hg : Function.Injective g := by
    intro a b hab
    have := mul_right_cancel hab
    exact Subtype.ext this
  have hmem : ∀ η : (𝓞 F)ˣ, x - logU η ∈ D0 F ↔ expo η = n := by
    intro η
    simp only [D0, Set.mem_ofPred_eq, repr_sub_logU, Set.mem_Ico]
    constructor
    · intro h; ext i
      have := h i
      refine (Int.floor_eq_iff.2 ⟨by linarith [this.1], by linarith [this.2]⟩).symm
    · intro h i
      rw [h]
      exact ⟨by linarith [Int.floor_le ((completeBasis F).repr x (equivFinRank i))],
        by linarith [Int.lt_floor_add_one ((completeBasis F).repr x (equivFinRank i))]⟩
  have hzero : ∀ η ∉ Set.range g, (D0 F).indicator (fun _ => (1 : ℝ)) (x - logU η) = 0 := by
    intro η hη
    rw [Set.indicator_of_notMem]
    intro hD
    apply hη
    have he := (hmem η).1 hD
    refine ⟨(decomp η).1, ?_⟩
    have := decomp_spec η
    rw [show expo η = n from he] at this
    exact this.symm
  rw [← hg.hasSum_iff hzero]
  have h1 : ∀ ζ : torsion F, (D0 F).indicator (fun _ => (1 : ℝ)) (x - logU (g ζ)) = 1 := fun ζ => by
    rw [Set.indicator_of_mem ((hmem _).2 (hrepr ζ))]
  have := hasSum_fintype (fun ζ : torsion F => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
  rw [torsionOrder, Nat.card_eq_fintype_card]
  exact this.congr_fun fun ζ => by simp only [Function.comp_apply, h1]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_DomS: a fundamental domain for the `S`-units acting on `realSpace × ℤ^S`

The `S`-unit `ε` acts by `(x, k) ↦ (x + ℓ(ε), k − val_S ε)`. With `B` a set of representatives of
`ℤ^S / val_S(U_S)`, the set `Ω = D₀ × B` meets every orbit in exactly `|μ_F|` points.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- `ℓ` of an `S`-unit. -/
noncomputable def LxU (ε : (SInt 𝔪)ˣ) : realSpace F := logK ((ε : SInt 𝔪) : F)

/-- `val_S` of an `S`-unit. -/
noncomputable def LkU (ε : (SInt 𝔪)ˣ) : SP 𝔪 → ℤ := valS ((ε : SInt 𝔪) : F)

theorem LxU_mul (ε ε' : (SInt 𝔪)ˣ) : LxU (ε * ε') = LxU ε + LxU ε' := by
  rw [LxU, LxU, LxU, Units.val_mul, Subalgebra.coe_mul, logK_mul (unit_ne_zero ε) (unit_ne_zero ε')]

theorem LkU_mul (ε ε' : (SInt 𝔪)ˣ) : LkU (ε * ε') = LkU ε + LkU ε' := by
  rw [LkU, LkU, LkU, Units.val_mul, Subalgebra.coe_mul, valS_mul (unit_ne_zero ε) (unit_ne_zero ε')]

/-- `val_S` as an additive homomorphism. -/
noncomputable def LkHom (𝔪 : Ideal (𝓞 F)) [Fintype (SP 𝔪)] : Additive (SInt 𝔪)ˣ →+ (SP 𝔪 → ℤ) where
  toFun ε := LkU (Additive.toMul ε)
  map_zero' := by
    funext v
    simp [LkU, valS, ordv_one]
  map_add' _ _ := LkU_mul _ _

/-- The units of `𝓞` as `S`-units. -/
noncomputable def iotaU (η : (𝓞 F)ˣ) : (SInt 𝔪)ˣ := Units.map (algebraMap (𝓞 F) (SInt 𝔪)) η

theorem coe_iotaU (η : (𝓞 F)ˣ) : (((iotaU (𝔪 := 𝔪) η : (SInt 𝔪)ˣ) : SInt 𝔪) : F) =
    ((η : 𝓞 F) : F) := rfl

theorem LxU_iotaU (η : (𝓞 F)ˣ) : LxU (iotaU (𝔪 := 𝔪) η) = logU η := rfl

theorem ordv_unit_O (v : HeightOneSpectrum (𝓞 F)) (η : (𝓞 F)ˣ) : ordv v ((η : 𝓞 F) : F) = 0 := by
  have h1 : 0 ≤ ordv v ((η : 𝓞 F) : F) := (valuation_le_one_iff v (unit_coe_ne_zero η)).1
    (v.valuation_le_one _)
  have h2 : 0 ≤ ordv v (((η⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) := (valuation_le_one_iff v
    (unit_coe_ne_zero _)).1 (v.valuation_le_one _)
  have h3 : (((η⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = ((η : 𝓞 F) : F)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have := congrArg (fun z : 𝓞 F => (z : F)) (η.inv_mul)
    simpa using this
  rw [h3, ordv_inv] at h2
  omega

theorem LkU_iotaU (η : (𝓞 F)ˣ) : LkU (iotaU (𝔪 := 𝔪) η) = 0 := by
  funext v; exact ordv_unit_O v.1 η

theorem exists_iotaU_of_LkU_eq_zero {ε : (SInt 𝔪)ˣ} (h : LkU ε = 0) :
    ∃ η : (𝓞 F)ˣ, iotaU η = ε := by
  have hε0 := unit_ne_zero ε
  have hord : ∀ v : HeightOneSpectrum (𝓞 F), ordv v ((ε : SInt 𝔪) : F) = 0 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact congrFun h ⟨v, hv⟩
    · have h1 : 0 ≤ ordv v ((ε : SInt 𝔪) : F) := (mem_SInt_iff hε0).1 (ε : SInt 𝔪).2 v hv
      have hinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        exact congrArg (fun z : SInt 𝔪 => (z : F)) (ε.inv_mul)
      have h2 : 0 ≤ ordv v (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) :=
        (mem_SInt_iff (unit_ne_zero _)).1 (ε⁻¹ : (SInt 𝔪)ˣ).1.2 v hv
      rw [hinv, ordv_inv] at h2
      omega
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((ε : SInt 𝔪) : F) ≤ 1 := fun v =>
    (valuation_le_one_iff v hε0).2 (hord v).ge
  have hval' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((ε : SInt 𝔪) : F)⁻¹ ≤ 1 := fun v =>
    (valuation_le_one_iff v (inv_ne_zero hε0)).2 (by rw [ordv_inv, hord v, neg_zero])
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hval
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hval'
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hε0]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  ext
  simp only [coe_iotaU]
  exact ha

/-- The image `Λ = val_S(U_S)`. -/
noncomputable def LamS (𝔪 : Ideal (𝓞 F)) [Fintype (SP 𝔪)] : AddSubgroup (SP 𝔪 → ℤ) :=
  (LkHom 𝔪).range

/-- Representatives of `ℤ^S / Λ`. -/
def Bset (𝔪 : Ideal (𝓞 F)) [Fintype (SP 𝔪)] : Set (SP 𝔪 → ℤ) :=
  Set.range (Quotient.out : (SP 𝔪 → ℤ) ⧸ LamS 𝔪 → SP 𝔪 → ℤ)

/-- The fundamental domain `Ω = D₀ × B`, as a weight. -/
noncomputable def Omg (x : realSpace F) (k : SP 𝔪 → ℤ) : ℝ :=
  (D0 F).indicator (fun _ => (1 : ℝ)) x * (Bset 𝔪).indicator (fun _ => (1 : ℝ)) k

/-- Exactly `|μ|` points of every orbit lie in `Ω`. -/
theorem hasSum_Omg (y : realSpace F) (k : SP 𝔪 → ℤ) :
    HasSum (fun ε : (SInt 𝔪)ˣ => Omg (y - LxU ε) (k + LkU ε)) (torsionOrder F : ℝ) := by
  set q : (SP 𝔪 → ℤ) ⧸ LamS 𝔪 := QuotientAddGroup.mk k
  set lam0 := Quotient.out q - k
  have hlam0 : lam0 ∈ LamS 𝔪 := by
    have : (QuotientAddGroup.mk (Quotient.out q) : (SP 𝔪 → ℤ) ⧸ LamS 𝔪) = QuotientAddGroup.mk k :=
      Quotient.out_eq q
    rw [QuotientAddGroup.eq] at this
    rw [show lam0 = -(-Quotient.out q + k) by simp only [lam0]; abel]
    exact neg_mem (by simpa [add_comm] using this)
  obtain ⟨ε₁, hε₁⟩ := hlam0
  set ε₁' : (SInt 𝔪)ˣ := Additive.toMul ε₁
  have hε₁' : LkU ε₁' = lam0 := hε₁
  set g : (𝓞 F)ˣ → (SInt 𝔪)ˣ := fun η => ε₁' * iotaU η
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : iotaU (𝔪 := 𝔪) a = iotaU b := mul_left_cancel hab
    have h2 := congrArg (fun z : (SInt 𝔪)ˣ => ((z : SInt 𝔪) : F)) h1
    simp only [coe_iotaU] at h2
    exact Units.ext (by exact_mod_cast h2)
  have hB : ∀ ε : (SInt 𝔪)ˣ, k + LkU ε ∈ Bset 𝔪 → LkU ε = lam0 := by
    rintro ε ⟨q', hq'⟩
    have hmem : LkU ε ∈ LamS 𝔪 := ⟨Additive.ofMul ε, rfl⟩
    have h1 : (QuotientAddGroup.mk (k + LkU ε) : (SP 𝔪 → ℤ) ⧸ LamS 𝔪) = q := by
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2 hmem, add_zero]
    have h2 : q' = q := by
      rw [← h1, ← hq']; exact (Quotient.out_eq q').symm
    simp only [lam0]
    rw [← h2, hq']; ring
  have hzero : ∀ ε ∉ Set.range g, Omg (y - LxU ε) (k + LkU ε) = 0 := by
    intro ε hε
    rw [Omg]
    by_cases hk : k + LkU ε ∈ Bset 𝔪
    · exfalso; apply hε
      have h1 : LkU (ε₁'⁻¹ * ε) = 0 := by
        rw [LkU_mul, hB ε hk, ← hε₁', ← LkU_mul, inv_mul_cancel]; exact (LkHom 𝔪).map_zero
      obtain ⟨η, hη⟩ := exists_iotaU_of_LkU_eq_zero h1
      exact ⟨η, by simp only [g, hη, mul_inv_cancel_left]⟩
    · rw [Set.indicator_of_notMem hk, mul_zero]
  rw [← hg.hasSum_iff hzero]
  have hcomp : ∀ η : (𝓞 F)ˣ, Omg (y - LxU (g η)) (k + LkU (g η)) =
      (D0 F).indicator (fun _ => (1 : ℝ)) ((y - LxU ε₁') - logU η) := by
    intro η
    have hk : k + LkU (g η) ∈ Bset 𝔪 := by
      rw [LkU_mul, LkU_iotaU, add_zero, hε₁']
      exact ⟨q, by simp [lam0]⟩
    rw [Omg, Set.indicator_of_mem hk, mul_one, LxU_mul, LxU_iotaU, sub_add_eq_sub_sub]
  have := hasSum_D0 (y - LxU ε₁')
  exact this.congr_fun fun η => by simp only [Function.comp_apply, hcomp]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Unf: unfolding over the `S`-units

For `G : realSpace × ℤ^S → ℂ` with `Σ_k ∫ ‖G(·, k)‖ < ∞`,
`Σ_{ε ∈ U_S} Σ_k ∫ Ω(x, k) G(x + ℓ(ε), k − val ε) dx = |μ| Σ_k ∫ G(x, k) dx`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open MeasureTheory
open scoped Classical ENNReal

set_option linter.unusedSectionVars false

/-- Termwise integration of a nonnegative series. -/
theorem hasSum_integral_of_nonneg {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {f : ι → α → ℝ} (hf : ∀ i a, 0 ≤ f i a) (hmeas : ∀ i, AEStronglyMeasurable (f i) μ)
    {g : α → ℝ} (hg : Integrable g μ) (hfg : ∀ a, HasSum (fun i => f i a) (g a)) :
    HasSum (fun i => ∫ a, f i a ∂μ) (∫ a, g a ∂μ) := by
  have hg0 : ∀ a, 0 ≤ g a := fun a => (hfg a).nonneg fun i => hf i a
  have hle : ∀ i a, f i a ≤ g a := fun i a => le_hasSum (hfg a) i fun j _ => hf j a
  have hint : ∀ i, Integrable (f i) μ := fun i =>
    hg.mono' (hmeas i) (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf i a)]; exact hle i a)
  have hl : ∫⁻ a, ENNReal.ofReal (g a) ∂μ = ∑' i, ∫⁻ a, ENNReal.ofReal (f i a) ∂μ := by
    rw [← lintegral_tsum fun i => (hmeas i).aemeasurable.ennreal_ofReal]
    refine lintegral_congr fun a => ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hf i a) (hfg a).summable, (hfg a).tsum_eq]
  have hfin : ∑' i, ∫⁻ a, ENNReal.ofReal (f i a) ∂μ ≠ ∞ := by
    rw [← hl]; exact (MeasureTheory.Integrable.lintegral_lt_top hg).ne
  have hfin' : ∀ i, ∫⁻ a, ENNReal.ofReal (f i a) ∂μ ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hfin (ENNReal.le_tsum i)
  have h := ENNReal.hasSum_toReal hfin
  rw [← ENNReal.tsum_toReal_eq hfin', ← hl] at h
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable]
  refine h.congr_fun fun i => ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hf i)) (hmeas i)]

theorem countable_numberField (F : Type*) [Field F] [NumberField F] : Countable F := by
  have b := Module.finBasis ℚ F
  exact b.equivFun.injective.countable

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

instance countable_SUnits : Countable (SInt 𝔪)ˣ := by
  have := countable_numberField F
  have h : Function.Injective (fun ε : (SInt 𝔪)ˣ => ((ε : SInt 𝔪) : F)) := fun a b h =>
    Units.ext (Subtype.ext h)
  exact h.countable

theorem measurableSet_D0 : MeasurableSet (D0 F) := by
  have hc : ∀ i : Fin (rank F), Continuous fun x : realSpace F =>
      (completeBasis F).repr x (equivFinRank i) := fun i => by
    have := ((completeBasis F).equivFunL).continuous
    exact (continuous_apply _).comp this
  have : D0 F = ⋂ i : Fin (rank F), (fun x : realSpace F =>
      (completeBasis F).repr x (equivFinRank i)) ⁻¹' Set.Ico 0 1 := by
    ext x; simp [D0]
  rw [this]
  exact MeasurableSet.iInter fun i => (hc i).measurable measurableSet_Ico

theorem Omg_nonneg (x : realSpace F) (k : SP 𝔪 → ℤ) : 0 ≤ Omg (𝔪 := 𝔪) x k := by
  unfold Omg; exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem Omg_le_one (x : realSpace F) (k : SP 𝔪 → ℤ) : Omg (𝔪 := 𝔪) x k ≤ 1 := by
  unfold Omg
  refine mul_le_one₀ ?_ (Set.indicator_nonneg (fun _ _ => zero_le_one) _) ?_
  · by_cases hx : x ∈ D0 F <;> simp [hx]
  · by_cases hk : k ∈ Bset 𝔪 <;> simp [hk]

theorem measurable_Omg (k : SP 𝔪 → ℤ) : Measurable fun x : realSpace F => Omg (𝔪 := 𝔪) x k :=
  ((measurable_const.indicator measurableSet_D0)).mul measurable_const

theorem tsum_integral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : realSpace F → (SP 𝔪 → ℤ) → ℝ) (G : realSpace F → (SP 𝔪 → ℤ) → E)
    (a : realSpace F) (b : SP 𝔪 → ℤ) :
    ∑' k, ∫ x, W x k • G (x + a) (k - b) = ∑' k, ∫ y, W (y - a) (k + b) • G y k := by
  have h1 : ∀ k, ∫ x, W x k • G (x + a) (k - b) = ∫ y, W (y - a) k • G y (k - b) := fun k => by
    have := integral_add_right_eq_self (μ := (volume : Measure (realSpace F)))
      (fun y => W (y - a) k • G y (k - b)) a
    simpa only [add_sub_cancel_right] using this
  simp_rw [h1]
  rw [← (Equiv.addRight b).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]

/-- The unfolding identity, real nonnegative form. -/
theorem hasSum_unfold_nonneg (G : realSpace F → (SP 𝔪 → ℤ) → ℝ) (hG0 : ∀ x k, 0 ≤ G x k)
    (hGi : ∀ k, Integrable fun x => G x k) (hGs : Summable fun k => ∫ x, G x k) :
    HasSum (fun ε : (SInt 𝔪)ˣ => ∑' k, ∫ x, Omg x k * G (x + LxU ε) (k - LkU ε))
      ((torsionOrder F : ℝ) * ∑' k, ∫ x, G x k) := by
  set N : (SP 𝔪 → ℤ) × (SInt 𝔪)ˣ → ℝ := fun p =>
    ∫ y, Omg (y - LxU p.2) (p.1 + LkU p.2) * G y p.1
  have hN0 : 0 ≤ N := fun p => integral_nonneg fun y => mul_nonneg (Omg_nonneg _ _) (hG0 _ _)
  have hk : ∀ k, HasSum (fun ε : (SInt 𝔪)ˣ => N (k, ε)) ((torsionOrder F : ℝ) * ∫ x, G x k) := by
    intro k
    rw [← integral_const_mul]
    refine hasSum_integral_of_nonneg (fun ε y => mul_nonneg (Omg_nonneg _ _) (hG0 _ _))
      (fun ε => ?_) ((hGi k).const_mul _) (fun y => (hasSum_Omg y k).mul_right (G y k))
    exact ((measurable_Omg _).comp (measurable_id.sub_const _)).aestronglyMeasurable.mul
      (hGi k).aestronglyMeasurable
  have hsum : Summable N := by
    refine (summable_prod_of_nonneg hN0).2 ⟨fun k => (hk k).summable, ?_⟩
    refine (hGs.mul_left (torsionOrder F : ℝ)).congr fun k => ?_
    exact (hk k).tsum_eq.symm
  have htot : HasSum N ((torsionOrder F : ℝ) * ∑' k, ∫ x, G x k) := by
    have := hsum.hasSum
    convert this using 1
    rw [hsum.tsum_prod, ← tsum_mul_left]
    exact tsum_congr fun k => (hk k).tsum_eq.symm
  -- swap to `ε` outer
  have hswap : HasSum (N ∘ Prod.swap) ((torsionOrder F : ℝ) * ∑' k, ∫ x, G x k) :=
    (Equiv.prodComm _ _).hasSum_iff.2 htot
  have hfib : ∀ ε : (SInt 𝔪)ˣ, HasSum (fun k => (N ∘ Prod.swap) (ε, k))
      (∑' k, ∫ x, Omg x k * G (x + LxU ε) (k - LkU ε)) := by
    intro ε
    have hs : Summable fun k => (N ∘ Prod.swap) (ε, k) :=
      ((Equiv.prodComm _ _).summable_iff.2 hsum).prod_factor ε
    convert hs.hasSum using 1
    have := tsum_integral_shift (E := ℝ) (fun x k => Omg x k) G (LxU ε) (LkU ε)
    simp only [smul_eq_mul] at this
    rw [this]
    rfl
  exact hswap.prod_fiberwise hfib

/-- The unfolding identity, complex form. -/
theorem hasSum_unfold (G : realSpace F → (SP 𝔪 → ℤ) → ℂ) (hGi : ∀ k, Integrable fun x => G x k)
    (hGs : Summable fun k => ∫ x, ‖G x k‖) :
    HasSum (fun ε : (SInt 𝔪)ˣ => ∑' k, ∫ x, (Omg x k : ℂ) * G (x + LxU ε) (k - LkU ε))
      ((torsionOrder F : ℂ) * ∑' k, ∫ x, G x k) := by
  set N : (SP 𝔪 → ℤ) × (SInt 𝔪)ˣ → ℝ := fun p =>
    ∫ y, Omg (y - LxU p.2) (p.1 + LkU p.2) * ‖G y p.1‖
  set H : (SP 𝔪 → ℤ) × (SInt 𝔪)ˣ → ℂ := fun p =>
    ∫ y, (Omg (y - LxU p.2) (p.1 + LkU p.2) : ℂ) * G y p.1
  have hN0 : 0 ≤ N := fun p => integral_nonneg fun y => mul_nonneg (Omg_nonneg _ _) (norm_nonneg _)
  have hmeasO : ∀ (ε : (SInt 𝔪)ˣ) (k : SP 𝔪 → ℤ), AEStronglyMeasurable
      (fun y : realSpace F => Omg (y - LxU ε) (k + LkU ε)) volume := fun ε k =>
    ((measurable_Omg _).comp (measurable_id.sub_const _)).aestronglyMeasurable
  have hNk : ∀ k, HasSum (fun ε : (SInt 𝔪)ˣ => N (k, ε)) ((torsionOrder F : ℝ) * ∫ x, ‖G x k‖) := by
    intro k
    rw [← integral_const_mul]
    exact hasSum_integral_of_nonneg (fun ε y => mul_nonneg (Omg_nonneg _ _) (norm_nonneg _))
      (fun ε => (hmeasO ε k).mul (hGi k).norm.aestronglyMeasurable) ((hGi k).norm.const_mul _)
      (fun y => (hasSum_Omg y k).mul_right ‖G y k‖)
  have hNsum : Summable N := by
    refine (summable_prod_of_nonneg hN0).2 ⟨fun k => (hNk k).summable, ?_⟩
    refine (hGs.mul_left (torsionOrder F : ℝ)).congr fun k => ?_
    exact (hNk k).tsum_eq.symm
  have hHN : ∀ p, ‖H p‖ ≤ N p := fun p => by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Omg_nonneg _ _)]
  have hHsum : Summable H := Summable.of_norm_bounded hNsum hHN
  have hintF : ∀ (k : SP 𝔪 → ℤ) (ε : (SInt 𝔪)ˣ), Integrable fun y : realSpace F =>
      (Omg (y - LxU ε) (k + LkU ε) : ℂ) * G y k := fun k ε => by
    refine (hGi k).norm.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hmeasO ε k)).mul
      (hGi k).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Omg_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Omg_le_one _ _)
  have hHk : ∀ k, HasSum (fun ε : (SInt 𝔪)ˣ => H (k, ε)) ((torsionOrder F : ℂ) * ∫ x, G x k) := by
    intro k
    have h1 := hasSum_integral_of_summable_integral_norm (μ := volume) (hintF k)
      (by
        refine (hNk k).summable.congr fun ε => ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Omg_nonneg _ _)])
    have heq : ∫ a, ∑' i : (SInt 𝔪)ˣ, (Omg (a - LxU i) (k + LkU i) : ℂ) * G a k =
        (torsionOrder F : ℂ) * ∫ x, G x k := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only []
      rw [tsum_mul_right, ← Complex.ofReal_tsum, (hasSum_Omg y k).tsum_eq]
      push_cast; ring
    rw [← heq]; exact h1
  have htot : HasSum H ((torsionOrder F : ℂ) * ∑' k, ∫ x, G x k) := by
    have := hHsum.hasSum
    convert this using 1
    rw [hHsum.tsum_prod, ← tsum_mul_left]
    exact tsum_congr fun k => (hHk k).tsum_eq.symm
  have hswap : HasSum (H ∘ Prod.swap) ((torsionOrder F : ℂ) * ∑' k, ∫ x, G x k) :=
    (Equiv.prodComm _ _).hasSum_iff.2 htot
  have hfib : ∀ ε : (SInt 𝔪)ˣ, HasSum (fun k => (H ∘ Prod.swap) (ε, k))
      (∑' k, ∫ x, (Omg x k : ℂ) * G (x + LxU ε) (k - LkU ε)) := by
    intro ε
    have hs : Summable fun k => (H ∘ Prod.swap) (ε, k) :=
      ((Equiv.prodComm _ _).summable_iff.2 hHsum).prod_factor ε
    convert hs.hasSum using 1
    have := tsum_integral_shift (E := ℂ) (fun x k => Omg x k) G (LxU ε) (LkU ε)
    simp only [Complex.real_smul] at this
    rw [this]
    rfl
  exact hswap.prod_fiberwise hfib

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Gen: `R ∖ 0 = U_S · {gen 𝔟}`

With a system of allowed generators, every nonzero `m ∈ R` is uniquely `ε · gen 𝔟` with `𝔟`
exterior and `ε ∈ R^×`. Sums over `R` (with vanishing term at `0`) are sums over these pairs.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- Exterior ideals. -/
abbrev Ext (𝔪 : Ideal (𝓞 F)) : Type _ := {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟}

theorem isUnit_of_ordv_eq_zero {x : F} (hx0 : x ≠ 0) (h : ∀ w ∉ placesOf 𝔪, ordv w x = 0) :
    ∃ ε : (SInt 𝔪)ˣ, ((ε : SInt 𝔪) : F) = x := by
  have h1 : x ∈ (placesOf 𝔪).integer F := (mem_SInt_iff hx0).2 fun w hw => (h w hw).ge
  have h2 : x⁻¹ ∈ (placesOf 𝔪).integer F := (mem_SInt_iff (inv_ne_zero hx0)).2 fun w hw => by
    rw [ordv_inv, h w hw, neg_zero]
  refine ⟨⟨⟨x, h1⟩, ⟨x⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩,
    rfl⟩

theorem ordv_eq_count_outside {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∉ placesOf 𝔪) : ordv w (m : F) = count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  have := congrArg (count F w) (spanSingleton_eq_mul_Pk h𝔟 hm)
  rw [count_mul F w (coeIdeal_ne_zero.2 h𝔟.1) (Pk_ne_zero _), count_Pk, dif_neg hw, add_zero] at this
  exact this

variable {ι : F →+* ℂ}

theorem span_unit_mul_gen (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) (ε : (SInt 𝔪)ˣ) :
    Ideal.span {(ε : SInt 𝔪) * g.gen 𝔟.1} = 𝔟.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen 𝔟.1 𝔟.2, Ideal.span_singleton_mul_left_unit ε.isUnit]

theorem gen_ne_zero (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) : ((g.gen 𝔟.1 : SInt 𝔪) : F) ≠ 0 :=
  ne_zero_of_span_eq 𝔟.2 (g.span_gen 𝔟.1 𝔟.2)

/-- The parametrization `(𝔟, ε) ↦ ε · gen 𝔟`. -/
noncomputable def par (g : AllowedGen ι 𝔪) (p : Ext 𝔪 × (SInt 𝔪)ˣ) : SInt 𝔪 :=
  (p.2 : SInt 𝔪) * g.gen p.1.1

theorem par_injective (g : AllowedGen ι 𝔪) : Function.Injective (par g) := by
  rintro ⟨𝔟, ε⟩ ⟨𝔟', ε'⟩ h
  simp only [par] at h
  have h1 := span_unit_mul_gen g 𝔟 ε
  have h2 := span_unit_mul_gen g 𝔟' ε'
  rw [h] at h1
  have hb : 𝔟 = 𝔟' := by
    apply Subtype.ext
    apply coeIdeal_injective (K := F)
    refine eq_of_count_eq (coeIdeal_ne_zero.2 𝔟.2.1) (coeIdeal_ne_zero.2 𝔟'.2.1) fun w => ?_
    by_cases hw : w ∈ placesOf 𝔪
    · rw [count_eq_zero_of_exterior 𝔟.2 hw, count_eq_zero_of_exterior 𝔟'.2 hw]
    · rw [← ordv_eq_count_outside 𝔟.2 h1 hw, ← ordv_eq_count_outside 𝔟'.2 h2 hw]
  subst hb
  have hg0 := gen_ne_zero g 𝔟
  have : ((ε : SInt 𝔪) : F) = ((ε' : SInt 𝔪) : F) := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) h
    simp only [Subalgebra.coe_mul] at this
    exact mul_right_cancel₀ hg0 this
  rw [Prod.mk.injEq]
  exact ⟨rfl, Units.ext (Subtype.ext this)⟩

theorem exists_par (g : AllowedGen ι 𝔪) {m : SInt 𝔪} (hm : (m : F) ≠ 0) :
    ∃ p, par g p = m := by
  set J := spanSingleton (𝓞 F)⁰ (m : F) *
    ((Pk (-valS (𝔪 := 𝔪) (m : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := mul_ne_zero (spanSingleton_ne_zero hm) (Pk_ne_zero _)
  have hcount : ∀ w, count F w J = if w ∈ placesOf 𝔪 then 0 else ordv w (m : F) := by
    intro w
    rw [count_mul F w (spanSingleton_ne_zero hm) (Pk_ne_zero _), count_Pk]
    split_ifs with hw
    · simp [valS, ordv]
    · rw [add_zero]; rfl
  have hJle : J ≤ 1 := by
    rw [le_iff_count hJ0 one_ne_zero]
    intro w
    rw [count_one, hcount]
    split_ifs with hw
    · exact le_rfl
    · exact (mem_SInt_iff hm).1 m.2 w hw
  obtain ⟨𝔟, h𝔟J⟩ := le_one_iff_exists_coeIdeal.1 hJle
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [← h𝔟J, coeIdeal_bot]
  have h𝔟ext : IsExterior 𝔪 𝔟 := by
    refine ⟨h𝔟0, ?_⟩
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hP0 : P ≠ ⊥ := fun h => h𝔟0 (le_bot_iff.1 (h ▸ le_sup_left.trans hle))
    set w : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, hP0⟩
    have hw : w ∈ placesOf 𝔪 := le_sup_right.trans hle
    have h1 : count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
      rw [h𝔟J, hcount, if_pos hw]
    rw [count_coe F w h𝔟0, Nat.cast_eq_zero] at h1
    exact (Associates.count_ne_zero_iff_dvd h𝔟0 w.irreducible).2
      (Ideal.dvd_iff_le.2 (le_sup_left.trans hle)) h1
  set b : Ext 𝔪 := ⟨𝔟, h𝔟ext⟩
  have hg0 := gen_ne_zero g b
  -- `m / gen 𝔟` is an `S`-unit
  have hq : ∀ w ∉ placesOf 𝔪, ordv w ((m : F) / (g.gen 𝔟 : F)) = 0 := by
    intro w hw
    rw [div_eq_mul_inv, ordv_mul w hm (inv_ne_zero hg0), ordv_inv,
      ordv_eq_count_outside h𝔟ext (g.span_gen 𝔟 h𝔟ext) hw, h𝔟J, hcount, if_neg hw]
    ring
  obtain ⟨ε, hε⟩ := isUnit_of_ordv_eq_zero (div_ne_zero hm hg0) hq
  refine ⟨(b, ε), Subtype.ext ?_⟩
  simp only [par, Subalgebra.coe_mul, hε, b]
  rw [div_mul_cancel₀ _ hg0]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L2B_SUnit: `U_S / U_S⁶` is finite; ideals are countable

`U_S` is finitely generated: the valuations at the finitely many places of `S` give a map to
`ℤ^S` whose kernel is the image of `(𝓞 F)ˣ` (finitely generated by Dirichlet's unit theorem).
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F]

theorem placesOf_finite {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  refine (Ideal.finite_factors (R := 𝓞 F) h𝔪).subset fun v hv => ?_
  exact Ideal.dvd_iff_le.2 hv

/-- The valuation vector of an `S`-unit at the places of `S`, additively. -/
noncomputable def valVec (𝔪 : Ideal (𝓞 F)) :
    Additive (SUnit 𝔪) →+ (placesOf 𝔪 → ℤ) where
  toFun x v := Multiplicative.toAdd (v.1.valuationOfNeZero ((Additive.toMul x : SUnit 𝔪) : Fˣ))
  map_zero' := by funext v; simp
  map_add' x y := by funext v; simp

theorem mem_ker_valVec {𝔪 : Ideal (𝓞 F)} (x : Additive (SUnit 𝔪)) (hx : valVec 𝔪 x = 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    v.valuation F (((Additive.toMul x : SUnit 𝔪) : Fˣ) : F) = 1 := by
  by_cases hv : v ∈ placesOf 𝔪
  · have h := congrFun hx ⟨v, hv⟩
    simp only [valVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at h
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, show v.valuationOfNeZero _ = 1 from h]
    rfl
  · exact (Additive.toMul x).2 v hv

theorem val_unit (v : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) :
    v.valuation F ((Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u : Fˣ) : F) = 1 := by
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq]
  rfl

/-- The units of `𝓞 F` as `S`-units. -/
noncomputable def unitsToSUnit (𝔪 : Ideal (𝓞 F)) : (𝓞 F)ˣ →* SUnit 𝔪 where
  toFun u := ⟨Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u, fun v _ => val_unit v u⟩
  map_one' := by ext; simp
  map_mul' u w := by ext; simp

theorem ker_valVec (𝔪 : Ideal (𝓞 F)) :
    LinearMap.ker (valVec 𝔪).toIntLinearMap =
      LinearMap.range (MonoidHom.toAdditive (unitsToSUnit 𝔪)).toIntLinearMap := by
  ext x
  simp only [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, LinearMap.mem_range]
  constructor
  · intro hx
    have hval := mem_ker_valVec x hx
    set y : Fˣ := ((Additive.toMul x : SUnit 𝔪) : Fˣ)
    have h1 : (y : F) ∈ (algebraMap (𝓞 F) F).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ fun v => (hval v).le
    have h2 : ((y⁻¹ : Fˣ) : F) ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ fun v => ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hval v, inv_one]
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hab : a * b = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    refine ⟨Additive.ofMul ⟨a, b, hab, by rw [mul_comm, hab]⟩, ?_⟩
    apply Additive.toMul.injective
    ext
    simp [unitsToSUnit, ha, y]
  · rintro ⟨u, rfl⟩
    funext v
    simp only [valVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
      MonoidHom.toAdditive_apply_apply]
    have : v.1.valuationOfNeZero ((unitsToSUnit 𝔪 (Additive.toMul u) : SUnit 𝔪) : Fˣ) = 1 :=
      HeightOneSpectrum.valuation_of_unit_eq v.1 _
    simp only [toMul_ofMul, this]
    rfl

instance moduleFinite_SUnit {𝔪 : Ideal (𝓞 F)} [Fact (𝔪 ≠ ⊥)] :
    Module.Finite ℤ (Additive (SUnit 𝔪)) := by
  have hfin : Finite (placesOf 𝔪) := (placesOf_finite (Fact.out)).to_subtype
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (valVec 𝔪).toIntLinearMap ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ker_valVec, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _

theorem finite_SClass {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  have : Fact (𝔪 ≠ ⊥) := ⟨h𝔪⟩
  have : Group.FG (SUnit 𝔪) :=
    GroupFG.iff_add_fg.2 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  refine CommGroup.finite_of_fg_isMulTorsion _ fun x => ?_
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨6, by norm_num, ?_⟩
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨y, rfl⟩

instance countable_ideal : Countable (Ideal (𝓞 F)) := by
  have : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
    ext I; simp
  have hc : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [this]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
  exact Set.countable_univ_iff.1 hc

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-!
# L3P_UnfR: unfolding a theta function over `R ∖ 0`

If `Q (ε m) (x, k) = Q m (x + ℓ(σ ε), k − val(σ ε))` for an automorphism `σ` of `U_S`, then
`Σ_k ∫ Ω(x,k) Σ_{m ∈ R} Q m (x, k) dx = |μ| Σ_{𝔟 exterior} Σ_k ∫ Q (gen 𝔟) (x, k) dx`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.Units MeasureTheory NumberField.mixedEmbedding
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]
variable {ι : F →+* ℂ}

theorem summable_integral_norm_shift (G : realSpace F → (SP 𝔪 → ℤ) → ℂ) (a : realSpace F)
    (b : SP 𝔪 → ℤ) (hG : Summable fun k => ∫ x, ‖G x k‖) :
    Summable fun k => ∫ x, ‖G (x + a) (k - b)‖ := by
  have h1 : ∀ k, ∫ x, ‖G (x + a) (k - b)‖ = ∫ x, ‖G x (k - b)‖ := fun k =>
    integral_add_right_eq_self (fun x => ‖G x (k - b)‖) a
  simp_rw [h1]
  exact (Equiv.subRight b).summable_iff.2 hG

/-- **Unfolding over `R ∖ 0`.** -/
theorem tsum_unfold_R (g : AllowedGen ι 𝔪) (σ : (SInt 𝔪)ˣ ≃ (SInt 𝔪)ˣ)
    (Q : SInt 𝔪 → realSpace F → (SP 𝔪 → ℤ) → ℂ) (hQ0 : ∀ x k, Q 0 x k = 0)
    (hQeq : ∀ (ε : (SInt 𝔪)ˣ) m x k, Q ((ε : SInt 𝔪) * m) x k =
      Q m (x + LxU (σ ε)) (k - LkU (σ ε)))
    (hQi : ∀ m k, Integrable fun x => Q m x k)
    (hQs1 : ∀ 𝔟 : Ext 𝔪, Summable fun k => ∫ x, ‖Q (g.gen 𝔟.1) x k‖)
    (hQs : Summable fun 𝔟 : Ext 𝔪 => ∑' k, ∫ x, ‖Q (g.gen 𝔟.1) x k‖) :
    ∑' k, ∫ x, (Omg x k : ℂ) * ∑' m, Q m x k =
      (torsionOrder F : ℂ) * ∑' 𝔟 : Ext 𝔪, ∑' k, ∫ x, Q (g.gen 𝔟.1) x k := by
  set P := Ext 𝔪 × (SInt 𝔪)ˣ
  set f : P → realSpace F → (SP 𝔪 → ℤ) → ℂ := fun p x k => Q (par g p) x k
  have hf_eq : ∀ (p : P) x k, f p x k = Q (g.gen p.1.1) (x + LxU (σ p.2)) (k - LkU (σ p.2)) :=
    fun p x k => hQeq p.2 _ x k
  -- step 1: reindex the inner sum
  have h1 : ∀ x k, ∑' m, Q m x k = ∑' p : P, f p x k := fun x k => by
    refine ((par_injective g).tsum_eq fun m hm => ?_).symm
    by_contra hr
    apply hm
    by_cases h0 : (m : F) = 0
    · rw [show m = 0 from Subtype.ext h0, hQ0]
    · exact absurd (exists_par g h0) hr
  simp_rw [h1]
  -- majorants
  set B : (SP 𝔪 → ℤ) × P → ℝ := fun q => ∫ x, Omg x q.1 * ‖f q.2 x q.1‖
  set A : (SP 𝔪 → ℤ) × P → ℂ := fun q => ∫ x, (Omg x q.1 : ℂ) * f q.2 x q.1
  have hB0 : 0 ≤ B := fun q => integral_nonneg fun x => mul_nonneg (Omg_nonneg _ _) (norm_nonneg _)
  -- per `𝔟`, the unfolded norm sum
  have hU : ∀ 𝔟 : Ext 𝔪, HasSum (fun ε : (SInt 𝔪)ˣ => ∑' k, B (k, (𝔟, ε)))
      ((torsionOrder F : ℝ) * ∑' k, ∫ x, ‖Q (g.gen 𝔟.1) x k‖) := by
    intro 𝔟
    have := hasSum_unfold_nonneg (𝔪 := 𝔪) (fun x k => ‖Q (g.gen 𝔟.1) x k‖) (fun _ _ => norm_nonneg _)
      (fun k => (hQi _ k).norm) (hQs1 𝔟)
    refine (σ.hasSum_iff.2 this).congr_fun fun ε => ?_
    simp only [Function.comp_apply, B]
    refine tsum_congr fun k => integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf_eq]
  -- the reindexing `Γ × P ≃ Ext × (U × Γ)`
  set e : (SP 𝔪 → ℤ) × P ≃ Ext 𝔪 × ((SInt 𝔪)ˣ × (SP 𝔪 → ℤ)) :=
    { toFun := fun q => (q.2.1, (q.2.2, q.1))
      invFun := fun r => (r.2.2, (r.1, r.2.1))
      left_inv := fun q => rfl
      right_inv := fun r => rfl }
  have hBk : ∀ (𝔟 : Ext 𝔪) (ε : (SInt 𝔪)ˣ), Summable fun k => B (k, (𝔟, ε)) := by
    intro 𝔟 ε
    refine Summable.of_nonneg_of_le (fun k => hB0 _) (fun k => ?_)
      (summable_integral_norm_shift (Q (g.gen 𝔟.1)) (LxU (σ ε)) (LkU (σ ε)) (hQs1 𝔟))
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
      mul_nonneg (Omg_nonneg _ _) (norm_nonneg _))
      ((hQi (g.gen 𝔟.1) (k - LkU (σ ε))).norm.comp_add_right (LxU (σ ε)))
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf_eq]
    exact mul_le_of_le_one_left (norm_nonneg _) (Omg_le_one _ _)
  have hBsum : Summable B := by
    rw [← e.symm.summable_iff]
    refine (summable_prod_of_nonneg (f := B ∘ e.symm) fun r => hB0 _).2 ⟨fun 𝔟 => ?_, ?_⟩
    · exact (summable_prod_of_nonneg (f := fun r : (SInt 𝔪)ˣ × (SP 𝔪 → ℤ) => B (r.2, (𝔟, r.1)))
        fun r => hB0 _).2 ⟨fun ε => hBk 𝔟 ε, (hU 𝔟).summable⟩
    · refine (hQs.mul_left (torsionOrder F : ℝ)).congr fun 𝔟 => ?_
      have hs : Summable fun r : (SInt 𝔪)ˣ × (SP 𝔪 → ℤ) => B (r.2, (𝔟, r.1)) :=
        (summable_prod_of_nonneg (f := fun r : (SInt 𝔪)ˣ × (SP 𝔪 → ℤ) => B (r.2, (𝔟, r.1)))
          fun r => hB0 _).2 ⟨fun ε => hBk 𝔟 ε, (hU 𝔟).summable⟩
      simp only [Function.comp_apply]
      rw [show (fun c : (SInt 𝔪)ˣ × (SP 𝔪 → ℤ) => B (e.symm (𝔟, c))) =
        fun r => B (r.2, (𝔟, r.1)) from rfl, hs.tsum_prod]
      exact (hU 𝔟).tsum_eq.symm
  have hfi : ∀ (p : P) k, Integrable fun x => f p x k := fun p k => by
    simp only [hf_eq]
    exact (hQi (g.gen p.1.1) (k - LkU (σ p.2))).comp_add_right (LxU (σ p.2))
  have hOfi : ∀ (p : P) k, Integrable fun x => (Omg x k : ℂ) * f p x k := fun p k => by
    refine (hfi p k).norm.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (measurable_Omg k).aestronglyMeasurable).mul (hfi p k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Omg_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Omg_le_one _ _)
  have hnormA : ∀ q : (SP 𝔪 → ℤ) × P, ∫ x, ‖(Omg x q.1 : ℂ) * f q.2 x q.1‖ = B q := fun q =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Omg_nonneg _ _)])
  have hAB : ∀ q, ‖A q‖ ≤ B q := fun q =>
    (norm_integral_le_integral_norm _).trans (le_of_eq (hnormA q))
  have hAsum : Summable A := Summable.of_norm_bounded hBsum hAB
  have hk : ∀ k, ∫ x, (Omg x k : ℂ) * ∑' p : P, f p x k = ∑' p : P, A (k, p) := by
    intro k
    simp_rw [← tsum_mul_left]
    refine (integral_tsum_of_summable_integral_norm (fun p => hOfi p k) ?_).symm
    exact (hBsum.prod_factor k).congr fun p => (hnormA (k, p)).symm
  simp_rw [hk]
  rw [← hAsum.tsum_prod, ← e.symm.tsum_eq]
  have hAe : Summable fun c => A (e.symm c) := e.symm.summable_iff.2 hAsum
  rw [hAe.tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun 𝔟 => ?_
  have hs : Summable fun c : (SInt 𝔪)ˣ × (SP 𝔪 → ℤ) => A (e.symm (𝔟, c)) := hAe.prod_factor 𝔟
  rw [hs.tsum_prod]
  have hun := hasSum_unfold (𝔪 := 𝔪) (Q (g.gen 𝔟.1)) (fun k => hQi _ k) (hQs1 𝔟)
  refine ((σ.hasSum_iff.2 hun).congr_fun fun ε => ?_).tsum_eq
  simp only [Function.comp_apply, A, e, Equiv.coe_fn_symm_mk]
  refine tsum_congr fun k => integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hf_eq]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # L92M_Basic: Mellin transforms of smooth functions supported in `[a, b] ⊂ (0, ∞)`

For `g : ℝ → ℝ` continuous with `tsupport g ⊆ Icc a b`, `0 < a`, the Mellin transform of
`(g · : ℂ)` is entire and bounded on vertical strips; for smooth `g`, integration by parts
(`D g t = t g'(t)`, `mellin (D g) s = -s mellin g s`) gives decay faster than any power of `|Im s|`.
-/

namespace ArtinPrimitiveRoots.L92M

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval ContDiff

section General

variable {g : ℝ → ℝ} {a b : ℝ}

lemma vanish_of_tsupport (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (t : ℝ)
    (ht : t ∉ Ioo (a / 2) (max a b + 1)) : g t = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ht ?_
  have := hs h
  exact ⟨by linarith [this.1], by linarith [this.2, le_max_right a b]⟩

lemma lt_bounds (ha : 0 < a) : 0 < a / 2 ∧ a / 2 < max a b + 1 :=
  ⟨by linarith, by linarith [le_max_left a b]⟩

lemma cpow_continuousOn (s : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (Ioi 0) :=
  fun _ ht => (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).continuousWithinAt

lemma hasCompactSupport_of_tsupport (hs : tsupport g ⊆ Icc a b) : HasCompactSupport g :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hs

lemma mellinConvergent_of_tsupport (hc : Continuous g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (s : ℂ) : MellinConvergent (fun t => (g t : ℂ)) s := by
  unfold MellinConvergent
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (g t : ℂ)) (Icc (a / 2) (max a b + 1)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ((cpow_continuousOn (s - 1)).mono ?_).smul (continuous_ofReal.comp hc).continuousOn
    intro t ht
    exact lt_of_lt_of_le (lt_bounds (b := b) ha).1 ht.1
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro t ht
  have : t ∉ Ioo (a / 2) (max a b + 1) := fun h' => ht.2 (Ioo_subset_Icc_self h')
  simp [vanish_of_tsupport ha hs t this]

lemma mellin_eq_intervalIntegral (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (s : ℂ) :
    mellin (fun t => (g t : ℂ)) s =
      ∫ t in (a / 2)..(max a b + 1), (t : ℂ) ^ (s - 1) * (g t : ℂ) := by
  rw [mellin, intervalIntegral.integral_of_le (lt_bounds (b := b) ha).2.le]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · intro t ht
    exact lt_trans (lt_bounds (b := b) ha).1 ht.1
  · intro t ht
    have : t ∉ Ioo (a / 2) (max a b + 1) := fun h' => ht.2 ⟨h'.1, h'.2.le⟩
    simp [vanish_of_tsupport ha hs t this]

lemma mellin_differentiable_of_tsupport (hc : Continuous g) (ha : 0 < a)
    (hs : tsupport g ⊆ Icc a b) : Differentiable ℂ (mellin (fun t => (g t : ℂ))) := by
  intro s
  have hF : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0) :=
    (continuous_ofReal.comp hc).locallyIntegrable.locallyIntegrableOn _
  have htop : (fun t => (g t : ℂ)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (max a b + 1)] with t ht
    simp [vanish_of_tsupport ha hs t fun h => absurd h.2 (not_lt.mpr ht.le)]
  have hbot : (fun t => (g t : ℂ)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a / 2 by linarith)] with t ht
    simp [vanish_of_tsupport ha hs t fun h => absurd h.1 (not_lt.mpr ht.2.le)]
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hF
    ((isBigO_zero _ _).congr' htop.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hbot.symm EventuallyEq.rfl) (by linarith)

/-- Boundedness of the Mellin transform on vertical strips. -/
lemma mellin_bounded_strip (hc : Continuous g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (σ₁ σ₂ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C := by
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_of_tsupport hs)
  have hcomp : IsCompact (Icc σ₁ σ₂ ×ˢ Icc α β) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ (p.1 - 1)) (Icc σ₁ σ₂ ×ˢ Icc α β) := by
    intro p hp
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.rpow continuousAt_snd (continuousAt_fst.sub continuousAt_const) ?_
    left
    have := hp.2.1
    exact ne_of_gt (lt_of_lt_of_le hαβ.1 this)
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max (B * max M 0 * (β - α)) 0, le_max_right _ _, fun s h1 h2 => ?_⟩
  rw [mellin_eq_intervalIntegral ha hs]
  refine le_trans ?_ (le_max_left _ _)
  have : ∀ t ∈ Ι α β, ‖(t : ℂ) ^ (s - 1) * (g t : ℂ)‖ ≤ B * max M 0 := by
    intro t ht
    have ht2 : t ∈ Ioc α β := by rwa [uIoc_of_le hαβ.2.le] at ht
    have ht' : t ∈ Icc α β := ⟨ht2.1.le, ht2.2⟩
    have htpos : 0 < t := lt_of_lt_of_le hαβ.1 ht'.1
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos, norm_real]
    have hb := hB (s.re, t) ⟨⟨h1, h2⟩, ht'⟩
    simp only [Real.norm_eq_abs] at hb
    rw [abs_of_nonneg (Real.rpow_nonneg htpos.le _)] at hb
    have hgt : ‖g t‖ ≤ max M 0 := le_trans (hM t) (le_max_left _ _)
    exact mul_le_mul hb hgt (norm_nonneg _) (le_trans (Real.rpow_nonneg htpos.le _) hb)
  have := intervalIntegral.norm_integral_le_of_norm_le_const this
  rwa [abs_of_pos (sub_pos.mpr hαβ.2)] at this

end General

section IBP

variable {g : ℝ → ℝ} {a b : ℝ}

/-- `D g t = t g'(t)`. -/
noncomputable def Dop (g : ℝ → ℝ) : ℝ → ℝ := fun t => t * deriv g t

lemma tsupport_Dop_subset (g : ℝ → ℝ) : tsupport (Dop g) ⊆ tsupport g :=
  (tsupport_mul_subset_right (f := fun t => t)).trans tsupport_deriv_subset

lemma contDiff_Dop (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (Dop g) :=
  contDiff_id.mul (contDiff_infty_iff_deriv.mp hg).2

lemma hasDerivAt_ofReal_cpow (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t := by
  have h1 : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have := ((hasDerivAt_id (t : ℂ)).cpow_const (c := s) h1).comp_ofReal
  simpa using this

/-- Integration by parts: `mellin (t g'(t)) s = -s mellin g s`. -/
lemma mellin_Dop (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b) (s : ℂ) :
    mellin (fun t => (Dop g t : ℂ)) s = -s * mellin (fun t => (g t : ℂ)) s := by
  have hs' : tsupport (Dop g) ⊆ Icc a b := (tsupport_Dop_subset g).trans hs
  rw [mellin_eq_intervalIntegral ha hs', mellin_eq_intervalIntegral ha hs]
  set α := a / 2
  set β := max a b + 1
  have hαβ := lt_bounds (b := b) ha
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcd : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hpos : ∀ t ∈ uIcc α β, 0 < t := by
    intro t ht
    rw [uIcc_of_le hαβ.2.le] at ht
    exact lt_of_lt_of_le hαβ.1 ht.1
  have h1 : ∫ t in α..β, (t : ℂ) ^ (s - 1) * ((Dop g t : ℝ) : ℂ) =
      ∫ t in α..β, (t : ℂ) ^ s * ((deriv g t : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos t ht).ne'
    simp only [Dop, ofReal_mul]
    rw [← mul_assoc]
    congr 1
    conv_rhs => rw [show s = (s - 1) + 1 by ring, cpow_add _ _ htc, cpow_one]
  rw [h1]
  have hu : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t :=
    fun t ht => hasDerivAt_ofReal_cpow s (hpos t ht)
  have hv : ∀ t ∈ uIcc α β, HasDerivAt (fun y : ℝ => (g y : ℂ)) ((deriv g t : ℝ) : ℂ) t :=
    fun t _ => (hdiff t).hasDerivAt.ofReal_comp
  have hu' : IntervalIntegrable (fun t : ℝ => s * (t : ℂ) ^ (s - 1)) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul ((cpow_continuousOn (s - 1)).mono fun t ht => hpos t ht)
  have hv' : IntervalIntegrable (fun t : ℝ => ((deriv g t : ℝ) : ℂ)) volume α β :=
    (continuous_ofReal.comp hcd).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hgα : g α = 0 := vanish_of_tsupport ha hs α (fun h => lt_irrefl _ h.1)
  have hgβ : g β = 0 := vanish_of_tsupport ha hs β (fun h => lt_irrefl _ h.2)
  rw [hgα, hgβ]
  simp only [ofReal_zero, mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

lemma mellin_Dop_iterate (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (N : ℕ) : ContDiff ℝ ∞ (Dop^[N] g) ∧ tsupport (Dop^[N] g) ⊆ Icc a b ∧
      ∀ s : ℂ, mellin (fun t => (Dop^[N] g t : ℂ)) s = (-s) ^ N * mellin (fun t => (g t : ℂ)) s := by
  induction N with
  | zero => exact ⟨hg, hs, fun s => by simp⟩
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨contDiff_Dop h1, (tsupport_Dop_subset _).trans h2, fun s => ?_⟩
    rw [mellin_Dop h1 ha h2, h3, pow_succ]
    ring

lemma one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + u ^ N) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg hu N])
  · calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * u ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + u ^ N) := by gcongr; linarith

/-- Rapid decay on vertical strips, with a nonnegative constant. -/
lemma mellin_decay_aux (hg : ContDiff ℝ ∞ g) (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (N : ℕ) (σ₁ σ₂ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C / (1 + |s.im|) ^ N := by
  obtain ⟨h1, h2, h3⟩ := mellin_Dop_iterate hg ha hs N
  obtain ⟨C₀, hC₀, hb₀⟩ := mellin_bounded_strip hg.continuous ha hs σ₁ σ₂
  obtain ⟨C₁, hC₁, hb₁⟩ := mellin_bounded_strip h1.continuous ha h2 σ₁ σ₂
  refine ⟨2 ^ N * (C₀ + C₁), by positivity, fun s hs1 hs2 => ?_⟩
  have hpos : 0 < (1 + |s.im|) ^ N := by positivity
  rw [le_div_iff₀ hpos]
  have e1 : ‖s‖ ^ N * ‖mellin (fun t => (g t : ℂ)) s‖ ≤ C₁ := by
    have := hb₁ s hs1 hs2
    rw [h3 s, norm_mul, norm_pow, norm_neg] at this
    exact this
  have e0 := hb₀ s hs1 hs2
  have him : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  calc ‖mellin (fun t => (g t : ℂ)) s‖ * (1 + |s.im|) ^ N
      ≤ ‖mellin (fun t => (g t : ℂ)) s‖ * (2 ^ N * (1 + |s.im| ^ N)) := by
        gcongr; exact one_add_pow_le _ (abs_nonneg _) N
    _ ≤ ‖mellin (fun t => (g t : ℂ)) s‖ * (2 ^ N * (1 + ‖s‖ ^ N)) := by
        gcongr
    _ = 2 ^ N * (‖mellin (fun t => (g t : ℂ)) s‖ + ‖s‖ ^ N * ‖mellin (fun t => (g t : ℂ)) s‖) := by
        ring
    _ ≤ 2 ^ N * (C₀ + C₁) := by gcongr

end IBP

section Main

variable (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
  (hab : tsupport f ⊆ Set.Icc a b)

include hf ha hab

/-- M3a -/
theorem mellin_differentiable : Differentiable ℂ (mellin (fun u : ℝ => (f u : ℂ))) :=
  mellin_differentiable_of_tsupport hf.continuous ha hab

/-- M3b' -/
theorem mellin_decay_rpow (A σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun u : ℝ => (f u : ℂ)) s‖ ≤ C * (1 + |s.im|) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := mellin_decay_aux hf ha hab ⌈A⌉₊ σ₁ σ₂
  refine ⟨C, fun s h1 h2 => le_trans (hC s h1 h2) ?_⟩
  have hb : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hb (by linarith [Nat.le_ceil A])) hC0

end Main

end ArtinPrimitiveRoots.L92M

end
end

section
section
/-!
# L3P_Rho: the norm cut-off `ρ`

`ρ` is a smooth bump on `[1/2, 3/2]`. Its Mellin transform is entire, decays faster than any power
on vertical strips (L92M), is positive at real points, and inverts back to `ρ` on every line.
-/

namespace ArtinPrimitiveRoots.L3P

open MeasureTheory Complex
open scoped Real

/-- The bump at `1` with radii `1/4 < 1/2`. -/
noncomputable def rhoB : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The cut-off `ρ`. -/
noncomputable def rho (t : ℝ) : ℝ := rhoB t

theorem rho_nonneg (t : ℝ) : 0 ≤ rho t := rhoB.nonneg

theorem rho_le_one (t : ℝ) : rho t ≤ 1 := rhoB.le_one

theorem contDiff_rho : ContDiff ℝ (⊤ : ℕ∞) rho := rhoB.contDiff

theorem continuous_rho : Continuous rho := rhoB.continuous

theorem tsupport_rho : tsupport rho ⊆ Set.Icc (1 / 2) (3 / 2) := by
  have : tsupport rho = Metric.closedBall (1 : ℝ) (1 / 2) := rhoB.tsupport_eq
  rw [this, Real.closedBall_eq_Icc]
  norm_num

theorem rho_eq_zero {t : ℝ} (ht : t < 1 / 2 ∨ 3 / 2 < t) : rho t = 0 := by
  by_contra h
  have := tsupport_rho (subset_tsupport _ h)
  rw [Set.mem_Icc] at this
  rcases ht with ht | ht <;> linarith [this.1, this.2]

/-- The Mellin transform of `ρ`. -/
noncomputable def rhoM (s : ℂ) : ℂ := mellin (fun t : ℝ => (rho t : ℂ)) s

theorem differentiable_rhoM : Differentiable ℂ rhoM :=
  L92M.mellin_differentiable rho contDiff_rho (1 / 2) (3 / 2) (by norm_num) tsupport_rho

theorem rhoM_decay (A σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖rhoM s‖ ≤ C * (1 + |s.im|) ^ (-A) :=
  L92M.mellin_decay_rpow rho contDiff_rho (1 / 2) (3 / 2) (by norm_num) tsupport_rho A σ₁ σ₂

theorem mellinConvergent_rho (s : ℂ) : MellinConvergent (fun t : ℝ => (rho t : ℂ)) s :=
  L92M.mellinConvergent_of_tsupport continuous_rho (by norm_num) tsupport_rho s

theorem verticalIntegrable_rhoM (σ : ℝ) : VerticalIntegrable rhoM σ := by
  obtain ⟨C, hC⟩ := rhoM_decay 2 σ σ
  have hcont : Continuous fun y : ℝ => rhoM (σ + y * I) :=
    differentiable_rhoM.continuous.comp (continuous_const.add (continuous_ofReal.mul continuous_const))
  refine Integrable.mono' ((integrable_one_add_norm (E := ℝ) (r := 2) (by norm_num)).const_mul C)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h := hC (σ + y * I) (by simp) (by simp)
  have him : ((σ : ℂ) + y * I).im = y := by simp
  rw [him] at h
  simpa [Real.norm_eq_abs] using h

/-- Mellin inversion for `ρ` on every line. -/
theorem mellinInv_rhoM (σ : ℝ) {x : ℝ} (hx : 0 < x) : mellinInv σ rhoM x = rho x := by
  have := mellinInv_mellin_eq σ (fun t : ℝ => (rho t : ℂ)) hx (mellinConvergent_rho σ)
    (verticalIntegrable_rhoM σ) (continuous_ofReal.comp continuous_rho).continuousAt
  exact this

/-- `ρ̃` is positive at real points. -/
theorem rhoM_ofReal_pos (σ : ℝ) : 0 < (rhoM σ).re ∧ (rhoM σ).im = 0 := by
  have h : rhoM σ = ((∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * rho t : ℝ) : ℂ) := by
    rw [rhoM, mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul]
    rw [ofReal_mul, ofReal_cpow (le_of_lt ht)]
    push_cast; rfl
  rw [h, ofReal_re, ofReal_im]
  refine ⟨?_, rfl⟩
  have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * rho t) (Set.Ioi 0) := by
    have := (mellinConvergent_rho (σ : ℂ)).norm
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rho_nonneg t)]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have hsub : Set.Ioo (3 / 4 : ℝ) (5 / 4) ⊆ Function.support (fun t : ℝ => t ^ (σ - 1) * rho t) ∩
        Set.Ioi 0 := by
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      refine ⟨?_, ht0⟩
      refine mul_ne_zero (Real.rpow_pos_of_pos ht0 _).ne' ?_
      refine (rhoB.pos_of_mem_ball ?_).ne'
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      simp only [rhoB]
      constructor <;> linarith [ht.1, ht.2]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo]; norm_num
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    exact mul_nonneg (Real.rpow_pos_of_pos ht _).le (rho_nonneg t)

theorem rhoM_ofReal_ne_zero (σ : ℝ) : rhoM σ ≠ 0 := fun h => by
  have := (rhoM_ofReal_pos σ).1; rw [h, zero_re] at this; exact lt_irrefl _ this

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Weight: the weights `V` and `M`

`V(X) = c_β^{r−1} ∫ χ(t) ρ(e^t / X) dt` (`= ∫ Φ(b) ρ(e^{Σb}/X) db`) is a probe weight, and
`M(z) = A d^{z−1} ρ̃(z − 1) W(z) Z(φ̂, z)` is a Mellin weight with `M(1/6) ≠ 0`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap Convolution

set_option linter.unusedSectionVars false

/-! ### The probe weight `V` -/

section V

variable (n : ℕ)

/-- `V(X) = c_β^n ∫ χ(t) ρ(e^t / X) dt`. -/
noncomputable def Vw (X : ℝ) : ℝ := cB ^ n * ∫ t, chi t * rho (Real.exp t / X)

theorem Vw_eq_zero {X : ℝ} (hX : X < Real.exp (-1) / 2 ∨ 4 * Real.exp 2 < X) : Vw n X = 0 := by
  rw [Vw]
  suffices h : ∀ t, chi t * rho (Real.exp t / X) = 0 by simp [h]
  intro t
  by_cases ht : t ≤ -1 ∨ 2 ≤ t
  · rw [chi_eq_zero ht, zero_mul]
  · push Not at ht
    rw [rho_eq_zero, mul_zero]
    rcases hX with hX | hX
    · rcases le_or_gt X 0 with hX0 | hX0
      · left
        have : Real.exp t / X ≤ 0 := div_nonpos_of_nonneg_of_nonpos (Real.exp_pos t).le hX0
        linarith
      · right
        rw [lt_div_iff₀ hX0]
        have h1 : Real.exp (-1) < Real.exp t := Real.exp_lt_exp.2 ht.1
        nlinarith
    · left
      have hX0 : 0 < X := by linarith [Real.exp_pos 2]
      rw [div_lt_iff₀ hX0]
      have h1 : Real.exp t < Real.exp 2 := Real.exp_lt_exp.2 ht.2
      nlinarith [Real.exp_pos 2]

/-- The log-variable version `g(u) = ∫ χ(t) ρ(e^{t−u}) dt`, a convolution. -/
noncomputable def rr (v : ℝ) : ℝ := rho (Real.exp (-v))

theorem contDiff_rr : ContDiff ℝ (⊤ : ℕ∞) rr :=
  contDiff_rho.comp (Real.contDiff_exp.comp contDiff_neg)

theorem hasCompactSupport_rr : HasCompactSupport rr := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -Real.log 2) (b := Real.log 2)) fun v hv => ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  rw [rr, rho_eq_zero]
  rcases hv with hv | hv
  · right
    have : Real.exp (Real.log 2) < Real.exp (-v) := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_log (by norm_num)] at this
    linarith
  · left
    have : Real.exp (-v) < Real.exp (-Real.log 2) := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)] at this
    linarith

theorem contDiff_conv :
    ContDiff ℝ (⊤ : ℕ∞) (chi ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] rr) :=
  hasCompactSupport_rr.contDiff_convolution_right _ continuous_chi.locallyIntegrable contDiff_rr

theorem Vw_eq_conv {X : ℝ} (hX : 0 < X) :
    Vw n X = cB ^ n * (chi ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] rr) (Real.log X) := by
  rw [Vw, convolution_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [rr, neg_sub]
  rw [Real.exp_sub, Real.exp_log hX]

theorem isProbeWeight_Vw : IsProbeWeight (Vw n) := by
  have hzero : ∀ X ∉ Set.Icc (Real.exp (-1) / 2) (4 * Real.exp 2), Vw n X = 0 := fun X hX => by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hX
    exact Vw_eq_zero n hX
  have hts : tsupport (Vw n) ⊆ Set.Icc (Real.exp (-1) / 2) (4 * Real.exp 2) :=
    closure_minimal (fun X hX => by_contra fun h => hX (hzero X h)) isClosed_Icc
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.exp (-1) / 2) (b := 4 * Real.exp 2)) ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun X => ?_
    by_cases hX : 0 < X
    · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun Y => cB ^ n *
          (chi ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] rr) (Real.log Y)) X :=
        contDiffAt_const.mul (contDiff_conv.contDiffAt.comp X (Real.contDiffAt_log.2 hX.ne'))
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hX] with Y hY
      exact Vw_eq_conv n hY
    · push Not at hX
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      have hlt : X < Real.exp (-1) / 2 := lt_of_le_of_lt hX (by positivity)
      filter_upwards [gt_mem_nhds hlt] with Y hY
      exact Vw_eq_zero n (Or.inl hY)
  · exact (subset_tsupport _).trans hts
  · exact hts.trans fun X hX => lt_of_lt_of_le (by positivity) hX.1

end V

/-! ### The Mellin weight `M` -/

section M

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
variable {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ) (hq : ∀ v, 1 < q v)
variable (dd Acst : ℝ)

/-- `φ̂` for the concrete test function. -/
noncomputable def phiHatS (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] :
    𝓢(mixedSpace K, ℂ) :=
  fourierS (phiS (K := K) contDiff_PhiT hasCompactSupport_PhiT)

theorem coe_phiHatS : ⇑(phiHatS K) = fourierM (phiF (PhiT (K := K))) := by
  rw [phiHatS, coe_fourierS]; rfl

/-- `M(z) = A d^{z−1} ρ̃(z−1) W(z) Z(φ̂, z)`. -/
noncomputable def Mw (z : ℂ) : ℂ :=
  Acst * Complex.exp ((z - 1) * Real.log dd) * rhoM (z - 1) * Wf q z *
    Zm (fourierM (phiF (PhiT (K := K)))) z

include hq in
theorem isMellinWeight_Mw : IsMellinWeight (Mw (K := K) q dd Acst) := by
  have hZ : Zm (fourierM (phiF (PhiT (K := K)))) = Zm (⇑(phiHatS K)) := by rw [coe_phiHatS]
  constructor
  · intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold Mw
    refine (((((differentiableAt_const _).mul ?_).mul ?_).mul ?_).mul ?_)
    · exact ((differentiableAt_id.sub_const 1).mul_const _).cexp
    · exact (differentiable_rhoM _).comp z (differentiableAt_id.sub_const 1)
    · exact (differentiableOn_Wf q hq z hz).differentiableAt (isOpen_lt continuous_const
        Complex.continuous_re |>.mem_nhds hz)
    · rw [hZ]
      exact (differentiableOn_Zm (phiHatS K) z hz).differentiableAt (isOpen_lt continuous_const
        Complex.continuous_re |>.mem_nhds hz)
  · intro a b A ha
    obtain ⟨C1, hC1⟩ := rhoM_decay A (a - 1) (b - 1)
    obtain ⟨C2, hC2⟩ := norm_Wf_le q hq (b := b) ha
    obtain ⟨C3, hC3⟩ := norm_Zm_le (phiHatS K) (b := b) ha
    set E := Real.exp ((|a| + |b| + 1) * |Real.log dd|)
    refine ⟨‖(Acst : ℂ)‖ * E * C1 * C2 * C3, fun z h1 h2 => ?_⟩
    unfold Mw
    rw [hZ]
    have hr : ‖rhoM (z - 1)‖ ≤ C1 * (1 + |z.im|) ^ (-A) := by
      have := hC1 (z - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith)
        (by rw [Complex.sub_re, Complex.one_re]; linarith)
      rwa [Complex.sub_im, Complex.one_im, sub_zero] at this
    have he : ‖Complex.exp ((z - 1) * Real.log dd)‖ ≤ E := by
      rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.sub_re, Complex.one_re]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (abs_sub _ _).trans ?_
      rw [abs_one]
      have : |z.re| ≤ |a| + |b| := by
        rw [abs_le]; constructor <;> [linarith [neg_abs_le a, le_abs_self b, abs_nonneg b];
          linarith [le_abs_self b, abs_nonneg a]]
      linarith
    have hW := hC2 z h1 h2
    have hZ3 := hC3 z h1 h2
    have hC1' : 0 ≤ C1 * (1 + |z.im|) ^ (-A) := (norm_nonneg _).trans hr
    have hC2' : 0 ≤ C2 := (norm_nonneg _).trans hW
    have hC3' : 0 ≤ C3 := (norm_nonneg _).trans hZ3
    simp only [norm_mul]
    calc ‖(Acst : ℂ)‖ * ‖Complex.exp ((z - 1) * Real.log dd)‖ * ‖rhoM (z - 1)‖ * ‖Wf q z‖ *
          ‖Zm (⇑(phiHatS K)) z‖
        ≤ ‖(Acst : ℂ)‖ * E * (C1 * (1 + |z.im|) ^ (-A)) * C2 * C3 := by gcongr
      _ = _ := by ring

include hq in
theorem Zm_phiHat_ne_zero : Zm (fourierM (phiF (PhiT (K := K)))) (1 / 6 : ℝ) ≠ 0 := by
  have h := Zm_exchange (K := K) (Φ := PhiT) contDiff_PhiT hasCompactSupport_PhiT
    ((1 / 6 : ℝ) : ℂ) (by simp) (by simp; norm_num)
  have h56 : (1 : ℂ) - ((1 / 6 : ℝ) : ℂ) = ((5 / 6 : ℝ) : ℂ) := by push_cast; ring
  rw [h56] at h
  intro h0
  rw [h0, zero_mul] at h
  have := mul_ne_zero (mul_ne_zero (show ((invC K : ℝ) : ℂ) ≠ 0 by exact_mod_cast invC_ne_zero)
    (Zm_phiF_PhiT_ne_zero (K := K) (1 / 6) (by norm_num)))
    (Zm_phiF_PhiT_ne_zero (K := K) (5 / 6) (by norm_num))
  rw [mul_assoc] at this
  exact this h.symm

include hq in
theorem Mw_ne_zero (hA : Acst ≠ 0) : Mw (K := K) q dd Acst (1 / 6) ≠ 0 := by
  have h16 : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by push_cast; ring
  unfold Mw
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast hA)
    (Complex.exp_ne_zero _)) ?_) ?_) ?_
  · have := rhoM_ofReal_ne_zero (1 / 6 - 1)
    convert this using 2; push_cast; ring
  · exact Wf_ne_zero q hq (by norm_num) (by norm_num)
  · rw [← h16]; exact Zm_phiHat_ne_zero q hq

end M

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_StarL: the left side of the class-form identity

`QL m (x, k) = ρ(T e^{Σx} N(k)) · 1[m ≠ 0, val m = k] c(m) Φ(x + ℓ(m))` is `U_S`-equivariant, and
`Σ_k ∫ QL (gen 𝔟) = c(gen 𝔟) V(N𝔟 / T)` with `V(X) = ∫ Φ(b) ρ(e^{Σb}/X) db`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

theorem sum_logK {x : F} (hx : x ≠ 0) :
    ∑ w, logK x w = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  rw [logK_eq_expMap_symm, sum_expMap_symm_apply hx]

theorem exp_sum_LxU (ε : (SInt 𝔪)ˣ) : Real.exp (∑ w, LxU ε w) = NN (qS (𝔪 := 𝔪)) (LkU ε) := by
  rw [LxU, sum_logK (unit_ne_zero ε), Real.exp_log, abs_norm_unit]; rfl
  have := abs_norm_unit ε
  rw [this]; exact NN_pos _ _

theorem NN_add {S : Type*} [Fintype S] (q : S → ℝ) (j j' : S → ℤ) :
    NN q (j + j') = NN q j * NN q j' := by
  simp only [NN, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, Real.exp_add]

theorem NN_sub {S : Type*} [Fintype S] (q : S → ℝ) (j j' : S → ℤ) :
    NN q (j - j') = NN q j / NN q j' := by
  rw [eq_div_iff (NN_pos q j').ne', ← NN_add, sub_add_cancel]

/-- The norm weight `ρ(T e^{Σx} N(k))`. -/
noncomputable def wt (T : ℝ) (x : realSpace F) (k : SP 𝔪 → ℤ) : ℝ :=
  rho (T * Real.exp (∑ w, x w) * NN (qS (𝔪 := 𝔪)) k)

theorem wt_shift (T : ℝ) (x : realSpace F) (k : SP 𝔪 → ℤ) (ε : (SInt 𝔪)ˣ) :
    wt T (x + LxU ε) (k - LkU ε) = wt T x k := by
  rw [wt, wt]
  congr 1
  simp only [Pi.add_apply, Finset.sum_add_distrib, Real.exp_add, exp_sum_LxU, NN_sub]
  have := NN_pos (qS (𝔪 := 𝔪)) (LkU ε)
  field_simp

/-- The left integrand. -/
noncomputable def QL (T : ℝ) (c : SInt 𝔪 → ℂ) (m : SInt 𝔪) (x : realSpace F) (k : SP 𝔪 → ℤ) : ℂ :=
  (wt T x k : ℂ) * (if (m : F) ≠ 0 ∧ valS (m : F) = k then c m * (PhiT (x + logK (m : F)) : ℂ) else 0)

theorem QL_zero (T : ℝ) (c : SInt 𝔪 → ℂ) (x : realSpace F) (k : SP 𝔪 → ℤ) : QL T c 0 x k = 0 := by
  simp [QL]

theorem QL_unit_mul (T : ℝ) (c : SInt 𝔪 → ℂ)
    (hcU : ∀ (ε : (SInt 𝔪)ˣ) (x : SInt 𝔪), c ((ε : SInt 𝔪) * x) = c x)
    (ε : (SInt 𝔪)ˣ) (m : SInt 𝔪) (x : realSpace F) (k : SP 𝔪 → ℤ) :
    QL T c ((ε : SInt 𝔪) * m) x k = QL T c m (x + LxU ε) (k - LkU ε) := by
  rw [QL, QL, wt_shift]
  congr 1
  have hε0 := unit_ne_zero ε
  have hmul : (((ε : SInt 𝔪) * m : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * (m : F) := rfl
  by_cases hm0 : (m : F) = 0
  · rw [if_neg (fun h => h.1 (by rw [hmul, hm0, mul_zero])), if_neg (fun h => h.1 hm0)]
  · rw [hmul, valS_mul hε0 hm0, logK_mul hε0 hm0, hcU]
    have h1 : (((ε : SInt 𝔪) : F) * (m : F) ≠ 0 ∧ valS (𝔪 := 𝔪) ((ε : SInt 𝔪) : F) + valS (m : F) = k) ↔
        ((m : F) ≠ 0 ∧ valS (𝔪 := 𝔪) (m : F) = k - LkU ε) := by
      constructor
      · rintro ⟨-, h⟩; exact ⟨hm0, by rw [← h]; simp [LkU]⟩
      · rintro ⟨-, h⟩; exact ⟨mul_ne_zero hε0 hm0, by rw [h]; simp [LkU]⟩
    simp only [h1]
    congr 2
    rw [LxU]; abel_nf

theorem continuous_wt (T : ℝ) (k : SP 𝔪 → ℤ) : Continuous fun x : realSpace F => wt T x k :=
  continuous_rho.comp ((continuous_const.mul (Real.continuous_exp.comp
    (continuous_finsetSum _ fun w _ => continuous_apply w))).mul continuous_const)

theorem hasCompactSupport_PhiT_add (a : realSpace F) :
    HasCompactSupport fun x : realSpace F => PhiT (x + a) := by
  have := hasCompactSupport_PhiT (K := F)
  exact this.comp_homeomorph (Homeomorph.addRight a)

theorem integrable_QL (T : ℝ) (c : SInt 𝔪 → ℂ) (m : SInt 𝔪) (k : SP 𝔪 → ℤ) :
    Integrable fun x => QL T c m x k := by
  by_cases h : (m : F) ≠ 0 ∧ valS (m : F) = k
  · simp only [QL, if_pos h]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp (continuous_wt T k)).mul (continuous_const.mul
        (Complex.continuous_ofReal.comp (contDiff_PhiT.continuous.comp
          (continuous_id.add continuous_const))))
    · exact (((hasCompactSupport_PhiT_add (logK (m : F))).comp_left Complex.ofReal_zero).mul_left
        |>.mul_left)
  · simp only [QL, if_neg h, mul_zero]
    exact integrable_zero _ _ _

/-- `V(X) = ∫ Φ(b) ρ(e^{Σb} / X) db`. -/
noncomputable def Vt (X : ℝ) : ℝ := ∫ b : realSpace F, PhiT b * rho (Real.exp (∑ w, b w) / X)

theorem Vt_eq_Vw (X : ℝ) : Vt (F := F) X = Vw (Fintype.card {w : InfinitePlace F // w ≠ w0 F}) X := by
  have h := integral_PhiT_mul (K := F) (fun t => (rho (Real.exp t / X) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_rho.comp (Real.continuous_exp.div_const X)))
  rw [Vt, Vw]
  have h2 : ((∫ b : realSpace F, PhiT b * rho (Real.exp (∑ w, b w) / X) : ℝ) : ℂ) =
      ((cB ^ Fintype.card {w : InfinitePlace F // w ≠ w0 F} *
        ∫ t, chi t * rho (Real.exp t / X) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    rw [← integral_complex_ofReal]
    push_cast
    convert h using 2
  exact_mod_cast h2

variable {ι : F →+* ℂ}

theorem tsum_QL_gen (T : ℝ) (hT : 0 < T) (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) :
    ∑' k, ∫ x, QL T c (g.gen 𝔟.1) x k =
      c (g.gen 𝔟.1) * (Vt (F := F) (Ideal.absNorm 𝔟.1 / T) : ℂ) := by
  set m := g.gen 𝔟.1
  have hm0 := gen_ne_zero g 𝔟
  rw [tsum_eq_single (valS (m : F))]
  · have hc : ((m : F) ≠ 0 ∧ valS (𝔪 := 𝔪) (m : F) = valS (m : F)) := ⟨hm0, rfl⟩
    have hm0' : ¬ ((m : F) = 0) := hm0
    simp only [QL, hm0', ne_eq, not_false_eq_true, if_true, and_self]
    simp_rw [← mul_assoc, mul_comm _ (c m), mul_assoc]
    rw [integral_const_mul]
    congr 1
    rw [Vt, ← integral_complex_ofReal]
    have := integral_add_right_eq_self (μ := (volume : Measure (realSpace F)))
      (fun x => ((wt T (x - logK (m : F)) (valS (𝔪 := 𝔪) (m : F)) : ℝ) : ℂ) * (PhiT x : ℂ)) (logK (m : F))
    simp only [add_sub_cancel_right] at this
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only []
    push_cast
    rw [mul_comm]
    congr 2
    -- the norm bookkeeping
    have hN : ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟.1 : ℝ) *
        NN (qS (𝔪 := 𝔪)) (valS (m : F)) := abs_norm_eq 𝔟.2 (g.span_gen 𝔟.1 𝔟.2)
    have hsum : ∑ w, logK (m : F) w = Real.log ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) :=
      sum_logK hm0
    have h1 := NN_pos (qS (𝔪 := 𝔪)) (valS (m : F))
    have h0 : Ideal.absNorm 𝔟.1 ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔟.2.1
    have h2 : (0 : ℝ) < Ideal.absNorm 𝔟.1 := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hpos : (0 : ℝ) < ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) := by rw [hN]; positivity
    rw [wt]
    congr 1
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Real.exp_sub]
    rw [hsum, Real.exp_log hpos, hN]
    field_simp
  · intro k hk
    have hc : ¬((m : F) ≠ 0 ∧ valS (𝔪 := 𝔪) (m : F) = k) := fun h => hk h.2.symm
    simp only [QL]
    simp_rw [if_neg hc, mul_zero, integral_zero]

theorem PhiT_ne_zero_sum {b : realSpace F} (h : PhiT b ≠ 0) : -1 < ∑ w, b w ∧ ∑ w, b w < 2 := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  exact h (by rw [PhiT, chi_eq_zero hc, zero_mul])

theorem wt_gen (T : ℝ) (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) (x : realSpace F) :
    wt T x (valS (𝔪 := 𝔪) ((g.gen 𝔟.1 : SInt 𝔪) : F)) =
      rho (T * Real.exp (∑ w, (x + logK ((g.gen 𝔟.1 : SInt 𝔪) : F)) w) / Ideal.absNorm 𝔟.1) := by
  set m := g.gen 𝔟.1
  have hm0 := gen_ne_zero g 𝔟
  have hN : ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟.1 : ℝ) *
      NN (qS (𝔪 := 𝔪)) (valS (m : F)) := abs_norm_eq 𝔟.2 (g.span_gen 𝔟.1 𝔟.2)
  have hsum : ∑ w, logK (m : F) w = Real.log ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) := sum_logK hm0
  have h1 := NN_pos (qS (𝔪 := 𝔪)) (valS (m : F))
  have h0 : Ideal.absNorm 𝔟.1 ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔟.2.1
  have h2 : (0 : ℝ) < Ideal.absNorm 𝔟.1 := by exact_mod_cast Nat.pos_of_ne_zero h0
  have hpos : (0 : ℝ) < ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) := by rw [hN]; positivity
  rw [wt]
  congr 1
  simp only [Pi.add_apply, Finset.sum_add_distrib, Real.exp_add]
  rw [hsum, Real.exp_log hpos, hN]
  field_simp

theorem QL_gen_eq_zero (T : ℝ) (hT : 0 < T) (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪)
    (h𝔟 : 2 * T * Real.exp 2 ≤ Ideal.absNorm 𝔟.1) (x : realSpace F) (k : SP 𝔪 → ℤ) :
    QL T c (g.gen 𝔟.1) x k = 0 := by
  simp only [QL]
  split_ifs with h
  · obtain ⟨-, rfl⟩ := h
    by_cases hP : PhiT (x + logK ((g.gen 𝔟.1 : SInt 𝔪) : F)) = 0
    · rw [hP]; simp
    · have hs := PhiT_ne_zero_sum hP
      rw [wt_gen, rho_eq_zero, Complex.ofReal_zero, zero_mul]
      left
      have hp : 0 < 2 * T * Real.exp 2 := by positivity
      have h2 : (0 : ℝ) < Ideal.absNorm 𝔟.1 := by linarith
      rw [div_lt_iff₀ h2]
      have := Real.exp_lt_exp.2 hs.2
      nlinarith [Real.exp_pos (∑ w, (x + logK ((g.gen 𝔟.1 : SInt 𝔪) : F)) w)]
  · rw [mul_zero]

theorem summable_QL (T : ℝ) (hT : 0 < T) (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) :
    Summable fun 𝔟 : Ext 𝔪 => ∑' k, ∫ x, ‖QL T c (g.gen 𝔟.1) x k‖ := by
  set B := ⌈2 * T * Real.exp 2⌉₊
  have hfin : {𝔟 : Ext 𝔪 | Ideal.absNorm 𝔟.1 ≤ B}.Finite := by
    have := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) B
    exact (this.preimage Subtype.val_injective.injOn)
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun 𝔟 h𝔟 => ?_
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at h𝔟
  have h2 : 2 * T * Real.exp 2 ≤ Ideal.absNorm 𝔟.1 := by
    have := Nat.le_ceil (2 * T * Real.exp 2)
    have h3 : (B : ℝ) < Ideal.absNorm 𝔟.1 := by exact_mod_cast h𝔟
    linarith
  simp [QL_gen_eq_zero T hT c g 𝔟 h2]

theorem summable_QL_k (T : ℝ) (c : SInt 𝔪 → ℂ) (m : SInt 𝔪) :
    Summable fun k => ∫ x, ‖QL T c m x k‖ := by
  refine summable_of_ne_finset_zero (s := {valS (m : F)}) fun k hk => ?_
  rw [Finset.mem_singleton] at hk
  have : ∀ x, QL T c m x k = 0 := fun x => by
    simp only [QL]; rw [if_neg (fun h => hk h.2.symm), mul_zero]
  simp [this]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Inv: `mellinInv 2 M = D`

`D(X) = (A/X) Σ_j Om(j) ∫ Φ̂(b) e^{Σb} ρ(X N(j) e^{−Σb} / d) db`: expand `W(z) Z(φ̂, z)` on the
line `Re z = 2`, swap the sum over `j`, the integral over `b` and the integral over the line, and
invert the Mellin transform of `ρ` on `Re = 1`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Complex
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

theorem cpow_ofReal_pos {Y : ℝ} (hY : 0 < Y) (w : ℂ) : (Y : ℂ) ^ w = cexp (w * Real.log Y) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hY.ne'), ← ofReal_log hY.le, mul_comm]

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
variable {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ) (hq : ∀ v, 1 < q v)
variable (dd Acst : ℝ) (hd : 0 < dd)

/-- The dual profile `D(X)`. -/
noncomputable def Dw (X : ℝ) : ℂ :=
  ((Acst / X : ℝ) : ℂ) * ∑' j : S → ℤ, (Om q j : ℂ) * ∫ b : realSpace K,
    PhiHat PhiT b * (Real.exp (∑ w, b w) : ℂ) *
      (rho (X * NN q j * Real.exp (-∑ w, b w) / dd) : ℂ)

/-- `log Y` for `Y = X N(j) e^{−Σb} / d`. -/
noncomputable def LY (X : ℝ) (j : S → ℤ) (b : realSpace K) : ℝ :=
  Real.log X + ∑ v, (j v : ℝ) * lq q v - ∑ w, b w - Real.log dd

include hd in
theorem exp_LY {X : ℝ} (hX : 0 < X) (j : S → ℤ) (b : realSpace K) :
    Real.exp (LY q dd X j b) = X * NN q j * Real.exp (-∑ w, b w) / dd := by
  rw [LY, Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hX, Real.exp_log hd, NN,
    Real.exp_neg]
  field_simp

/-- The integrand on `j × b × τ`. -/
noncomputable def GG (X : ℝ) (j : S → ℤ) (b : realSpace K) (τ : ℝ) : ℂ :=
  (Acst : ℂ) * (Om q j : ℂ) * PhiHat PhiT b * cexp (-(Real.log X : ℂ) + ∑ w, (b w : ℂ)) *
    (cexp (-(1 + τ * I) * LY q dd X j b) * rhoM (1 + τ * I))

theorem Zm_phiHat_eq (z : ℂ) :
    Zm (fourierM (phiF (PhiT (K := K)))) z =
      ∫ b : realSpace K, PhiHat PhiT b * cexp (z * ∑ w, (b w : ℂ)) := rfl

theorem GG_eq_aux {X : ℝ} (hX : 0 < X) (τ : ℝ) (j : S → ℤ) (b : realSpace K) :
    ((X : ℂ) ^ (-(((2 : ℝ) : ℂ) + τ * I)) * (Acst : ℂ) *
        cexp ((((2 : ℝ) : ℂ) + τ * I - 1) * Real.log dd) * rhoM (((2 : ℝ) : ℂ) + τ * I - 1)) *
      ((Om q j : ℂ) * Ncp q j (1 - (((2 : ℝ) : ℂ) + τ * I))) *
      (PhiHat PhiT b * cexp ((((2 : ℝ) : ℂ) + τ * I) * ∑ w, (b w : ℂ))) =
    GG q dd Acst X j b τ := by
  rw [GG, cpow_ofReal_pos hX, Ncp, LY]
  have h1 : ((2 : ℝ) : ℂ) + τ * I - 1 = 1 + τ * I := by push_cast; ring
  rw [h1]
  have e : ∀ A B C D E F G H : ℂ, (cexp A * B * cexp C * D) * (E * cexp F) * (G * cexp H) =
      B * E * G * D * cexp (A + C + F + H) := by
    intro A B C D E F G H
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring
  rw [e]
  have e2 : ∀ B E G D A F : ℂ, B * E * G * cexp A * (cexp F * D) = B * E * G * D * cexp (A + F) := by
    intro B E G D A F; rw [Complex.exp_add]; ring
  rw [e2]
  congr 2
  push_cast
  ring

include hq in
theorem cpow_smul_Mw {X : ℝ} (hX : 0 < X) (τ : ℝ) :
    (X : ℂ) ^ (-(((2 : ℝ) : ℂ) + τ * I)) • Mw (K := K) q dd Acst (((2 : ℝ) : ℂ) + τ * I) =
      ∑' j : S → ℤ, ∫ b : realSpace K, GG q dd Acst X j b τ := by
  set z : ℂ := ((2 : ℝ) : ℂ) + τ * I
  have hz : 0 < z.re := by simp [z]
  have hW := (hasSum_Om q hq z hz).1
  unfold Mw
  rw [← hW.tsum_eq, Zm_phiHat_eq, smul_eq_mul]
  set C : ℂ := (X : ℂ) ^ (-z) * (Acst : ℂ) * cexp ((z - 1) * Real.log dd) * rhoM (z - 1)
  have : (X : ℂ) ^ (-z) * ((Acst : ℂ) * cexp ((z - 1) * Real.log dd) * rhoM (z - 1) *
      (∑' j, (Om q j : ℂ) * Ncp q j (1 - z)) *
        ∫ b : realSpace K, PhiHat PhiT b * cexp (z * ∑ w, (b w : ℂ))) =
      C * (∑' j, (Om q j : ℂ) * Ncp q j (1 - z)) *
        ∫ b : realSpace K, PhiHat PhiT b * cexp (z * ∑ w, (b w : ℂ)) := by
    simp only [C]; ring
  rw [this, ← tsum_mul_left, ← tsum_mul_right]
  refine tsum_congr fun j => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  exact GG_eq_aux q dd Acst hX τ j b

theorem continuous_PhiHat : Continuous (PhiHat (PhiT (K := K))) := by
  have := continuous_prof (phiHatS K)
  rwa [coe_phiHatS] at this

theorem continuous_LY (X : ℝ) (j : S → ℤ) : Continuous (LY (K := K) q dd X j) :=
  (continuous_const.sub (continuous_finsetSum _ fun w _ => continuous_apply w)).sub continuous_const

theorem continuous_GG (X : ℝ) (j : S → ℤ) :
    Continuous fun p : realSpace K × ℝ => GG q dd Acst X j p.1 p.2 := by
  unfold GG
  refine (((continuous_const.mul (continuous_PhiHat.comp continuous_fst)).mul ?_).mul ?_)
  · exact Complex.continuous_exp.comp (continuous_const.add (continuous_finsetSum _ fun w _ =>
      Complex.continuous_ofReal.comp ((continuous_apply w).comp continuous_fst)))
  · refine (Complex.continuous_exp.comp ?_).mul ?_
    · exact ((continuous_const.add (Complex.continuous_ofReal.comp continuous_snd |>.mul
        continuous_const)).neg).mul (Complex.continuous_ofReal.comp
        ((continuous_LY q dd X j).comp continuous_fst))
    · exact differentiable_rhoM.continuous.comp (continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))

include hd in
theorem norm_GG {X : ℝ} (hX : 0 < X) (j : S → ℤ) (b : realSpace K) (τ : ℝ) :
    ‖GG q dd Acst X j b τ‖ = (‖(Acst : ℂ)‖ * ‖(Om q j : ℂ) * Ncp q j (1 - 2)‖ * (dd / X ^ 2)) *
      (‖PhiHat PhiT b‖ * Real.exp (2 * ∑ w, b w)) * ‖rhoM (1 + τ * I)‖ := by
  have hY := exp_LY q dd hd hX j b
  unfold GG
  simp only [norm_mul, Complex.norm_exp]
  have h1 : (-(Real.log X : ℂ) + ∑ w, (b w : ℂ)).re = -Real.log X + ∑ w, b w := by simp
  have h2 : (-(1 + τ * I) * (LY q dd X j b : ℂ)).re = -LY q dd X j b := by simp
  rw [h1, h2, show (1 : ℂ) - 2 = -1 by norm_num, Ncp_neg_one]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.2 (NN_pos q j)), Real.exp_neg (LY q dd X j b), hY,
    Real.exp_add, Real.exp_neg (Real.log X), Real.exp_log hX]
  have hN := NN_pos q j
  have hE := Real.exp_pos (∑ w, b w)
  rw [show Real.exp (2 * ∑ w, b w) = Real.exp (∑ w, b w) * Real.exp (∑ w, b w) by
    rw [← Real.exp_add]; ring_nf, Real.exp_neg]
  field_simp

theorem integrable_beta : Integrable fun b : realSpace K =>
    ‖PhiHat PhiT b‖ * Real.exp (2 * ∑ w, b w) := by
  have := integrable_prof_exp (phiHatS K) (σ := 2) (by norm_num)
  rw [coe_phiHatS] at this
  exact this

theorem integrable_gamma : Integrable fun τ : ℝ => ‖rhoM (1 + τ * I)‖ := by
  have := (verticalIntegrable_rhoM 1).norm
  simpa using this

include hd in
theorem integrable_GG {X : ℝ} (hX : 0 < X) (j : S → ℤ) :
    Integrable (fun p : realSpace K × ℝ => GG q dd Acst X j p.1 p.2)
      ((volume : Measure (realSpace K)).prod volume) := by
  refine ((integrable_beta.mul_prod integrable_gamma).const_mul
    (‖(Acst : ℂ)‖ * ‖(Om q j : ℂ) * Ncp q j (1 - 2)‖ * (dd / X ^ 2))).mono'
    (continuous_GG q dd Acst X j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_GG q dd Acst hd hX]
  ring_nf; rfl

include hd in
theorem integral_GG_tau {X : ℝ} (hX : 0 < X) (j : S → ℤ) (b : realSpace K) :
    ∫ τ : ℝ, GG q dd Acst X j b τ = 2 * π * ((Acst : ℂ) * (Om q j : ℂ) * PhiHat PhiT b *
      cexp (-(Real.log X : ℂ) + ∑ w, (b w : ℂ))) *
        (rho (X * NN q j * Real.exp (-∑ w, b w) / dd) : ℂ) := by
  set Y := X * NN q j * Real.exp (-∑ w, b w) / dd
  have hYpos : 0 < Y := by have := NN_pos q j; positivity
  have hLY : Real.log Y = LY q dd X j b := by
    rw [show Y = Real.exp (LY q dd X j b) from (exp_LY q dd hd hX j b).symm, Real.log_exp]
  have hinv := mellinInv_rhoM 1 hYpos
  rw [mellinInv] at hinv
  have hint : ∫ τ : ℝ, cexp (-(1 + τ * I) * LY q dd X j b) * rhoM (1 + τ * I) =
      2 * π * (rho Y : ℂ) := by
    rw [← hinv]
    rw [Complex.real_smul, ← mul_assoc]
    have h2pi : (2 * π : ℂ) * (1 / (2 * π) : ℝ) = 1 := by
      push_cast; field_simp
    rw [h2pi, one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [smul_eq_mul]
    rw [cpow_ofReal_pos hYpos, hLY]
    push_cast; ring_nf
  unfold GG
  rw [integral_const_mul, hint]
  ring

include hq hd in
theorem mellinInv_Mw {X : ℝ} (hX : 0 < X) :
    mellinInv 2 (Mw (K := K) q dd Acst) X = Dw (K := K) q dd Acst X := by
  rw [mellinInv]
  simp_rw [cpow_smul_Mw q hq dd Acst hX]
  -- swap the sum over `j` with the line integral
  set F : (S → ℤ) → ℝ → ℂ := fun j τ => ∫ b : realSpace K, GG q dd Acst X j b τ
  have hFint : ∀ j, Integrable (F j) := fun j => (integrable_GG q dd Acst hd hX j).integral_prod_right
  have hFnorm : ∀ j τ, ‖F j τ‖ ≤ (‖(Acst : ℂ)‖ * ‖(Om q j : ℂ) * Ncp q j (1 - 2)‖ * (dd / X ^ 2)) *
      (∫ b : realSpace K, ‖PhiHat PhiT b‖ * Real.exp (2 * ∑ w, b w)) * ‖rhoM (1 + τ * I)‖ := by
    intro j τ
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [norm_GG q dd Acst hd hX]
    rw [integral_mul_const, integral_const_mul]
  have hsum : Summable fun j => ∫ τ, ‖F j τ‖ := by
    have hS := (hasSum_Om q hq 2 (by norm_num)).2
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun τ => norm_nonneg _)
      (fun j => ?_) ((hS.mul_left (‖(Acst : ℂ)‖)).mul_right
        ((dd / X ^ 2) * (∫ b : realSpace K, ‖PhiHat PhiT b‖ * Real.exp (2 * ∑ w, b w)) *
          ∫ τ : ℝ, ‖rhoM (1 + τ * I)‖))
    refine (integral_mono (hFint j).norm (integrable_gamma.const_mul _) (hFnorm j)).trans
      (le_of_eq ?_)
    rw [integral_const_mul]; ring
  rw [← integral_tsum_of_summable_integral_norm hFint hsum]
  have hswap : ∀ j, ∫ τ, F j τ = ∫ b : realSpace K, ∫ τ : ℝ, GG q dd Acst X j b τ := fun j =>
    (integral_integral_swap (integrable_GG q dd Acst hd hX j)).symm
  simp_rw [hswap, integral_GG_tau q dd Acst hd hX]
  rw [Dw, Complex.real_smul, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hE : cexp (-(Real.log X : ℂ) + ∑ w, (b w : ℂ)) = ((X⁻¹ : ℝ) : ℂ) * (Real.exp (∑ w, b w) : ℂ) := by
    rw [Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hX, Complex.ofReal_exp,
      Complex.ofReal_sum, Complex.ofReal_inv]
  simp only [hE]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  push_cast
  field_simp

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_StarR: the dual side of the class-form identity

`QR h (x, k) = ρ(T e^{Σx} N(k)) Σ_{e ⊆ S} (−1)^{|e|} (covol(𝔫P^{k+e}) e^{Σx})⁻¹
  1[h ≠ 0, h ∈ P^{val ν − k − e − δ}] ĉ⁻(h) Φ̂(ℓ(h) − ℓ(ν) − x)` is `U_S`-equivariant (for the inverse
action), and `Σ_k ∫ QR (gen 𝔥) = (T/q_𝔫) ĉ⁻(gen 𝔥) D(T N𝔥 / q_𝔫)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical nonZeroDivisors

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-! ### The dual coefficient `ĉ⁻` -/

theorem sAddChar_shift {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) {a b : SInt 𝔪}
    (hab : a - b ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (h : SInt 𝔪) :
    sAddChar 𝔪 (-(a : F) * ((h : F) / (ν : F))) = sAddChar 𝔪 (-(b : F) * ((h : F) / (ν : F))) := by
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hν ▸ hab)
  have hsF : (s : F) * (ν : F) = (a : F) - (b : F) := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hs
    simpa using this
  have hsplit : -(a : F) * ((h : F) / (ν : F)) = -(b : F) * ((h : F) / (ν : F)) + -((s : F) * (h : F)) := by
    have : (a : F) = (b : F) + (s : F) * (ν : F) := by rw [hsF]; ring
    rw [this]; field_simp; ring
  have hw1 : C3I.HasWit 𝔪 (-(b : F) * ((h : F) / (ν : F))) := by
    have := hasWit_div h𝔫 hν (-b * h)
    convert this using 1; push_cast; ring
  have hr : -((s : F) * (h : F)) ∈ (placesOf 𝔪).integer F := neg_mem (s * h).2
  rw [hsplit, C3I.sAddChar_add hw1 (C3I.hasWit_of_mem hr), sAddChar_of_mem hr, mul_one]

theorem quotLift_sub_mem {𝔫 : Ideal (𝓞 F)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk (𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) x) - x ∈
      𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← Ideal.Quotient.eq]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

theorem periodic_eq {𝔫 : Ideal (𝓞 F)} (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x) {a b : SInt 𝔪}
    (hab : a - b ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) : c a = c b := by
  have := hc b (a - b) hab
  rwa [add_sub_cancel] at this

theorem chm_unit_mul {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (hcU : ∀ (ε : (SInt 𝔪)ˣ) (x : SInt 𝔪), c ((ε : SInt 𝔪) * x) = c x)
    (ε : (SInt 𝔪)ˣ) (h : SInt 𝔪) :
    chm (𝔫 := 𝔫) c ν (((ε : SInt 𝔪) * h : SInt 𝔪) : F) = chm (𝔫 := 𝔫) c ν (h : F) := by
  set I := 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))
  set u : (Qn 𝔪 𝔫)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom ε
  rw [chm, chm]
  refine Fintype.sum_equiv (Units.mulLeft u) (M := ℂ)
    (fun xc => c (quotLift xc) * sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) *
      ((((ε : SInt 𝔪) * h : SInt 𝔪) : F) / (ν : F))))
    (fun xc => c (quotLift xc) * sAddChar 𝔪 (-((quotLift xc : SInt 𝔪) : F) * ((h : F) / (ν : F))))
    fun xc => ?_
  simp only [Units.mulLeft_apply]
  have hmem : quotLift ((u : Qn 𝔪 𝔫) * xc) - (ε : SInt 𝔪) * quotLift xc ∈ I := by
    have h1 : ((u : Qn 𝔪 𝔫) * xc) = Ideal.Quotient.mk I ((ε : SInt 𝔪) * quotLift xc) := by
      rw [map_mul]
      congr 1
      exact (Function.surjInv_eq Ideal.Quotient.mk_surjective xc).symm
    rw [h1]
    exact quotLift_sub_mem _
  rw [periodic_eq c hc hmem, hcU, sAddChar_shift h𝔫 hν hmem h]
  congr 2
  push_cast
  ring

theorem norm_chm_le {𝔫 : Ideal (𝓞 F)} [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (ν : SInt 𝔪) (h : F) :
    ‖chm (𝔫 := 𝔫) c ν h‖ ≤ ∑ xc : Qn 𝔪 𝔫, ‖c (quotLift xc)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun xc _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (L2B.norm_sAddChar_le _ _)

/-! ### The covolume of `𝔫 P^j` -/

/-- `C_K = 2^{−r₂} √|d|`, the covolume of `𝓞`. -/
noncomputable def CK (F : Type*) [Field F] [NumberField F] : ℝ :=
  (2⁻¹ : ℝ) ^ nrComplexPlaces F * Real.sqrt |(discr F : ℝ)|

theorem CK_pos : 0 < CK F := by
  unfold CK
  have : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  positivity

theorem covN_eq {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) (j : SP 𝔪 → ℤ) :
    covN h𝔫 j = (Ideal.absNorm 𝔫 : ℝ) * NN (qS (𝔪 := 𝔪)) j * CK F := by
  rw [covN, covolume_idealLattice, coe_nPk, map_mul, FractionalIdeal.coeIdeal_absNorm, CK]
  push_cast
  rw [absNorm_Pk]
  ring

/-! ### The dual integrand -/

/-- The dual integrand. -/
noncomputable def QR (T : ℝ) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) [Fintype (Qn 𝔪 𝔫)]
    (c : SInt 𝔪 → ℂ) (ν : SInt 𝔪) (h : SInt 𝔪) (x : realSpace F) (k : SP 𝔪 → ℤ) : ℂ :=
  (wt T x k : ℂ) * ∑ e : Finset (SP 𝔪), (-1 : ℂ) ^ e.card *
    (((covN h𝔫 (k + indE e) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
      (if (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
          (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
        chm (𝔫 := 𝔫) c ν (h : F) * PhiHat PhiT (logK (h : F) - logK (ν : F) - x) else 0))

theorem QR_zero (T : ℝ) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) [Fintype (Qn 𝔪 𝔫)]
    (c : SInt 𝔪 → ℂ) (ν : SInt 𝔪) (x : realSpace F) (k : SP 𝔪 → ℤ) : QR T h𝔫 c ν 0 x k = 0 := by
  simp [QR]

theorem LxU_inv (ε : (SInt 𝔪)ˣ) : LxU ε⁻¹ = -LxU ε := by
  have := LxU_mul ε⁻¹ ε
  rw [inv_mul_cancel] at this
  have h1 : LxU (1 : (SInt 𝔪)ˣ) = 0 := by simp [LxU, logK_one]
  rw [h1] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem LkU_inv (ε : (SInt 𝔪)ˣ) : LkU ε⁻¹ = -LkU ε := by
  have := LkU_mul ε⁻¹ ε
  rw [inv_mul_cancel] at this
  have h1 : LkU (1 : (SInt 𝔪)ˣ) = 0 := (LkHom 𝔪).map_zero
  rw [h1] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem QR_unit_mul (T : ℝ) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (hcU : ∀ (ε : (SInt 𝔪)ˣ) (x : SInt 𝔪), c ((ε : SInt 𝔪) * x) = c x)
    (ε : (SInt 𝔪)ˣ) (h : SInt 𝔪) (x : realSpace F) (k : SP 𝔪 → ℤ) :
    QR T h𝔫 c ν ((ε : SInt 𝔪) * h) x k =
      QR T h𝔫 c ν h (x + LxU (Equiv.inv _ ε)) (k - LkU (Equiv.inv _ ε)) := by
  simp only [Equiv.inv_apply]
  have hw := wt_shift T x k ε⁻¹
  rw [QR, QR, hw]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [LxU_inv, LkU_inv, sub_neg_eq_add]
  have hε0 := unit_ne_zero ε
  have hmul : (((ε : SInt 𝔪) * h : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * (h : F) := rfl
  -- the covolume factor
  have hK : covN h𝔫 (k + indE e) * Real.exp (∑ w, x w) =
      covN h𝔫 (k + LkU ε + indE e) * Real.exp (∑ w, (x + -LxU ε) w) := by
    rw [covN_eq, covN_eq, show k + LkU ε + indE e = (k + indE e) + LkU ε by abel, NN_add]
    simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Real.exp_add, Real.exp_neg, exp_sum_LxU]
    have := NN_pos (qS (𝔪 := 𝔪)) (LkU ε)
    field_simp
    rw [NN_add, NN_add]; ring
  rw [hK]
  congr 2
  by_cases hh0 : (h : F) = 0
  · rw [if_neg (fun hh => hh.1 (by rw [hmul, hh0, mul_zero])), if_neg (fun hh => hh.1 hh0)]
  have hc1 : ((((ε : SInt 𝔪) * h : SInt 𝔪) : F) ≠ 0 ∧ (((ε : SInt 𝔪) * h : SInt 𝔪) : F) ∈
      ((Pk (valS (ν : F) - (k + indE e) - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F)) ↔ ((h : F) ≠ 0 ∧ (h : F) ∈
      ((Pk (valS (ν : F) - (k + LkU ε + indE e) - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [hmul, mem_Pk_iff (mul_ne_zero hε0 hh0), mem_Pk_iff hh0, valS_mul hε0 hh0]
    have hR1 : ((ε : SInt 𝔪) : F) * (h : F) ∈ (placesOf 𝔪).integer F := ((ε : SInt 𝔪) * h).2
    simp only [ne_eq, mul_eq_zero, hε0, hh0, or_self, not_false_eq_true, true_and, hR1, h.2]
    constructor
    · intro hle v; have := hle v; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      simp only [LkU] at *; omega
    · intro hle v; have := hle v; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      simp only [LkU] at *; omega
  by_cases hcond : (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk (valS (ν : F) - (k + LkU ε + indE e) - delta) :
      (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
  · rw [if_pos (hc1.2 hcond), if_pos hcond, chm_unit_mul h𝔫 hν c hc hcU ε h, hmul,
      logK_mul hε0 hh0]
    congr 2
    rw [LxU]; abel
  · rw [if_neg (fun h' => hcond (hc1.1 h')), if_neg hcond]

/-! ### The dual computation -/

theorem tsum_integral_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace F → (SP 𝔪 → ℤ) → E) (c₀ : realSpace F) (s : SP 𝔪 → ℤ) :
    ∑' k, ∫ x, f x k = ∑' j, ∫ b, f (c₀ - b) (j - s) := by
  rw [← (Equiv.subRight s).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.subRight_apply]
  exact (integral_sub_left_eq_self (fun x => f x (j - s)) volume c₀).symm

variable {ι : F →+* ℂ}

/-- The dual integrand after the substitution `x = ℓ(h) − ℓ(ν) − b`, `k = j − s`. -/
theorem QR_subst (T : ℝ) (hT : 0 < T) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) [Fintype (Qn 𝔪 𝔫)]
    (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔥 : Ext 𝔪) (b : realSpace F) (j : SP 𝔪 → ℤ) :
    QR T h𝔫 c ν (g.gen 𝔥.1) (logK ((g.gen 𝔥.1 : SInt 𝔪) : F) - logK (ν : F) - b)
        (j - (valS ((g.gen 𝔥.1 : SInt 𝔪) : F) - valS (ν : F) + delta)) =
      (((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) * chm (𝔫 := 𝔫) c ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
        (((|(discr F : ℝ)| / CK F) / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) : ℝ) : ℂ)) *
      ((Om (qS (𝔪 := 𝔪)) j : ℂ) * (PhiHat PhiT b * (Real.exp (∑ w, b w) : ℂ) *
        (rho ((T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) * NN qS j * Real.exp (-∑ w, b w) /
          |(discr F : ℝ)|) : ℂ))) := by
  set h := g.gen 𝔥.1
  have hh0 := gen_ne_zero g 𝔥
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  set s := valS (𝔪 := 𝔪) (h : F) - valS (ν : F) + delta
  set c₀ := logK (h : F) - logK (ν : F)
  -- norms
  have hNh : ((|Algebra.norm ℚ (h : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔥.1 : ℝ) *
      NN (qS (𝔪 := 𝔪)) (valS (h : F)) := abs_norm_eq 𝔥.2 (g.span_gen 𝔥.1 𝔥.2)
  have hNν : ((|Algebra.norm ℚ (ν : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔫 : ℝ) *
      NN (qS (𝔪 := 𝔪)) (valS (ν : F)) := abs_norm_eq h𝔫 hν
  have hd : NN (qS (𝔪 := 𝔪)) delta = |(discr F : ℝ)| := NN_delta hD
  have h𝔥0 : (0 : ℝ) < Ideal.absNorm 𝔥.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔥.2.1)
  have h𝔫0 : (0 : ℝ) < Ideal.absNorm 𝔫 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫.1)
  have hdpos : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  have hexp : Real.exp (∑ w, c₀ w) = ((Ideal.absNorm 𝔥.1 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (h : F))) /
      ((Ideal.absNorm 𝔫 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (ν : F))) := by
    simp only [c₀, Pi.sub_apply, Finset.sum_sub_distrib, Real.exp_sub]
    rw [sum_logK hh0, sum_logK hν0, Real.exp_log (by rw [hNh]; exact mul_pos h𝔥0 (NN_pos _ _)),
      Real.exp_log (by rw [hNν]; exact mul_pos h𝔫0 (NN_pos _ _)), hNh, hNν]
  have hNs : NN (qS (𝔪 := 𝔪)) s = NN (qS (𝔪 := 𝔪)) (valS (h : F)) / NN (qS (𝔪 := 𝔪)) (valS (ν : F)) * |(discr F : ℝ)| := by
    simp only [s]; rw [NN_add, NN_sub, hd]
  have hsumb : ∑ w, (c₀ - b) w = ∑ w, c₀ w - ∑ w, b w := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  have hA := NN_pos (qS (𝔪 := 𝔪)) (valS (h : F))
  have hB := NN_pos (qS (𝔪 := 𝔪)) (valS (ν : F))
  have hwt : wt T (c₀ - b) (j - s) = rho ((T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) *
      NN (qS (𝔪 := 𝔪)) j * Real.exp (-∑ w, b w) / |(discr F : ℝ)|) := by
    unfold wt
    congr 1
    rw [hsumb, Real.exp_sub, hexp, NN_sub, hNs, Real.exp_neg]
    field_simp
  have hcov : ∀ e : Finset (SP 𝔪),
      ((covN h𝔫 (j - s + indE e) * Real.exp (∑ w, (c₀ - b) w) : ℝ) : ℂ)⁻¹ =
        (((|(discr F : ℝ)| / CK F) / (Ideal.absNorm 𝔥.1 : ℝ) * (NN (qS (𝔪 := 𝔪)) (j + indE e))⁻¹ *
          Real.exp (∑ w, b w) : ℝ) : ℂ) := by
    intro e
    rw [← Complex.ofReal_inv]
    congr 1
    have hC := CK_pos (F := F)
    have hE := NN_pos (qS (𝔪 := 𝔪)) (j + indE e)
    rw [covN_eq, hsumb, Real.exp_sub, hexp, show j - s + indE e = (j + indE e) - s by abel,
      NN_sub, hNs]
    field_simp
  have hcond : ∀ e : Finset (SP 𝔪), ((h : F) ≠ 0 ∧ (h : F) ∈
      ((Pk (valS (ν : F) - (j - s + indE e) - delta) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F)) ↔ 0 ≤ j + indE e := by
    intro e
    rw [mem_Pk_iff hh0, show valS (ν : F) - (j - s + indE e) - delta =
      valS (h : F) - (j + indE e) by simp only [s]; abel]
    constructor
    · rintro ⟨-, -, hle⟩
      intro v
      have := hle v
      simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢
      linarith
    · intro hle
      refine ⟨hh0, h.2, fun v => ?_⟩
      have := hle v
      simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢
      linarith
  have hb : logK (h : F) - logK (ν : F) - (c₀ - b) = b := by simp only [c₀]; abel
  unfold QR
  simp_rw [hcond, hcov, hb]
  rw [hwt, Om]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have h𝔫c : ((Ideal.absNorm 𝔫 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h𝔫0.ne'
  have h𝔥c : ((Ideal.absNorm 𝔥.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h𝔥0.ne'
  have hCc : ((CK F : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (CK_pos (F := F)).ne'
  have hdc : ((|(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hEc : ((NN (qS (𝔪 := 𝔪)) (j + indE e) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (NN_pos _ _).ne'
  split_ifs
  · push_cast at hTc h𝔫c h𝔥c
    field_simp
    push_cast
    field_simp
  · simp

/-- The dual side, one generator at a time: `Σ_k ∫ Q^R(gen 𝔥) = (T/N𝔫) ĉ(gen 𝔥) D(T N𝔥 / N𝔫)`. -/
theorem tsum_QR_gen (T : ℝ) (hT : 0 < T) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) [Fintype (Qn 𝔪 𝔫)]
    (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔥 : Ext 𝔪) :
    ∑' k, ∫ x, QR T h𝔫 c ν (g.gen 𝔥.1) x k =
      ((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) * chm (𝔫 := 𝔫) c ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
        Dw (K := F) (qS (𝔪 := 𝔪)) |(discr F : ℝ)| (|(discr F : ℝ)| / CK F)
          (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) := by
  rw [tsum_integral_subst _ (logK ((g.gen 𝔥.1 : SInt 𝔪) : F) - logK (ν : F))
    (valS ((g.gen 𝔥.1 : SInt 𝔪) : F) - valS (ν : F) + delta)]
  simp_rw [QR_subst T hT hD h𝔫 hν c g 𝔥, integral_const_mul]
  rw [tsum_mul_left, Dw]
  push_cast
  ring

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_StarR2: integrability and summability of the dual integrand

`ρ(Y) ≤ (9/4) Y⁻²` makes `x ↦ QR h (x, k)` integrable, and after the substitution of
`QR_subst` the `L¹` norms are `≪ N(𝔥)⁻³ |Om j| N(j)⁻²`, summable over `j` and `𝔥`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical nonZeroDivisors

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

theorem rho_le_sq {Y : ℝ} (hY : 0 < Y) : rho Y ≤ 9 / 4 / Y ^ 2 := by
  by_cases h : 3 / 2 < Y
  · rw [rho_eq_zero (Or.inr h)]; positivity
  · push Not at h
    calc rho Y ≤ 1 := rho_le_one Y
      _ ≤ 9 / 4 / Y ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith

theorem integrable_beta3 : Integrable fun b : realSpace F =>
    ‖PhiHat PhiT b‖ * Real.exp (3 * ∑ w, b w) := by
  have := integrable_prof_exp (phiHatS F) (σ := 3) (by norm_num)
  rw [coe_phiHatS] at this
  exact this

theorem wt_le {T : ℝ} (hT : 0 < T) (x : realSpace F) (k : SP 𝔪 → ℤ) :
    wt T x k ≤ 9 / 4 / (T * NN (qS (𝔪 := 𝔪)) k) ^ 2 * Real.exp (-2 * ∑ w, x w) := by
  have hN := NN_pos (qS (𝔪 := 𝔪)) k
  have hE := Real.exp_pos (∑ w, x w)
  refine (rho_le_sq (by positivity)).trans (le_of_eq ?_)
  rw [neg_mul, Real.exp_neg, show (2 : ℝ) * ∑ w, x w = ∑ w, x w + ∑ w, x w by ring, Real.exp_add]
  field_simp

variable {ι : F →+* ℂ}

theorem integrable_QR {T : ℝ} (hT : 0 < T) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (ν m : SInt 𝔪) (k : SP 𝔪 → ℤ) :
    Integrable fun x => QR T h𝔫 c ν m x k := by
  unfold QR
  simp_rw [Finset.mul_sum]
  refine integrable_finsetSum _ fun e _ => ?_
  by_cases hc : (m : F) ≠ 0 ∧ (m : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
      (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
  swap
  · simp_rw [if_neg hc, mul_zero]; exact integrable_zero _ _ _
  simp_rw [if_pos hc]
  set a := logK (m : F) - logK (ν : F)
  set C0 := covN h𝔫 (k + indE e)
  have hC0 : 0 < C0 := by
    simp only [C0]; rw [covN_eq]
    have := CK_pos (F := F)
    have := NN_pos (qS (𝔪 := 𝔪)) (k + indE e)
    have : (0 : ℝ) < Ideal.absNorm 𝔫 := by
      exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫.1)
    positivity
  have hinv : ∀ x : realSpace F, ((C0 * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ =
      ((C0⁻¹ * Real.exp (-∑ w, x w) : ℝ) : ℂ) := fun x => by
    rw [Real.exp_neg, ← mul_inv, Complex.ofReal_inv]
  simp_rw [hinv]
  set ch := chm (𝔫 := 𝔫) c ν (m : F)
  set K0 := C0⁻¹ * ‖ch‖ * (9 / 4 / (T * NN (qS (𝔪 := 𝔪)) k) ^ 2) * Real.exp (-3 * ∑ w, a w)
  have hw : Continuous fun x : realSpace F => wt T x k := continuous_wt T k
  have hP : Continuous fun x : realSpace F => PhiHat PhiT (a - x) :=
    continuous_PhiHat.comp (continuous_const.sub continuous_id)
  have hs : Continuous fun x : realSpace F => ∑ w, x w :=
    continuous_finsetSum _ fun w _ => continuous_apply w
  refine ((integrable_beta3 (F := F)).comp_sub_left a |>.const_mul K0).mono' ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact (Complex.continuous_ofReal.comp hw).mul (continuous_const.mul
      ((Complex.continuous_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp
        hs.neg))).mul (continuous_const.mul hP)))
  · simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (rho_nonneg _)]
    have hwx := wt_le (𝔪 := 𝔪) hT x k
    have hC0i : 0 ≤ C0⁻¹ := inv_nonneg.2 hC0.le
    rw [abs_of_nonneg hC0i, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-3 * ∑ w, a w) * Real.exp (3 * ∑ w, (a - x) w) =
        Real.exp (-2 * ∑ w, x w) * Real.exp (-∑ w, x w) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      ring
    calc |wt T x k| * (C0⁻¹ * Real.exp (-∑ w, x w) * (‖ch‖ * ‖PhiHat PhiT (a - x)‖))
        = wt T x k * (C0⁻¹ * Real.exp (-∑ w, x w) * (‖ch‖ * ‖PhiHat PhiT (a - x)‖)) := by
          rw [abs_of_nonneg (show 0 ≤ wt T x k from rho_nonneg _)]
      _ ≤ (9 / 4 / (T * NN (qS (𝔪 := 𝔪)) k) ^ 2 * Real.exp (-2 * ∑ w, x w)) *
          (C0⁻¹ * Real.exp (-∑ w, x w) * (‖ch‖ * ‖PhiHat PhiT (a - x)‖)) := by
          gcongr
      _ = K0 * (‖PhiHat PhiT (a - x)‖ * Real.exp (3 * ∑ w, (a - x) w)) := by
          simp only [K0]
          linear_combination (-(C0⁻¹ * ‖ch‖ * (9 / 4 / (T * NN (qS (𝔪 := 𝔪)) k) ^ 2)) *
            ‖PhiHat PhiT (a - x)‖) * hexp

/-! ### `L¹` bounds after the substitution -/

theorem norm_Ncp_three {S : Type*} [Fintype S] (q : S → ℝ) (j : S → ℤ) :
    ‖Ncp q j (1 - 3)‖ = (NN q j ^ 2)⁻¹ := by
  rw [Ncp, show ((1 : ℂ) - 3) * ((∑ v, ((j v : ℝ) * lq q v) : ℝ) : ℂ) =
      ((-(2 * ∑ v, ((j v : ℝ) * lq q v)) : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal,
    Real.exp_neg, NN, show (2 : ℝ) * ∑ v, ((j v : ℝ) * lq q v) =
      ((2 : ℕ) : ℝ) * ∑ v, ((j v : ℝ) * lq q v) by norm_num, Real.exp_nat_mul]

/-- The `j`-weights `|Om j| N(j)⁻²`. -/
noncomputable def uJ (j : SP 𝔪 → ℤ) : ℝ := ‖(Om (qS (𝔪 := 𝔪)) j : ℂ) * Ncp (qS (𝔪 := 𝔪)) j (1 - 3)‖

theorem summable_uJ : Summable (uJ (𝔪 := 𝔪)) :=
  (hasSum_Om (qS (𝔪 := 𝔪)) one_lt_qS 3 (by norm_num)).2

theorem uJ_eq (j : SP 𝔪 → ℤ) : uJ j = |Om (qS (𝔪 := 𝔪)) j| * (NN (qS (𝔪 := 𝔪)) j ^ 2)⁻¹ := by
  rw [uJ, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_Ncp_three]

theorem uJ_nonneg (j : SP 𝔪 → ℤ) : 0 ≤ uJ j := norm_nonneg _

/-- `∫ ‖Φ̂(b)‖ e^{3Σb} db`. -/
noncomputable def I3 (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F] : ℝ :=
  ∫ b : realSpace F, ‖PhiHat PhiT b‖ * Real.exp (3 * ∑ w, b w)

theorem I3_nonneg : 0 ≤ I3 F := integral_nonneg fun _ => by positivity

theorem pt_bound (A : ℂ) {X dd : ℝ} (hX : 0 < X) (hdpos : 0 < dd) (j : SP 𝔪 → ℤ)
    (b : realSpace F) :
    ‖A * ((Om (qS (𝔪 := 𝔪)) j : ℂ) * (PhiHat PhiT b * (Real.exp (∑ w, b w) : ℂ) *
      (rho (X * NN (qS (𝔪 := 𝔪)) j * Real.exp (-∑ w, b w) / dd) : ℂ)))‖ ≤
      (‖A‖ * (9 / 4 * dd ^ 2 / X ^ 2) * uJ j) * (‖PhiHat PhiT b‖ * Real.exp (3 * ∑ w, b w)) := by
  set E := Real.exp (∑ w, b w) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hN := NN_pos (qS (𝔪 := 𝔪)) j
  rw [Real.exp_neg, ← hEdef]
  have hY : 0 < X * NN (qS (𝔪 := 𝔪)) j * E⁻¹ / dd := by positivity
  have hr := rho_le_sq hY
  have hr0 := rho_nonneg (X * NN (qS (𝔪 := 𝔪)) j * E⁻¹ / dd)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_pos hE]
  rw [uJ_eq, show Real.exp (3 * ∑ w, b w) = E ^ 3 by
    rw [hEdef, ← Real.exp_nat_mul]; norm_num]
  calc ‖A‖ * (|Om (qS (𝔪 := 𝔪)) j| * (‖PhiHat PhiT b‖ * E *
        rho (X * NN (qS (𝔪 := 𝔪)) j * E⁻¹ / dd)))
      ≤ ‖A‖ * (|Om (qS (𝔪 := 𝔪)) j| * (‖PhiHat PhiT b‖ * E *
        (9 / 4 / (X * NN (qS (𝔪 := 𝔪)) j * E⁻¹ / dd) ^ 2))) := by gcongr
    _ = _ := by field_simp

theorem integral_norm_QR_le {T : ℝ} (hT : 0 < T) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)))
    [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔥 : Ext 𝔪) (j : SP 𝔪 → ℤ) :
    ∫ x, ‖QR T h𝔫 c ν (g.gen 𝔥.1) x
        (j - (valS ((g.gen 𝔥.1 : SInt 𝔪) : F) - valS (ν : F) + delta))‖ ≤
      (‖((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) * chm (𝔫 := 𝔫) c ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
        (((|(discr F : ℝ)| / CK F) / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) : ℝ) : ℂ)‖ *
        (9 / 4 * |(discr F : ℝ)| ^ 2 / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) ^ 2) * I3 F) *
        uJ j := by
  have h𝔥0 : (0 : ℝ) < Ideal.absNorm 𝔥.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔥.2.1)
  have h𝔫0 : (0 : ℝ) < Ideal.absNorm 𝔫 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫.1)
  have hdpos : (0 : ℝ) < |(discr F : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  have hX : 0 < T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫 := by positivity
  rw [← integral_sub_left_eq_self _ volume
    (logK ((g.gen 𝔥.1 : SInt 𝔪) : F) - logK (ν : F))]
  simp only [QR_subst T hT hD h𝔫 hν c g 𝔥]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (integrable_beta3.const_mul _)
    (Filter.Eventually.of_forall fun b => pt_bound _ hX hdpos j b)).trans (le_of_eq ?_)
  rw [integral_const_mul, ← I3]; ring

theorem summable_QR_k {T : ℝ} (hT : 0 < T) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)))
    [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔥 : Ext 𝔪) :
    Summable fun k => ∫ x, ‖QR T h𝔫 c ν (g.gen 𝔥.1) x k‖ := by
  rw [← (Equiv.subRight (valS ((g.gen 𝔥.1 : SInt 𝔪) : F) - valS (ν : F) + delta)).summable_iff]
  exact Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
    (fun j => integral_norm_QR_le hT hD h𝔫 hν c g 𝔥 j) (summable_uJ.mul_left _)

theorem tsum_QR_k_le {T : ℝ} (hT : 0 < T) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)))
    [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) (𝔥 : Ext 𝔪) :
    ∑' k, ∫ x, ‖QR T h𝔫 c ν (g.gen 𝔥.1) x k‖ ≤
      (‖((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) * chm (𝔫 := 𝔫) c ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
        (((|(discr F : ℝ)| / CK F) / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) : ℝ) : ℂ)‖ *
        (9 / 4 * |(discr F : ℝ)| ^ 2 / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) ^ 2) * I3 F) *
        ∑' j, uJ (𝔪 := 𝔪) j := by
  have hs := summable_QR_k hT hD h𝔫 hν c g 𝔥
  set s := valS ((g.gen 𝔥.1 : SInt 𝔪) : F) - valS (ν : F) + delta
  rw [← (Equiv.subRight s).tsum_eq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun j => integral_norm_QR_le hT hD h𝔫 hν c g 𝔥 j)
    ((Equiv.subRight s).summable_iff.2 hs) (summable_uJ.mul_left _)

theorem summable_QR {T : ℝ} (hT : 0 < T) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)))
    [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (g : AllowedGen ι 𝔪) :
    Summable fun 𝔥 : Ext 𝔪 => ∑' k, ∫ x, ‖QR T h𝔫 c ν (g.gen 𝔥.1) x k‖ := by
  set Cc := ∑ xc : Qn 𝔪 𝔫, ‖c (quotLift xc)‖
  set dd := |(discr F : ℝ)|
  set U := ∑' j, uJ (𝔪 := 𝔪) j
  have hU : 0 ≤ U := tsum_nonneg uJ_nonneg
  have hI := I3_nonneg (F := F)
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC := CK_pos (F := F)
  have h𝔫0 : (0 : ℝ) < Ideal.absNorm 𝔫 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫.1)
  have hdpos : (0 : ℝ) < dd := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  set K := T / Ideal.absNorm 𝔫 * Cc * (dd / CK F) * (9 / 4 * dd ^ 2) * I3 F * U *
    (Ideal.absNorm 𝔫 / T) ^ 3
  have hsum : Summable fun 𝔥 : Ext 𝔪 => ((Ideal.absNorm 𝔥.1 : ℕ) : ℝ) ^ (-(3 : ℝ)) :=
    (T12B.summable_absNorm_rpow (F := F) (by norm_num : (1 : ℝ) < 3)).comp_injective
      Subtype.val_injective
  refine Summable.of_nonneg_of_le
    (fun 𝔥 => tsum_nonneg fun k => integral_nonneg fun _ => norm_nonneg _)
    (fun 𝔥 => (tsum_QR_k_le hT hD h𝔫 hν c g 𝔥).trans ?_) (hsum.mul_left K)
  have h𝔥0 : (0 : ℝ) < Ideal.absNorm 𝔥.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔥.2.1)
  have hX : 0 < T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫 := by positivity
  rw [Real.rpow_neg (Nat.cast_nonneg _), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  have hA : ‖((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) * chm (𝔫 := 𝔫) c ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
      (((dd / CK F) / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) : ℝ) : ℂ)‖ ≤
      T / Ideal.absNorm 𝔫 * Cc * ((dd / CK F) / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    gcongr
    exact norm_chm_le c ν _
  calc _ ≤ (T / Ideal.absNorm 𝔫 * Cc * ((dd / CK F) / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫))) *
        (9 / 4 * dd ^ 2 / (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) ^ 2) * I3 F * U := by
        gcongr
    _ = _ := by simp only [K]; field_simp

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Star: the class-form identity (★)

For `c` periodic modulo `𝔫R` and invariant under `R^×`:
`Σ_𝔟 c(gen 𝔟) V(N𝔟/T) = Σ_𝔥 (T/N𝔫) ĉ⁻(gen 𝔥) D(T N𝔥 / N𝔫)`, both sums over exterior ideals.
Proof: multiply the theta identity by `ρ(T e^{Σx} N(k))`, integrate against the fundamental domain
`Ω(x, k)`, and unfold both sides over `R ∖ 0 = U_S · {gen}`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical nonZeroDivisors SchwartzMap

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

theorem summable_dual {𝔫 : Ideal (𝓞 F)} [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) {ν : SInt 𝔪}
    (hν0 : (ν : F) ≠ 0) (x : realSpace F) (j : SP 𝔪 → ℤ) :
    Summable fun h : SInt 𝔪 => (if (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) then
      chm (𝔫 := 𝔫) c ν (h : F) * PhiHat PhiT (logK (h : F) - logK (ν : F) - x) else 0) := by
  set ψ : 𝓢(mixedSpace F, ℂ) := phiHatS F
  have hψ : ⇑ψ = fourierM (phiF (PhiT (K := F))) := coe_phiHatS
  have hab : (dilV (-x) * mixedEmbedding F (ν : F)⁻¹) * (dilV x * mixedEmbedding F (ν : F)) = 1 := by
    rw [mul_mul_mul_comm, mul_comm (dilV (-x)), dilV_mul_neg, ← map_mul, inv_mul_cancel₀ hν0,
      map_one, one_mul]
  set e := mulE _ _ hab
  set φ' : 𝓢(mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e ψ
  have hite : ∀ h : SInt 𝔪, (if (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) then
      chm (𝔫 := 𝔫) c ν (h : F) * PhiHat PhiT (logK (h : F) - logK (ν : F) - x) else 0) =
      (if (h : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
        chm (𝔫 := 𝔫) c ν (h : F) * φ' (0 + mixedEmbedding F (h : F)) else 0) := by
    intro h
    have hφ' : φ' (0 + mixedEmbedding F (h : F)) =
        fourierM (phiF (PhiT (K := F))) (dilV (-x) * mixedEmbedding F ((h : F) / (ν : F))) := by
      simp only [φ', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        zero_add, hψ, e, mulE_apply]
      rw [div_eq_inv_mul, map_mul, mul_assoc]
    rw [hφ']
    by_cases hh0 : (h : F) = 0
    · rw [if_neg (fun hh => hh.1 hh0)]
      split_ifs
      · rw [hh0, zero_div, map_zero, mul_zero, fourierM_phiF_PhiT_zero, mul_zero]
      · rfl
    · by_cases hJ : (h : F) ∈ ((Pk j : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
      · rw [if_pos ⟨hh0, hJ⟩, if_pos hJ, fourierM_eq_PhiHat_div hh0 hν0]
      · rw [if_neg (fun hh => hJ hh.2), if_neg hJ]
  simp_rw [hite]
  refine summable_SInt_ite_mem _ _ ?_
  have h1 := summable_schwartz_fractionalIdeal φ' (Pk j) 0
  refine Summable.of_norm_bounded (h1.mul_left (∑ xc : Qn 𝔪 𝔫, ‖c (quotLift xc)‖)) fun m => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_chm_le c ν _) (norm_nonneg _)

variable {ι : F →+* ℂ}

theorem tsum_QL_eq (T : ℝ) (c : SInt 𝔪 → ℂ) (x : realSpace F) (k : SP 𝔪 → ℤ) :
    ∑' m, QL T c m x k = (wt T x k : ℂ) * ∑' m : SInt 𝔪, (if (m : F) ≠ 0 ∧ valS (m : F) = k then
        c m * (PhiT (x + logK (m : F)) : ℂ) else 0) := by
  simp only [QL]; rw [tsum_mul_left]

theorem tsum_QR_eq (T : ℝ) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) [Fintype (Qn 𝔪 𝔫)]
    (c : SInt 𝔪 → ℂ) (x : realSpace F) (k : SP 𝔪 → ℤ) :
    ∑' h, QR T h𝔫 c ν h x k = (wt T x k : ℂ) * ∑ e : Finset (SP 𝔪), (-1 : ℂ) ^ e.card *
        (((covN h𝔫 (k + indE e) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
          ∑' h : SInt 𝔪, (if (h : F) ≠ 0 ∧ (h : F) ∈ ((Pk (valS (ν : F) - (k + indE e) - delta) :
              (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then
            chm (𝔫 := 𝔫) c ν (h : F) * PhiHat PhiT (logK (h : F) - logK (ν : F) - x) else 0)) := by
  have hν0 := ne_zero_of_span_eq h𝔫 hν
  simp only [QR]
  rw [tsum_mul_left, Summable.tsum_finsetSum fun e _ =>
    ((summable_dual c hν0 x _).mul_left _).mul_left _]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  rw [tsum_mul_left, tsum_mul_left]

/-- **The class-form identity (★).** -/
theorem star (h𝔪 : 𝔪 ≠ ⊥) (hD : DiffInS 𝔪) {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫)
    {ν : SInt 𝔪} (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (hcU : ∀ (ε : (SInt 𝔪)ˣ) (x : SInt 𝔪), c ((ε : SInt 𝔪) * x) = c x)
    [Fintype (Qn 𝔪 𝔫)] (g : AllowedGen ι 𝔪) {T : ℝ} (hT : 0 < T) :
    ∑' 𝔟 : Ext 𝔪, c (g.gen 𝔟.1) * (Vt (F := F) (Ideal.absNorm 𝔟.1 / T) : ℂ) =
      ∑' 𝔥 : Ext 𝔪, ((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) *
        chm (𝔫 := 𝔫) c ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
        Dw (K := F) (qS (𝔪 := 𝔪)) |(discr F : ℝ)| (|(discr F : ℝ)| / CK F)
          (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) := by
  have key : ∀ x k, ∑' m, QL T c m x k = ∑' h, QR T h𝔫 c ν h x k := fun x k => by
    rw [tsum_QL_eq, tsum_QR_eq T h𝔫 hν, theta_identity h𝔪 hD h𝔫 hν c hc]
  have L := tsum_unfold_R g (Equiv.refl _) (QL T c) (QL_zero T c)
    (fun ε m x k => QL_unit_mul T c hcU ε m x k) (integrable_QL T c)
    (fun 𝔟 => summable_QL_k T c _) (summable_QL T hT c g)
  have R := tsum_unfold_R g (Equiv.inv _) (QR T h𝔫 c ν) (QR_zero T h𝔫 c ν)
    (fun ε m x k => QR_unit_mul T h𝔫 hν c hc hcU ε m x k) (integrable_QR hT h𝔫 c ν)
    (summable_QR_k hT hD h𝔫 hν c g) (summable_QR hT hD h𝔫 hν c g)
  simp_rw [key] at L
  rw [L] at R
  have h0 : (torsionOrder F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos F).ne'
  have := mul_left_cancel₀ h0 R
  simp_rw [tsum_QL_gen T hT c g, tsum_QR_gen T hT hD h𝔫 hν c g] at this
  exact this

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Six: `𝔥 = 𝔲 𝔯⁶` and the generators of `𝔲 𝔯⁶`

Every exterior `𝔥` is uniquely `𝔲 𝔯⁶` with `𝔲` sixth-power-free (both exterior), and
`gen 𝔲 · (gen 𝔯)⁶ = w⁶ · gen (𝔲 𝔯⁶)` for an `S`-unit `w`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField UniqueFactorizationMonoid
open scoped Classical

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem isExterior_mul' {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨?_, ?_⟩
  · rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    exact ⟨hI.1, hJ.1⟩
  · exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 hI.2).mul_left
      (Ideal.isCoprime_iff_sup_eq.2 hJ.2))

theorem isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (k : ℕ) :
    IsExterior 𝔪 (I ^ k) := by
  induction k with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul' ih hI

theorem isExterior_of_dvd {I J : Ideal (𝓞 F)} (hJ : IsExterior 𝔪 J) (hIJ : I ∣ J) :
    IsExterior 𝔪 I := by
  refine ⟨fun h => hJ.1 ?_, ?_⟩
  · rw [h] at hIJ; exact (zero_dvd_iff.1 (by rwa [Ideal.zero_eq_bot])).trans Ideal.zero_eq_bot
  · rw [eq_top_iff, ← hJ.2]
    exact sup_le_sup_right (Ideal.le_of_dvd hIJ) _

/-! ### Sixth-power decomposition -/

/-- The multiplicity of `P` in `I`. -/
noncomputable def vl (I P : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).count P

noncomputable def fM (I : Ideal (𝓞 F)) (e : ℕ → ℕ) : Multiset (Ideal (𝓞 F)) :=
  ∑ P ∈ (normalizedFactors I).toFinset, Multiset.replicate (e (vl I P)) P

theorem fM_subset (I : Ideal (𝓞 F)) (e : ℕ → ℕ) : fM I e ⊆ normalizedFactors I := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Multiset.mem_sum.mp hP
  have he : P = Q := (Multiset.mem_replicate.mp hPQ).2
  exact he ▸ Multiset.mem_toFinset.mp hQ

theorem fM_count (I P : Ideal (𝓞 F)) (e : ℕ → ℕ) (he : e 0 = 0) :
    (fM I e).count P = e (vl I P) := by
  unfold fM
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  split_ifs with hP
  · rfl
  · have hz : vl I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (Multiset.mem_toFinset.mpr h))
    rw [hz, he]

noncomputable def fP (I : Ideal (𝓞 F)) (e : ℕ → ℕ) : Ideal (𝓞 F) := (fM I e).prod

theorem fP_ne_zero (I : Ideal (𝓞 F)) (e : ℕ → ℕ) : fP I e ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fM_subset I e)

theorem vl_fP (I P : Ideal (𝓞 F)) (e : ℕ → ℕ) (he : e 0 = 0) :
    vl (fP I e) P = e (vl I P) := by
  unfold vl fP
  rw [normalizedFactors_prod_eq_self_of_subset (fM_subset I e)]
  exact fM_count I P e he

theorem fP_dvd (I : Ideal (𝓞 F)) (hI : I ≠ 0) (e : ℕ → ℕ) (he : ∀ n, e n ≤ n) : fP I e ∣ I := by
  conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_dvd_prod_of_le ?_
  rw [Multiset.le_iff_count]
  intro P
  by_cases hP : P ∈ normalizedFactors I
  · have h0 : e 0 = 0 := Nat.le_zero.1 (he 0)
    rw [fM_count I P e h0]; exact he _
  · rw [Multiset.count_eq_zero.2 (fun h => hP (fM_subset I e h))]; exact Nat.zero_le _

noncomputable def rem6 (I : Ideal (𝓞 F)) : Ideal (𝓞 F) := fP I (fun n => n % 6)

noncomputable def quo6 (I : Ideal (𝓞 F)) : Ideal (𝓞 F) := fP I (fun n => n / 6)

theorem vl_mul (I J P : Ideal (𝓞 F)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    vl (I * J) P = vl I P + vl J P := by
  simp only [vl, normalizedFactors_mul hI hJ, Multiset.count_add]

theorem vl_pow (I P : Ideal (𝓞 F)) (n : ℕ) : vl (I ^ n) P = n * vl I P := by
  simp only [vl, normalizedFactors_pow, Multiset.count_nsmul]

theorem eq_of_vl_eq {I J : Ideal (𝓞 F)} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ P, vl I P = vl J P) : I = J := by
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ]
  exact congrArg Multiset.prod (Multiset.ext.mpr h)

theorem rem6_mul_quo6 (I : Ideal (𝓞 F)) (hI : I ≠ 0) : rem6 I * quo6 I ^ 6 = I := by
  apply eq_of_vl_eq (mul_ne_zero (fP_ne_zero _ _) (pow_ne_zero _ (fP_ne_zero _ _))) hI
  intro P
  rw [vl_mul _ _ _ (fP_ne_zero _ _) (pow_ne_zero _ (fP_ne_zero _ _)), vl_pow,
    vl_fP _ _ _ (by norm_num), vl_fP _ _ _ (by norm_num)]
  omega

theorem unique6 {A B C D : Ideal (𝓞 F)} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hAf : ∀ P, vl A P < 6) (hCf : ∀ P, vl C P < 6) (h : A * B ^ 6 = C * D ^ 6) :
    A = C ∧ B = D := by
  have hv (P : Ideal (𝓞 F)) := congrArg (fun I => vl I P) h
  simp only [vl_mul _ _ _ hA (pow_ne_zero _ hB), vl_mul _ _ _ hC (pow_ne_zero _ hD), vl_pow] at hv
  have he (P : Ideal (𝓞 F)) : vl A P = vl C P ∧ vl B P = vl D P := by
    have := hv P; have := hAf P; have := hCf P; omega
  exact ⟨eq_of_vl_eq hA hC (fun P => (he P).1), eq_of_vl_eq hB hD (fun P => (he P).2)⟩

theorem vl_lt_of_free {I : Ideal (𝓞 F)} (hI : I ≠ 0) (h6 : IsSixthPowerFree I) (P : Ideal (𝓞 F)) :
    vl I P < 6 := by
  by_contra hle
  push Not at hle
  have hP : P ∈ normalizedFactors I := Multiset.count_pos.1 (by unfold vl at hle; omega)
  have hdvd : P ^ 6 ∣ I := by
    have hle' : Multiset.replicate 6 P ≤ normalizedFactors I := by
      rw [Multiset.le_iff_count]
      intro Q
      rw [Multiset.count_replicate]
      split_ifs with hQ
      · subst hQ; exact hle
      · exact Nat.zero_le _
    have := Multiset.prod_dvd_prod_of_le hle'
    rw [Multiset.prod_replicate, Ideal.prod_normalizedFactors_eq_self hI] at this
    exact this
  have hu := h6 P hdvd
  have hPp := prime_of_normalized_factor P hP
  exact hPp.not_isUnit hu

theorem free_of_vl_lt {I : Ideal (𝓞 F)} (hI : I ≠ 0) (h : ∀ P, vl I P < 6) :
    IsSixthPowerFree I := by
  intro J hJ
  by_contra hJu
  have hJ0 : J ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num), zero_dvd_iff] at hJ; exact hI hJ
  obtain ⟨P, hP⟩ := exists_mem_normalizedFactors hJ0 hJu
  have hPd : P ∣ J := dvd_of_mem_normalizedFactors hP
  have hP6 : P ^ 6 ∣ I := (pow_dvd_pow_of_dvd hPd 6).trans hJ
  have hPp := prime_of_normalized_factor P hP
  have hPn : normalize P = P := normalize_normalized_factor P hP
  have hle : normalizedFactors (P ^ 6) ≤ normalizedFactors I :=
    (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hPp.ne_zero) hI).1 hP6
  have := Multiset.le_iff_count.1 hle P
  rw [normalizedFactors_pow, normalizedFactors_irreducible hPp.irreducible, hPn,
    Multiset.count_nsmul, Multiset.count_singleton_self] at this
  have := h P
  unfold vl at this
  omega

theorem rem6_free (I : Ideal (𝓞 F)) : IsSixthPowerFree (rem6 I) := by
  refine free_of_vl_lt (fP_ne_zero _ _) fun P => ?_
  rw [rem6, vl_fP _ _ _ (by norm_num)]
  omega

/-- `(𝔲, 𝔯) ↦ 𝔲 𝔯⁶`, a bijection onto the exterior ideals. -/
noncomputable def sixEquiv (𝔪 : Ideal (𝓞 F)) :
    {𝔲 : Ideal (𝓞 F) // IsExterior 𝔪 𝔲 ∧ IsSixthPowerFree 𝔲} ×
      {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯} ≃ {𝔥 : Ideal (𝓞 F) // IsExterior 𝔪 𝔥} where
  toFun p := ⟨p.1.1 * p.2.1 ^ 6, isExterior_mul' p.1.2.1 (isExterior_pow p.2.2 6)⟩
  invFun h :=
    have h0 : h.1 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact h.2.1
    (⟨rem6 h.1, isExterior_of_dvd h.2 (fP_dvd _ h0 _ fun n => Nat.mod_le n 6), rem6_free _⟩,
      ⟨quo6 h.1, isExterior_of_dvd h.2 ((fP_dvd _ h0 _ fun n => Nat.div_le_self n 6))⟩)
  left_inv p := by
    obtain ⟨⟨𝔲, h𝔲e, h𝔲f⟩, ⟨𝔯, h𝔯e⟩⟩ := p
    have h𝔲0 : 𝔲 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact h𝔲e.1
    have h𝔯0 : 𝔯 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact h𝔯e.1
    have hI0 : 𝔲 * 𝔯 ^ 6 ≠ 0 := mul_ne_zero h𝔲0 (pow_ne_zero _ h𝔯0)
    have := unique6 (fP_ne_zero _ _) (fP_ne_zero _ _) h𝔲0 h𝔯0
      (fun P => by rw [vl_fP _ _ _ (by norm_num)]; omega) (vl_lt_of_free h𝔲0 h𝔲f)
      (rem6_mul_quo6 _ hI0)
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact this
  right_inv h := by
    have h0 : h.1 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact h.2.1
    exact Subtype.ext (rem6_mul_quo6 _ h0)

/-! ### Generators of products -/

variable {ι : F →+* ℂ}

/-- The `S`-unit group, as units of `R`. -/
noncomputable abbrev eU (𝔪 : Ideal (𝓞 F)) : SUnit 𝔪 ≃* (SInt 𝔪)ˣ :=
  Set.unitEquivUnitsInteger (placesOf 𝔪) F

theorem coe_eU (u : SUnit 𝔪) : (((eU 𝔪 u : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((u : Fˣ) : F) := rfl

theorem coe_unit_inv (w : (SInt 𝔪)ˣ) :
    (((w⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((w : SInt 𝔪) : F))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    rw [← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl)

theorem coe_unit_ne_zero (w : (SInt 𝔪)ˣ) : (((w : SInt 𝔪) : F)) ≠ 0 := fun h => by
  have : (((w : SInt 𝔪) : F)) * (((w⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem gen_mul_unit (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) : ∃ w : (SInt 𝔪)ˣ,
      ((g.gen (I * J) : SInt 𝔪) : F) = ((w : SInt 𝔪) : F) ^ 6 * (g.gen I : F) * (g.gen J : F) := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  exact ⟨eU 𝔪 ε, by rw [coe_eU, hε]⟩

theorem gen_pow_unit (g : AllowedGen ι 𝔪) {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (k : ℕ) :
    ∃ w : (SInt 𝔪)ˣ, ((g.gen (I ^ (k + 1)) : SInt 𝔪) : F) =
      ((w : SInt 𝔪) : F) ^ 6 * (g.gen I : F) ^ (k + 1) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := gen_mul_unit g (isExterior_pow hI (k + 1)) hI
    refine ⟨w' * w, ?_⟩
    rw [pow_succ I (k + 1), hw', hw]
    push_cast
    ring

theorem gen_six_unit (g : AllowedGen ι 𝔪) {𝔲 𝔯 : Ideal (𝓞 F)} (h𝔲 : IsExterior 𝔪 𝔲)
    (h𝔯 : IsExterior 𝔪 𝔯) : ∃ w : (SInt 𝔪)ˣ,
      (((g.gen 𝔲 * g.gen 𝔯 ^ 6 : SInt 𝔪)) : F) =
        ((w : SInt 𝔪) : F) ^ 6 * (g.gen (𝔲 * 𝔯 ^ 6) : F) := by
  obtain ⟨w₁, h₁⟩ := gen_mul_unit g h𝔲 (isExterior_pow h𝔯 6)
  obtain ⟨w₂, h₂⟩ := gen_pow_unit g h𝔯 5
  refine ⟨(w₁ * w₂)⁻¹, ?_⟩
  rw [h₁, show 𝔯 ^ 6 = 𝔯 ^ (5 + 1) from rfl, h₂, coe_unit_inv, Units.val_mul, Subalgebra.coe_mul]
  have := coe_unit_ne_zero w₁
  have := coe_unit_ne_zero w₂
  field_simp
  push_cast
  ring

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Avg: averaging over `U_S / U_S⁶`

`c♯(x) = Σ_{ε ∈ U_S/U_S⁶} c(rep ε · x)` is `R^×`-invariant and `𝔫R`-periodic when `c` is
`U_S⁶`-invariant and periodic, and `ĉ♯⁻(h) = Σ_ε ĉ⁻(−rep ε · h)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-! ### Classes of units -/

/-- The class of a unit of `R` in `U_S / U_S⁶`. -/
noncomputable def cls (u : (SInt 𝔪)ˣ) : SClass 𝔪 := QuotientGroup.mk ((eU 𝔪).symm u)

/-- The chosen representative, as a unit. -/
noncomputable def repU (ε : SClass 𝔪) : (SInt 𝔪)ˣ :=
  eU 𝔪 (Function.surjInv QuotientGroup.mk_surjective ε)

theorem coe_repU (ε : SClass 𝔪) : ((repU ε : (SInt 𝔪)ˣ) : SInt 𝔪) = ε.rep := rfl

theorem cls_repU (ε : SClass 𝔪) : cls (repU ε) = ε := by
  simp only [cls, repU, MulEquiv.symm_apply_apply]
  exact Function.surjInv_eq QuotientGroup.mk_surjective ε

theorem cls_mul (u v : (SInt 𝔪)ˣ) : cls (u * v) = cls u * cls v := by
  simp only [cls, map_mul, QuotientGroup.mk_mul]

theorem cls_inv (u : (SInt 𝔪)ˣ) : cls u⁻¹ = (cls u)⁻¹ := by
  simp only [cls, map_inv, QuotientGroup.mk_inv]

theorem exists_of_cls_eq {u v : (SInt 𝔪)ˣ} (h : cls u = cls v) : ∃ w : (SInt 𝔪)ˣ, u = v * w ^ 6 := by
  have h' := QuotientGroup.eq.1 h.symm
  obtain ⟨w, hw⟩ := h'
  refine ⟨eU 𝔪 w, ?_⟩
  have : eU 𝔪 (w ^ 6) = eU 𝔪 (((eU 𝔪).symm v)⁻¹ * (eU 𝔪).symm u) := by
    rw [← hw]; rfl
  rw [map_pow, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  rw [this, mul_inv_cancel_left]

variable [Fintype (SClass 𝔪)]

/-- Reindexing a class sum. -/
theorem sum_cls_reindex (Φ : SInt 𝔪 → ℂ) (hΦ : ∀ (w : (SInt 𝔪)ˣ) y, Φ ((w : SInt 𝔪) ^ 6 * y) = Φ y)
    (φ : SClass 𝔪 → (SInt 𝔪)ˣ) (π : SClass 𝔪 ≃ SClass 𝔪) (hφ : ∀ ε, cls (φ ε) = π ε)
    (y : SInt 𝔪) :
    ∑ ε, Φ ((φ ε : SInt 𝔪) * y) = ∑ ε : SClass 𝔪, Φ (ε.rep * y) := by
  refine Fintype.sum_equiv π _ _ fun ε => ?_
  obtain ⟨w, hw⟩ := exists_of_cls_eq (u := φ ε) (v := repU (π ε)) (by rw [hφ, cls_repU])
  rw [hw, Units.val_mul, Units.val_pow_eq_pow_val, ← coe_repU,
    show ((repU (π ε) : SInt 𝔪) * (w : SInt 𝔪) ^ 6) * y = (w : SInt 𝔪) ^ 6 *
      ((repU (π ε) : SInt 𝔪) * y) by ring, hΦ]

/-! ### The averaged coefficient -/

/-- `c♯(x) = Σ_ε c(rep ε · x)`. -/
noncomputable def cAvg (c : SInt 𝔪 → ℂ) (x : SInt 𝔪) : ℂ := ∑ ε : SClass 𝔪, c (ε.rep * x)

theorem cAvg_periodic {𝔫 : Ideal (𝓞 F)} (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x) :
    ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → cAvg c (x + y) = cAvg c x := by
  intro x y hy
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [mul_add]
  exact hc _ _ (Ideal.mul_mem_left _ _ hy)

theorem cAvg_unit (c : SInt 𝔪 → ℂ) (hc6 : ∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x)
    (u : (SInt 𝔪)ˣ) (x : SInt 𝔪) : cAvg c ((u : SInt 𝔪) * x) = cAvg c x := by
  unfold cAvg
  have := sum_cls_reindex c (fun w y => hc6 y w) (fun ε => repU ε * u) (Equiv.mulRight (cls u))
    (fun ε => by rw [cls_mul, cls_repU]; rfl) x
  rw [← this]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Units.val_mul, coe_repU, mul_assoc]

/-! ### The dual coefficient of `c♯` -/

variable {𝔫 : Ideal (𝓞 F)} [Fintype (Qn 𝔪 𝔫)]

theorem chm_comp_unit (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (a : (SInt 𝔪)ˣ) (h : SInt 𝔪) :
    chm (𝔫 := 𝔫) (fun y => c ((a : SInt 𝔪) * y)) ν (h : F) =
      chm (𝔫 := 𝔫) c ν ((((a⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * h : SInt 𝔪) : F) := by
  set I := 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))
  set u : (Qn 𝔪 𝔫)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom a
  rw [chm, chm]
  refine Fintype.sum_equiv (Units.mulLeft u) (M := ℂ) _ _ fun xc => ?_
  simp only [Units.mulLeft_apply]
  have hmem : quotLift ((u : Qn 𝔪 𝔫) * xc) - (a : SInt 𝔪) * quotLift xc ∈ I := by
    have h1 : ((u : Qn 𝔪 𝔫) * xc) = Ideal.Quotient.mk I ((a : SInt 𝔪) * quotLift xc) := by
      rw [map_mul]
      congr 1
      exact (Function.surjInv_eq Ideal.Quotient.mk_surjective xc).symm
    rw [h1]
    exact quotLift_sub_mem _
  rw [periodic_eq c hc hmem, sAddChar_shift h𝔫 hν hmem]
  congr 2
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, coe_unit_inv]
  have := coe_unit_ne_zero a
  push_cast
  field_simp

theorem chm_unit_inv (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (a : (SInt 𝔪)ˣ) (ha : ∀ y, c ((a : SInt 𝔪) * y) = c y) (h : SInt 𝔪) :
    chm (𝔫 := 𝔫) c ν ((((a : SInt 𝔪) * h : SInt 𝔪)) : F) = chm (𝔫 := 𝔫) c ν (h : F) := by
  have := chm_comp_unit h𝔫 hν c hc a ((a : SInt 𝔪) * h)
  rw [show (fun y => c ((a : SInt 𝔪) * y)) = c from funext ha, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul] at this
  exact this

theorem chm_six (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (hc6 : ∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x)
    (w : (SInt 𝔪)ˣ) (h : SInt 𝔪) :
    chm (𝔫 := 𝔫) c ν ((((w : SInt 𝔪) ^ 6 * h : SInt 𝔪)) : F) = chm (𝔫 := 𝔫) c ν (h : F) := by
  have := chm_unit_inv h𝔫 hν c hc (w ^ 6) (fun y => by rw [Units.val_pow_eq_pow_val, hc6]) h
  rwa [Units.val_pow_eq_pow_val] at this

theorem chm_cAvg (h𝔫 : IsExterior 𝔪 𝔫) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (hc6 : ∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x) (h : SInt 𝔪) :
    chm (𝔫 := 𝔫) (cAvg c) ν (h : F) =
      ∑ ε : SClass 𝔪, chm (𝔫 := 𝔫) c ν (((-ε.rep * h : SInt 𝔪)) : F) := by
  have hlin : chm (𝔫 := 𝔫) (cAvg c) ν (h : F) =
      ∑ ε : SClass 𝔪, chm (𝔫 := 𝔫) (fun y => c ((repU ε : SInt 𝔪) * y)) ν (h : F) := by
    simp only [chm, cAvg, Finset.sum_mul, coe_repU]
    exact Finset.sum_comm
  rw [hlin]
  simp_rw [chm_comp_unit h𝔫 hν c hc]
  set Φ : SInt 𝔪 → ℂ := fun y => chm (𝔫 := 𝔫) c ν (y : F)
  have hΦ : ∀ (w : (SInt 𝔪)ˣ) y, Φ ((w : SInt 𝔪) ^ 6 * y) = Φ y := fun w y =>
    chm_six h𝔫 hν c hc hc6 w y
  have h1 := sum_cls_reindex Φ hΦ (fun ε => (repU ε)⁻¹) (Equiv.inv _)
    (fun ε => by rw [cls_inv, cls_repU]; rfl) h
  have h2 := sum_cls_reindex Φ hΦ (fun ε => -1 * repU ε) (Equiv.mulLeft (cls (-1)))
    (fun ε => by rw [cls_mul, cls_repU]; rfl) h
  simp only [Φ] at h1 h2
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 2
  simp only [Units.val_mul, Units.val_neg, Units.val_one, coe_repU]
  ring

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Fin: the Poisson cut, assembled

From the class-form identity (★) for the average `c♯` over `U_S/U_S⁶`, rewrite the rows over
`RowClass = Ext × SClass` and the dual side over `FreqClass × Ext` via `𝔥 = 𝔲 𝔯⁶`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical nonZeroDivisors

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
variable {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

theorem norm_Dw_le {dd : ℝ} (hd : 0 < dd) (Acst : ℝ) {X : ℝ} (hX : 0 < X) :
    ‖Dw (K := F) (qS (𝔪 := 𝔪)) dd Acst X‖ ≤
      |Acst| / X * (9 / 4 * dd ^ 2 / X ^ 2 * I3 F * ∑' j, uJ (𝔪 := 𝔪) j) := by
  set C := 9 / 4 * dd ^ 2 / X ^ 2 * I3 F
  have hterm : ∀ j, ‖(Om (qS (𝔪 := 𝔪)) j : ℂ) * ∫ b : realSpace F,
      PhiHat PhiT b * (Real.exp (∑ w, b w) : ℂ) *
        (rho (X * NN (qS (𝔪 := 𝔪)) j * Real.exp (-∑ w, b w) / dd) : ℂ)‖ ≤ C * uJ j := by
    intro j
    rw [← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc _ ≤ ∫ b : realSpace F, (‖(1 : ℂ)‖ * (9 / 4 * dd ^ 2 / X ^ 2) * uJ j) *
          (‖PhiHat PhiT b‖ * Real.exp (3 * ∑ w, b w)) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_beta3.const_mul _) (Filter.Eventually.of_forall fun b => ?_)
          have := pt_bound (𝔪 := 𝔪) 1 hX hd j b
          rwa [one_mul] at this
      _ = C * uJ j := by rw [integral_const_mul, ← I3, norm_one]; ring
  have hs : Summable fun j => ‖(Om (qS (𝔪 := 𝔪)) j : ℂ) * ∫ b : realSpace F,
      PhiHat PhiT b * (Real.exp (∑ w, b w) : ℂ) *
        (rho (X * NN (qS (𝔪 := 𝔪)) j * Real.exp (-∑ w, b w) / dd) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (summable_uJ.mul_left _)
  rw [Dw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hX]
  gcongr
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hterm hs (summable_uJ.mul_left _)

/-- The bijection `((𝔲, ε), 𝔯) ↦ (𝔲 𝔯⁶, ε)`. -/
noncomputable def eqv (𝔪 : Ideal (𝓞 F)) :
    FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯} ≃
      {𝔥 : Ideal (𝓞 F) // IsExterior 𝔪 𝔥} × SClass 𝔪 where
  toFun p := (sixEquiv 𝔪 (p.1.1, p.2), p.1.2)
  invFun q := ((((sixEquiv 𝔪).symm q.1).1, q.2), ((sixEquiv 𝔪).symm q.1).2)
  left_inv p := by simp
  right_inv q := by simp

variable {ι : F →+* ℂ}

theorem eqv_fst (p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯}) :
    ((eqv 𝔪 p).1 : Ideal (𝓞 F)) = p.1.1.1 * p.2.1 ^ 6 := rfl

theorem eqv_snd (p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯}) :
    (eqv 𝔪 p).2 = p.1.2 := rfl

theorem diffInS_of {𝔪 : Ideal (𝓞 F)}
    (hsm : SmallPrimesDvd (Ideal.absNorm (differentIdeal ℤ (𝓞 F))) 𝔪) : DiffInS 𝔪 := by
  intro w hw
  have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  have hle : Ideal.absNorm w.asIdeal ≤ Ideal.absNorm (differentIdeal ℤ (𝓞 F)) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hw))
  exact hsm w.asIdeal w.isPrime w.ne_bot hle

variable [Fintype (SClass 𝔪)]

theorem summable_B {𝔫 : Ideal (𝓞 F)} (h𝔫 : IsExterior 𝔪 𝔫) [Fintype (Qn 𝔪 𝔫)]
    (c : SInt 𝔪 → ℂ) (ν : SInt 𝔪) (g : AllowedGen ι 𝔪) {T : ℝ} (hT : 0 < T) {dd : ℝ} (hd : 0 < dd)
    (Acst : ℝ) :
    Summable fun q : {𝔥 : Ideal (𝓞 F) // IsExterior 𝔪 𝔥} × SClass 𝔪 =>
      chm (𝔫 := 𝔫) c ν ((-q.2.rep * g.gen q.1.1 : SInt 𝔪) : F) *
        Dw (K := F) (qS (𝔪 := 𝔪)) dd Acst (T * Ideal.absNorm q.1.1 / Ideal.absNorm 𝔫) := by
  set Cc := ∑ xc : Qn 𝔪 𝔫, ‖c (quotLift xc)‖
  set U := ∑' j, uJ (𝔪 := 𝔪) j
  have hU : 0 ≤ U := tsum_nonneg uJ_nonneg
  have hI := I3_nonneg (F := F)
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h𝔫0 : (0 : ℝ) < Ideal.absNorm 𝔫 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫.1)
  set K := Cc * (|Acst| * (9 / 4 * dd ^ 2) * I3 F * U * (Ideal.absNorm 𝔫 / T) ^ 3)
  have hsum : Summable fun 𝔥 : {𝔥 : Ideal (𝓞 F) // IsExterior 𝔪 𝔥} =>
      ((Ideal.absNorm 𝔥.1 : ℕ) : ℝ) ^ (-(3 : ℝ)) :=
    (T12B.summable_absNorm_rpow (F := F) (by norm_num : (1 : ℝ) < 3)).comp_injective
      Subtype.val_injective
  have hG : Summable fun q : {𝔥 : Ideal (𝓞 F) // IsExterior 𝔪 𝔥} × SClass 𝔪 =>
      K * ((Ideal.absNorm q.1.1 : ℕ) : ℝ) ^ (-(3 : ℝ)) := by
    refine (summable_prod_of_nonneg (fun q => ?_)).2 ⟨fun _ => Summable.of_finite, ?_⟩
    · have : 0 ≤ K := by positivity
      positivity
    · refine ((hsum.mul_left K).mul_left (Fintype.card (SClass 𝔪) : ℝ)).congr fun 𝔥 => ?_
      rw [tsum_fintype]
      simp
  refine Summable.of_norm_bounded hG fun q => ?_
  have h𝔥0 : (0 : ℝ) < Ideal.absNorm q.1.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.1.2.1)
  have hX : 0 < T * Ideal.absNorm q.1.1 / Ideal.absNorm 𝔫 := by positivity
  rw [norm_mul]
  refine (mul_le_mul (norm_chm_le c ν _) (norm_Dw_le hd Acst hX) (norm_nonneg _) hCc).trans
    (le_of_eq ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg _), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  simp only [K]
  field_simp
  simp only [Cc, U]
  ring

/-- The dual coefficient of the statement is `ĉ⁻(−z)`. -/
theorem finsum_eq_chm {𝔫 : Ideal (𝓞 F)} [Fintype (Qn 𝔪 𝔫)] (c : SInt 𝔪 → ℂ) (ν z : SInt 𝔪) :
    (∑ᶠ x : SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)),
      c (quotLift x) * sAddChar 𝔪 ((z : F) * (quotLift x : F) / (ν : F))) =
      chm (𝔫 := 𝔫) c ν ((-z : SInt 𝔪) : F) := by
  rw [finsum_eq_sum_of_fintype, chm]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 2
  push_cast
  ring

theorem row_summable (g : AllowedGen ι 𝔪) (c : SInt 𝔪 → ℂ) (V : ℝ → ℝ) (B : ℕ)
    (hV : ∀ 𝔟 : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟}, B < Ideal.absNorm 𝔟.1 →
      V (Ideal.absNorm 𝔟.1) = 0) :
    Summable fun r : RowClass 𝔪 => c (rowElt g r) * ((V (Ideal.absNorm r.1.1) : ℝ) : ℂ) := by
  have hS : {𝔟 : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟} | Ideal.absNorm 𝔟.1 ≤ B}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le B).preimage Subtype.val_injective.injOn
  have hfin := hS.prod (Set.finite_univ (α := SClass 𝔪))
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun r hr => ?_
  have : B < Ideal.absNorm r.1.1 := by
    by_contra hle
    push Not at hle
    exact hr (hfin.mem_toFinset.2 ⟨hle, Set.mem_univ _⟩)
  rw [hV r.1 this, Complex.ofReal_zero, mul_zero]

/-- **The Poisson cut, for fixed data.** -/
theorem poisson_rowElt (h𝔪 : 𝔪 ≠ ⊥) (hD : DiffInS 𝔪) (g : AllowedGen ι 𝔪) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : IsExterior 𝔪 𝔫) [Fintype (Qn 𝔪 𝔫)] {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪))) (c : SInt 𝔪 → ℂ)
    (hc : ∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x)
    (hc6 : ∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x) {T : ℝ} (hT : 0 < T) :
    HasSum (fun r : RowClass 𝔪 => c (rowElt g r) *
        ((Vw (Fintype.card {w : InfinitePlace F // w ≠ w0 F}) (Ideal.absNorm r.1.1 / T) : ℝ) : ℂ))
      (((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) *
        ∑' p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯},
          (∑ᶠ x : SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)),
            c (quotLift x) * sAddChar 𝔪
              (((freqElt g p.1 * g.gen p.2.1 ^ 6 : SInt 𝔪) : F) * (quotLift x : F) / (ν : F))) *
          mellinInv 2 (Mw (K := F) (qS (𝔪 := 𝔪)) |(discr F : ℝ)| (|(discr F : ℝ)| / CK F))
            (T * (Ideal.absNorm p.1.1.1 * Ideal.absNorm p.2.1 ^ 6) / Ideal.absNorm 𝔫)) := by
  set nV := Fintype.card {w : InfinitePlace F // w ≠ w0 F}
  have hdd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  have h𝔫0 : (0 : ℝ) < Ideal.absNorm 𝔫 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫.1)
  -- the rows
  set f : RowClass 𝔪 → ℂ := fun r => c (rowElt g r) * ((Vw nV (Ideal.absNorm r.1.1 / T) : ℝ) : ℂ)
  have hf : Summable f := by
    refine row_summable g c (fun t => Vw nV (t / T)) ⌈4 * Real.exp 2 * T⌉₊ fun 𝔟 h𝔟 => ?_
    refine Vw_eq_zero nV (Or.inr ?_)
    rw [lt_div_iff₀ hT]
    have := Nat.lt_of_ceil_lt h𝔟
    exact_mod_cast this
  have hL : ∑' r, f r = ∑' 𝔟 : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟},
      cAvg c (g.gen 𝔟.1) * (Vt (F := F) (Ideal.absNorm 𝔟.1 / T) : ℂ) := by
    rw [hf.tsum_prod]
    refine tsum_congr fun 𝔟 => ?_
    rw [tsum_fintype, cAvg, Finset.sum_mul, Vt_eq_Vw]
    rfl
  have hstar := star h𝔪 hD h𝔫 hν (cAvg c) (cAvg_periodic c hc) (fun ε x => cAvg_unit c hc6 ε x)
    g hT
  have hS := hf.hasSum
  rw [hL, hstar] at hS
  convert hS using 1
  -- the dual side
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  congr 1
  have hB := summable_B h𝔫 c ν g hT hdd (|(discr F : ℝ)| / CK F)
  have h1 : ∀ 𝔥 : {𝔥 : Ideal (𝓞 F) // IsExterior 𝔪 𝔥},
      chm (𝔫 := 𝔫) (cAvg c) ν ((g.gen 𝔥.1 : SInt 𝔪) : F) *
        Dw (K := F) (qS (𝔪 := 𝔪)) |(discr F : ℝ)| (|(discr F : ℝ)| / CK F) (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) =
      ∑' ε : SClass 𝔪, chm (𝔫 := 𝔫) c ν ((-ε.rep * g.gen 𝔥.1 : SInt 𝔪) : F) *
        Dw (K := F) (qS (𝔪 := 𝔪)) |(discr F : ℝ)| (|(discr F : ℝ)| / CK F) (T * Ideal.absNorm 𝔥.1 / Ideal.absNorm 𝔫) := by
    intro 𝔥
    rw [tsum_fintype, chm_cAvg h𝔫 hν c hc hc6, Finset.sum_mul]
  simp_rw [h1]
  rw [← hB.tsum_prod, ← (eqv 𝔪).tsum_eq]
  refine (tsum_congr fun p => ?_).symm
  obtain ⟨⟨𝔲, ε⟩, 𝔯⟩ := p
  obtain ⟨w, hw⟩ := gen_six_unit g 𝔲.2.1 𝔯.2
  have hN : (Ideal.absNorm ((eqv 𝔪 ((𝔲, ε), 𝔯)).1 : Ideal (𝓞 F)) : ℝ) =
      Ideal.absNorm 𝔲.1 * Ideal.absNorm 𝔯.1 ^ 6 := by
    rw [eqv_fst, map_mul, map_pow]; push_cast; rfl
  have h𝔲0 : (0 : ℝ) < Ideal.absNorm 𝔲.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔲.2.1.1)
  have h𝔯0 : (0 : ℝ) < Ideal.absNorm 𝔯.1 := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔯.2.1)
  have hX : 0 < T * (Ideal.absNorm 𝔲.1 * Ideal.absNorm 𝔯.1 ^ 6 : ℝ) / Ideal.absNorm 𝔫 := by
    positivity
  rw [finsum_eq_chm, mellinInv_Mw _ one_lt_qS |(discr F : ℝ)| (|(discr F : ℝ)| / CK F) hdd hX, hN, eqv_snd]
  congr 1
  have hz : (((-(freqElt g (𝔲, ε) * g.gen 𝔯.1 ^ 6) : SInt 𝔪)) : F) =
      ((((w : SInt 𝔪) ^ 6 * (-ε.rep * g.gen (eqv 𝔪 ((𝔲, ε), 𝔯)).1.1) : SInt 𝔪)) : F) := by
    rw [eqv_fst]
    simp only [freqElt]
    push_cast
    rw [show -((ε.rep : F) * (g.gen 𝔲.1 : F) * (g.gen 𝔯.1 : F) ^ 6) =
      -(ε.rep : F) * (((g.gen 𝔲.1 * g.gen 𝔯.1 ^ 6 : SInt 𝔪)) : F) by push_cast; ring, hw]
    ring
  rw [hz, chm_six h𝔫 hν c hc hc6]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Main: the Poisson cut (does not import its stub)

`chk_exists_cutoff_exists_weights_hasSum_poisson_rowElt` has the statement of
`ArtinPrimitiveRoots.exists_cutoff_exists_weights_hasSum_poisson_rowElt` verbatim.
`N₀ = N(𝔡_F)`, `V = Vw`, `M = Mw` (Mellin weight of `D`), via `L3P.poisson_rowElt`.
-/

namespace ArtinPrimitiveRoots

open NumberField

theorem chk_exists_cutoff_exists_weights_hasSum_poisson_rowElt (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ (V : ℝ → ℝ) (M : ℂ → ℂ), IsProbeWeight V ∧ IsMellinWeight M ∧ M (1 / 6) ≠ 0 ∧
        ∀ (g : AllowedGen ι 𝔪) (𝔫 : Ideal (𝓞 F)), IsExterior 𝔪 𝔫 →
          ∀ ν : SInt 𝔪, Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) →
          ∀ c : SInt 𝔪 → ℂ,
            (∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x) →
            (∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x) →
            ∀ T : ℝ, 0 < T →
              HasSum (fun r : RowClass 𝔪 =>
                  c (rowElt g r) * ((V (Ideal.absNorm r.1.1 / T) : ℝ) : ℂ))
                (((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) *
                  ∑' p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯},
                    (∑ᶠ x : SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)),
                      c (quotLift x) * sAddChar 𝔪
                        (((freqElt g p.1 * g.gen p.2.1 ^ 6 : SInt 𝔪) : F) * (quotLift x : F) /
                          (ν : F))) *
                    mellinInv 2 M (T * (Ideal.absNorm p.1.1.1 * Ideal.absNorm p.2.1 ^ 6) /
                      Ideal.absNorm 𝔫)) := by
  classical
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : IsTotallyComplex F := IsCyclotomicExtension.Rat.isTotallyComplex (n := n) F
    (by have := Nat.le_of_dvd hn0 hn; omega)
  refine ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 F)), fun 𝔪 h𝔪 hsm => ?_⟩
  haveI : Fintype (L3P.SP 𝔪) := (L2B.placesOf_finite h𝔪).fintype
  haveI : Fintype (SClass 𝔪) := @Fintype.ofFinite _ (L2B.finite_SClass h𝔪)
  have hD : L3P.DiffInS 𝔪 := L3P.diffInS_of hsm
  have hdd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  have hA : |(discr F : ℝ)| / L3P.CK F ≠ 0 := (div_pos hdd L3P.CK_pos).ne'
  refine ⟨L3P.Vw (Fintype.card {w : InfinitePlace F // w ≠ L3P.w0 F}),
    L3P.Mw (K := F) (L3P.qS (𝔪 := 𝔪)) |(discr F : ℝ)| (|(discr F : ℝ)| / L3P.CK F),
    L3P.isProbeWeight_Vw _, L3P.isMellinWeight_Mw _ L3P.one_lt_qS _ _,
    L3P.Mw_ne_zero _ L3P.one_lt_qS _ _ hA, ?_⟩
  intro g 𝔫 h𝔫 ν hν c hc hc6 T hT
  haveI : Fintype (L3P.Qn 𝔪 𝔫) := @Fintype.ofFinite _ (L2B.finite_quot_map 𝔫 h𝔫.1 h𝔫.2)
  exact L3P.poisson_rowElt h𝔪 hD g h𝔫 hν c hc hc6 hT

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3P_Dev: the Poisson cut under the target's own name (does not import its stub) -/

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_weights_hasSum_poisson_rowElt (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ (V : ℝ → ℝ) (M : ℂ → ℂ), IsProbeWeight V ∧ IsMellinWeight M ∧ M (1 / 6) ≠ 0 ∧
        ∀ (g : AllowedGen ι 𝔪) (𝔫 : Ideal (𝓞 F)), IsExterior 𝔪 𝔫 →
          ∀ ν : SInt 𝔪, Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) →
          ∀ c : SInt 𝔪 → ℂ,
            (∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x) →
            (∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x) →
            ∀ T : ℝ, 0 < T →
              HasSum (fun r : RowClass 𝔪 =>
                  c (rowElt g r) * ((V (Ideal.absNorm r.1.1 / T) : ℝ) : ℂ))
                (((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) *
                  ∑' p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯},
                    (∑ᶠ x : SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)),
                      c (quotLift x) * sAddChar 𝔪
                        (((freqElt g p.1 * g.gen p.2.1 ^ 6 : SInt 𝔪) : F) * (quotLift x : F) /
                          (ν : F))) *
                    mellinInv 2 M (T * (Ideal.absNorm p.1.1.1 * Ideal.absNorm p.2.1 ^ 6) /
                      Ideal.absNorm 𝔫)) :=
  chk_exists_cutoff_exists_weights_hasSum_poisson_rowElt n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ (V : ℝ → ℝ) (M : ℂ → ℂ), IsProbeWeight V ∧ IsMellinWeight M ∧ M (1 / 6) ≠ 0 ∧
        ∀ (g : AllowedGen ι 𝔪) (𝔫 : Ideal (𝓞 F)), IsExterior 𝔪 𝔫 →
          ∀ ν : SInt 𝔪, Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) →
          ∀ c : SInt 𝔪 → ℂ,
            (∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x) →
            (∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x) →
            ∀ T : ℝ, 0 < T →
              HasSum (fun r : RowClass 𝔪 =>
                  c (rowElt g r) * ((V (Ideal.absNorm r.1.1 / T) : ℝ) : ℂ))
                (((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) *
                  ∑' p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯},
                    (∑ᶠ x : SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)),
                      c (quotLift x) * sAddChar 𝔪
                        (((freqElt g p.1 * g.gen p.2.1 ^ 6 : SInt 𝔪) : F) * (quotLift x : F) /
                          (ν : F))) *
                    mellinInv 2 M (T * (Ideal.absNorm p.1.1.1 * Ideal.absNorm p.2.1 ^ 6) /
                      Ideal.absNorm 𝔫)) := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_weights_hasSum_poisson_rowElt n hn0 hn F ι

end
