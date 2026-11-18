-- Prove2me | solution 1 for ArtinKP.X.X.inner_coreLap_coreL2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:33:00.322864+00:00
-- url     : https://prove2.me/submissions/56799d9a-0d70-45ba-affb-4450cfeeac8e

import Mathlib
import Definitions.Def_ArtinKPB011
import Definitions.Def_ArtinKPB013
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
import Theorems.Thm_ArtinKP_X_X_smooth_of_mem_core

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

namespace H3

lemma coe_eq (P : H3) : P.coe = (P.x, P.v) := rfl

end H3

open H3

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
attribute [-simp] _root_.ArtinKP.X.e1_one _root_.ArtinKP.X.e1_two _root_.ArtinKP.X.e1_zero
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

section PiDensity

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

variable {ι : Type*} [Fintype ι]

/-- Tonelli on a finite product, for a product of functions of one coordinate each. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → ℝ≥0∞)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))]

/-- A product of measures with densities is the product measure with the product density. -/
theorem pi_withDensity {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h : ∀ x : ∀ i, α i, (Set.pi univ s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, forall_true_left, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  simp_rw [h]
  rw [lintegral_fintype_prod_eq_prod _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PiDensity

/-! ### One factor -/

lemma map_exp_withDensity :
    Measure.map Real.exp
        ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal ((v ^ 3)⁻¹) := by
  ext s hs
  rw [Measure.map_apply Real.measurable_exp hs, withDensity_apply _ (Real.measurable_exp hs),
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Real.exp ⁻¹' s) (f := Real.exp)
    (f' := Real.exp) (Real.measurable_exp hs)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun v => ENNReal.ofReal ((v ^ 3)⁻¹))
  rw [image_preimage_eq_inter_range, Real.range_exp] at h
  rw [h]
  refine setLIntegral_congr_fun (Real.measurable_exp hs) fun t _ => ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos t), ← Real.exp_nat_mul,
    ← Real.exp_neg, ← Real.exp_add]
  congr 2
  push_cast
  ring

lemma map_coe_chart1 : Measure.map (fun p : E1 => (p.1, Real.exp p.2)) mu1 = amb := by
  have h0 : mu1 = (volume : Measure ℂ).prod
      ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) := by
    rw [prod_withDensity_right (by fun_prop)]
    rfl
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have h3 : (fun p : E1 => (p.1, Real.exp p.2)) = Prod.map id Real.exp := rfl
  rw [h0, h3, ← Measure.map_prod_map _ _ measurable_id Real.measurable_exp, Measure.map_id,
    map_exp_withDensity, prod_withDensity_right (by fun_prop), h2]
  rfl

/-- `H3.vol` is the image of `exp (-2t) dx dt` under the chart. -/
theorem map_chart1 : Measure.map chart1 mu1 = H3.vol := by
  have h := map_coe_chart1
  have hc : (fun p : E1 => (p.1, Real.exp p.2)) = H3.coe ∘ chart1 := rfl
  rw [hc, ← Measure.map_map H3.measurableEmbedding_coe.measurable chart1.continuous.measurable] at h
  unfold H3.vol
  rw [← h, H3.measurableEmbedding_coe.comap_map]

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma rho_pos (y : Coord F) : 0 < rho y := Real.exp_pos _

lemma rho_eq_prod (y : Coord F) : rho y = ∏ w, rho1 (y w) := by
  unfold rho rho1
  rw [Finset.mul_sum, Real.exp_sum]

lemma continuous_rho : Continuous (rho : Coord F → ℝ) := by
  unfold rho; fun_prop

variable (F)

lemma muE_eq_pi : muE F = Measure.pi fun _ : InfinitePlace F => mu1 := by
  unfold mu1
  rw [pi_withDensity _ _ (fun _ => by unfold rho1; fun_prop)]
  unfold muE
  congr 1
  funext y
  rw [rho_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos (-2 * (y w).2)).le

/-- **The chart carries `exp (-2 ∑ t_w) dy` to the invariant measure.** -/
theorem measurePreserving_chart : MeasurePreserving (chart F) (muE F) (X.vol F) := by
  rw [muE_eq_pi]
  exact measurePreserving_pi (fun _ => mu1) (fun _ => H3.vol)
    (fun _ => ⟨chart1.continuous.measurable, map_chart1⟩)

variable {F}

theorem integral_vol_eq (f : X F → ℂ) :
    ∫ P, f P ∂X.vol F = ∫ y, (rho y : ℂ) * f (chart F y) := by
  rw [← (measurePreserving_chart F).integral_comp (chart F).measurableEmbedding f]
  unfold muE
  rw [integral_withDensity_eq_integral_toReal_smul (by unfold rho; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (rho_pos y).le]
  rw [Complex.real_smul]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Calc
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X2, file 2: calculus in the logarithmic chart

On `Coord F = InfinitePlace F → ℂ × ℝ` (coordinates `(x_w, t_w)`, `v_w = exp t_w`):

* `pd w k U` — partial derivative in the direction `bvec w k` (`k = 0, 1`: real and imaginary
  part of `x_w`; `k = 2`: `t_w`);
* `lapE U = ∑_w (-(e^{2t_w}(∂₀² + ∂₁²) + ∂₂²) U + 2 ∂₂ U)` — the Laplacian
  `∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` in the chart;
* `gamE U W = ∑_w (e^{2t_w}(∂₀U ∂₀W + ∂₁U ∂₁W) + ∂₂U ∂₂W)` — the (bilinear) carré du champ
  `∑_w v_w² ∇_w U · ∇_w W`;
* `green_E`: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` when one of `T`, `U` has compact support;
* Leibniz rules, compatibility with conjugation.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-- Decomposition of a vector of `E1` in the basis `e1`. -/
lemma e1_decomp (v : E1) : v = v.1.re • e1 0 + v.1.im • e1 1 + v.2 • e1 2 := by
  apply Prod.ext
  · apply Complex.ext <;> simp
  · simp

lemma clm_decomp (α : E1 →L[ℝ] ℂ) (v : E1) :
    α v = v.1.re * α (e1 0) + v.1.im * α (e1 1) + v.2 * α (e1 2) := by
  conv_lhs => rw [e1_decomp v]
  simp only [map_add, map_smul, Complex.real_smul]

theorem instIsAddHaarMeasureCoordVolume : (volume : Measure (Coord F)).IsAddHaarMeasure :=
  haveI _iHCR := ArtinKP.X.instIsAddHaarMeasureProdComplexRealVolume_solutions
  have h : (volume : Measure (Coord F)) = Measure.pi fun _ : InfinitePlace F => (volume : Measure E1) := rfl
  h ▸ { toIsFiniteMeasureOnCompacts := inferInstance
        toIsAddLeftInvariant := inferInstance
        toIsOpenPosMeasure := inferInstance }

/-! ### Regularity -/

lemma contDiff_pd_top {U : Coord F → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) U)
    (w : InfinitePlace F) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (pd w k U) :=
  contDiff_pd h (by exact le_rfl) w k

lemma contDiff_acoef (k : Fin 3) (w : InfinitePlace F) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : Coord F => ((acoef k (y w) : ℝ) : ℂ) := by
  unfold acoef
  split_ifs
  · exact contDiff_const
  · have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : Coord F => Real.exp (2 * (y w).2)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h

lemma contDiff_lapE {U : Coord F → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) U) :
    ContDiff ℝ (⊤ : ℕ∞) (lapE U) := by
  unfold lapE
  refine ContDiff.sum fun w _ => ContDiff.add (ContDiff.sum fun k _ => ContDiff.neg ?_) ?_
  · exact (contDiff_acoef k w).mul (contDiff_pd_top (contDiff_pd_top h w k) w k)
  · exact contDiff_const.mul (contDiff_pd_top h w 2)

lemma contDiff_gamE {U W : Coord F → ℂ} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) : ContDiff ℝ (⊤ : ℕ∞) (gamE U W) := by
  unfold gamE
  refine ContDiff.sum fun w _ => ContDiff.sum fun k _ => ?_
  exact (contDiff_acoef k w).mul ((contDiff_pd_top hU w k).mul (contDiff_pd_top hW w k))

/-! ### Algebraic rules -/

lemma pd_congr {U W : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] W)
    (w : InfinitePlace F) (k : Fin 3) : pd w k U =ᶠ[nhds y] pd w k W := by
  filter_upwards [h.eventually_nhds] with z hz
  unfold pd
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hz]

lemma lapE_congr {U W : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] W) :
    lapE U y = lapE W y := by
  unfold lapE
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [(pd_congr (pd_congr h w k) w k).self_of_nhds]
  · rw [(pd_congr h w 2).self_of_nhds]

lemma gamE_congr {U U' W W' : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] U')
    (h' : W =ᶠ[nhds y] W') : gamE U W y = gamE U' W' y := by
  unfold gamE
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
  rw [(pd_congr h w k).self_of_nhds, (pd_congr h' w k).self_of_nhds]

lemma gamE_comm (U W : Coord F → ℂ) : gamE U W = gamE W U := by
  funext y
  unfold gamE
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma pd_const (c : ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k (fun _ => c) y = 0 := by
  unfold pd
  simp

lemma pd_const' (c : ℂ) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun _ : Coord F => c) = fun _ => 0 := funext (pd_const c w k)

lemma pd_sum {ι : Type*} (s : Finset ι) {U : ι → Coord F → ℂ} {y : Coord F}
    (hU : ∀ i ∈ s, DifferentiableAt ℝ (U i) y) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun y => ∑ i ∈ s, U i y) y = ∑ i ∈ s, pd w k (U i) y := by
  unfold pd
  rw [fderiv_fun_sum hU]
  simp

lemma pd_conj (U : Coord F → ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k (fun y => conj (U y)) y = conj (pd w k U y) := by
  unfold pd
  have h : (fun y => conj (U y)) = Complex.conjCLE ∘ U := rfl
  rw [h, Complex.conjCLE.comp_fderiv]
  rfl

lemma lapE_sum {ι : Type*} (s : Finset ι) {U : ι → Coord F → ℂ}
    (hU : ∀ i ∈ s, ContDiff ℝ 2 (U i)) (y : Coord F) :
    lapE (fun y => ∑ i ∈ s, U i y) y = ∑ i ∈ s, lapE (U i) y := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp [lapE, pd_const']
  | insert a s ha ih =>
    have h1 : (fun y => ∑ i ∈ insert a s, U i y) = fun y => U a y + ∑ i ∈ s, U i y := by
      funext z; rw [Finset.sum_insert ha]
    rw [h1, lapE_add (hU a (Finset.mem_insert_self a s))
      (ContDiff.sum fun i hi => hU i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha,
      ih fun i hi => hU i (Finset.mem_insert_of_mem hi)]

lemma lapE_conj (U : Coord F → ℂ) (y : Coord F) :
    lapE (fun y => conj (U y)) y = conj (lapE U y) := by
  unfold lapE
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : ∀ k, pd w k (fun y => conj (U y)) = fun y => conj (pd w k U y) :=
    fun k => funext fun z => pd_conj U w k z
  simp_rw [h1, pd_conj]
  simp [map_sum, map_ofNat]

lemma gamE_sum_left {ι : Type*} (s : Finset ι) {U : ι → Coord F → ℂ} {W : Coord F → ℂ}
    {y : Coord F} (hU : ∀ i ∈ s, DifferentiableAt ℝ (U i) y) :
    gamE (fun y => ∑ i ∈ s, U i y) W y = ∑ i ∈ s, gamE (U i) W y := by
  unfold gamE
  simp_rw [pd_sum s hU]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]

/-! ### The weights `ρ · a_k` -/

lemma Ls_apply (y : Coord F) : Ls y = ∑ w, (y w).2 := by
  simp [Ls]

lemma Lw_apply (w : InfinitePlace F) (y : Coord F) : Lw w y = (y w).2 := rfl

lemma mC_eq (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    mC w k y = ((Real.exp (Lk w k y) : ℝ) : ℂ) := by
  unfold mC rho acoef Lk
  split_ifs
  · simp [Ls_apply]
  · rw [← Real.exp_add]
    simp [Ls_apply, Lw_apply]

lemma mC_two (w : InfinitePlace F) (y : Coord F) : mC w 2 y = (rho y : ℂ) := by
  simp [mC, acoef]

lemma hasFDerivAt_mC (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    HasFDerivAt (mC w k) (Complex.ofRealCLM.comp (Real.exp (Lk w k y) • Lk w k)) y := by
  have h : mC w k = fun y => ((Real.exp (Lk w k y) : ℝ) : ℂ) := funext (mC_eq w k)
  rw [h]
  exact Complex.ofRealCLM.hasFDerivAt.comp y (Lk w k).hasFDerivAt.exp

lemma contDiff_mC (w : InfinitePlace F) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mC w k) := by
  have h : mC w k = fun y => ((Real.exp (Lk w k y) : ℝ) : ℂ) := funext (mC_eq w k)
  rw [h]
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (Lk w k).contDiff)

lemma Lk_bvec (w : InfinitePlace F) (k : Fin 3) : ((Lk w k (bvec w k) : ℝ) : ℂ) = cco k := by
  have h1 : ∀ k, Ls (bvec w k) = (e1 k).2 := by
    intro k
    rw [Ls_apply]
    unfold bvec
    rw [Finset.sum_eq_single w]
    · simp
    · intro w' _ hw'
      simp [hw']
    · simp
  have h2 : ∀ k, Lw w (bvec w k) = (e1 k).2 := by
    intro k
    simp [Lw_apply, bvec]
  fin_cases k <;> simp [Lk, cco, h1, h2]

lemma fderiv_mC_bvec (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    fderiv ℝ (mC w k) y (bvec w k) = cco k * mC w k y := by
  rw [(hasFDerivAt_mC w k y).fderiv, mC_eq, ← Lk_bvec w k]
  simp
  ring

/-! ### Green's identity on the chart -/

lemma integrable_cmul {c A B : Coord F → ℂ} (hc : Continuous c) (hA : Continuous A)
    (hB : Continuous B) (h : HasCompactSupport A ∨ HasCompactSupport B) :
    Integrable (fun y => c y * (A y * B y)) := by
  refine (hc.mul (hA.mul hB)).integrable_of_hasCompactSupport ?_
  rcases h with h | h
  · exact (h.mul_right (f' := B)).mul_left (f := c)
  · exact (h.mul_left (f := A)).mul_left (f := c)

lemma ibp_term {U T : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (hT : ContDiff ℝ 1 T)
    (hc : HasCompactSupport T ∨ HasCompactSupport U) (w : InfinitePlace F) (k : Fin 3) :
    ∫ y, mC w k y * (T y * pd w k (pd w k U) y) =
      -(∫ y, mC w k y * (pd w k T y * pd w k U y)) - cco k * ∫ y, mC w k y * (T y * pd w k U y) := by
  haveI _iHCo := ArtinKP.X.instIsAddHaarMeasureCoordVolume (F := F)
  have hm := contDiff_mC (F := F) w k
  have hmc : Continuous (mC (F := F) w k) := hm.continuous
  have hTc : Continuous T := hT.continuous
  have hpT : Continuous (pd w k T) := (contDiff_pd (m := 0) hT (by simp) w k).continuous
  have hpU1 : ContDiff ℝ 1 (pd w k U) := contDiff_pd hU (by norm_num) w k
  have hpU : Continuous (pd w k U) := hpU1.continuous
  have hppU : Continuous (pd w k (pd w k U)) :=
    (contDiff_pd (m := 0) hpU1 (by simp) w k).continuous
  have hc1 : HasCompactSupport T ∨ HasCompactSupport (pd w k U) :=
    hc.imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc2 : HasCompactSupport T ∨ HasCompactSupport (pd w k (pd w k U)) :=
    hc1.imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc3 : HasCompactSupport (pd w k T) ∨ HasCompactSupport (pd w k U) :=
    hc1.imp (fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)) id
  have hTd : Differentiable ℝ T := hT.differentiable (by simp)
  have hmd : Differentiable ℝ (mC (F := F) w k) := hm.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun y => mC w k y * T y) y (bvec w k) =
      mC w k y * pd w k T y + cco k * (mC w k y * T y) := by
    intro y
    rw [fderiv_fun_mul (hmd y) (hTd y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_mC_bvec]
    unfold pd
    ring
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Coord F)))
    (f := fun y => mC w k y * T y) (g := pd w k U) (v := bvec w k) ?_ ?_ ?_
    (fun y _ => (hmd y).mul (hTd y)) (fun y _ => hpU1.differentiable (by simp) y)
  · have e1 : ∀ y, (mC w k y * T y) * fderiv ℝ (pd w k U) y (bvec w k) =
        mC w k y * (T y * pd w k (pd w k U) y) := fun y => by unfold pd; ring
    have e2 : ∀ y, fderiv ℝ (fun y => mC w k y * T y) y (bvec w k) * pd w k U y =
        mC w k y * (pd w k T y * pd w k U y) + cco k * (mC w k y * (T y * pd w k U y)) :=
      fun y => by rw [hfd]; ring
    simp_rw [e1, e2] at key
    rw [key, integral_add (integrable_cmul hmc hpT hpU hc3)
      ((integrable_cmul hmc hTc hpU hc1).const_mul _), integral_const_mul]
    ring
  · have e2 : (fun y => fderiv ℝ (fun y => mC w k y * T y) y (bvec w k) * pd w k U y) =
        fun y => mC w k y * (pd w k T y * pd w k U y) + cco k * (mC w k y * (T y * pd w k U y)) :=
      funext fun y => by rw [hfd]; ring
    rw [e2]
    exact (integrable_cmul hmc hpT hpU hc3).add ((integrable_cmul hmc hTc hpU hc1).const_mul _)
  · have e1 : (fun y => (mC w k y * T y) * fderiv ℝ (pd w k U) y (bvec w k)) =
        fun y => mC w k y * (T y * pd w k (pd w k U) y) := funext fun y => by unfold pd; ring
    rw [e1]
    exact integrable_cmul hmc hTc hppU hc2
  · have e1 : (fun y => (mC w k y * T y) * pd w k U y) =
        fun y => mC w k y * (T y * pd w k U y) := funext fun y => by ring
    rw [e1]
    exact integrable_cmul hmc hTc hpU hc1

/-- **Green's identity in the chart**: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` if `T` or `U` has compact
support. -/
theorem green_E {U T : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (hT : ContDiff ℝ 1 T)
    (hc : HasCompactSupport T ∨ HasCompactSupport U) :
    ∫ y, (rho y : ℂ) * (T y * lapE U y) = ∫ y, (rho y : ℂ) * gamE T U y := by
  have hTc : Continuous T := hT.continuous
  have hpT : ∀ w k, Continuous (pd w k T) :=
    fun w k => (contDiff_pd (m := 0) hT (by simp) w k).continuous
  have hpU1 : ∀ w k, ContDiff ℝ 1 (pd w k U) := fun w k => contDiff_pd hU (by norm_num) w k
  have hpU : ∀ w k, Continuous (pd w k U) := fun w k => (hpU1 w k).continuous
  have hppU : ∀ w k, Continuous (pd w k (pd w k U)) :=
    fun w k => (contDiff_pd (m := 0) (hpU1 w k) (by simp) w k).continuous
  have hmc : ∀ w k, Continuous (mC (F := F) w k) := fun w k => (contDiff_mC w k).continuous
  have hc1 : ∀ w k, HasCompactSupport T ∨ HasCompactSupport (pd w k U) :=
    fun w k => hc.imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc2 : ∀ w k, HasCompactSupport T ∨ HasCompactSupport (pd w k (pd w k U)) :=
    fun w k => (hc1 w k).imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc3 : ∀ w k, HasCompactSupport (pd w k T) ∨ HasCompactSupport (pd w k U) :=
    fun w k => (hc1 w k).imp (fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)) id
  have h1 : ∀ y, (rho y : ℂ) * (T y * lapE U y) =
      ∑ w, ((∑ k, -(mC w k y * (T y * pd w k (pd w k U) y))) +
        2 * (mC w 2 y * (T y * pd w 2 U y))) := by
    intro y
    unfold lapE
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, mC_two]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      unfold mC
      push_cast
      ring
    · ring
  have h2 : ∀ y, (rho y : ℂ) * gamE T U y =
      ∑ w, ∑ k, mC w k y * (pd w k T y * pd w k U y) := by
    intro y
    unfold gamE
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold mC
    push_cast
    ring
  simp_rw [h1, h2]
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_add, integral_finsetSum, integral_finsetSum, integral_const_mul]
    · simp_rw [integral_neg, ibp_term hU hT hc]
      simp only [Fin.sum_univ_three, cco]
      simp
      ring
    · exact fun k _ => integrable_cmul (hmc w k) (hpT w k) (hpU w k) (hc3 w k)
    · exact fun k _ => (integrable_cmul (hmc w k) hTc (hppU w k) (hc2 w k)).neg
    · exact integrable_finsetSum _
        fun k _ => (integrable_cmul (hmc w k) hTc (hppU w k) (hc2 w k)).neg
    · exact (integrable_cmul (hmc w 2) hTc (hpU w 2) (hc1 w 2)).const_mul _
  · exact fun w _ => integrable_finsetSum _
      fun k _ => integrable_cmul (hmc w k) (hpT w k) (hpU w k) (hc3 w k)
  · exact fun w _ => (integrable_finsetSum _
      fun k _ => (integrable_cmul (hmc w k) hTc (hppU w k) (hc2 w k)).neg).add
        ((integrable_cmul (hmc w 2) hTc (hpU w 2) (hc1 w 2)).const_mul _)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X2, file 3: the group acts by isometries; the Laplacian commutes with it

* `Iso1 φ`: a smooth self-map of one factor (in the chart) whose derivative is conformal for the
  hyperbolic metric; translations and the inversion `Jmap` (the chart form of the Weyl element)
  are such, hence every element of `SL(2,ℂ)` acts by one (`mem_iso1`).
* `IsoHalf Φ`: a smooth self-map of `Coord F` preserving the carré du champ.
* `lapE_comp_of_iso`: a measure-preserving `IsoHalf` bijection with `IsoHalf` inverse commutes
  with the Laplacian.  The proof is weak: test against `C_c^∞`, use Green twice — no second
  derivative of the Möbius action is ever computed.
* On `X`: `X.Smooth`, `X.lap`, `X.gam`, and their invariance under `G∞ = SL(2,ℂ)^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

/-! ### One factor -/

lemma Iso1.trans (b : ℂ) : Iso1 (fun p : E1 => (p.1 + b, p.2)) where
  smooth := by fun_prop
  conf p α β := by
    have h0 : (fun p : E1 => (p.1 + b, p.2)) = fun p => p + (b, 0) := by
      funext p; apply Prod.ext <;> simp
    have : fderiv ℝ (fun p : E1 => (p.1 + b, p.2)) p = ContinuousLinearMap.id ℝ E1 := by
      rw [h0, fderiv_add_const]; exact fderiv_id'
    simp [this, acoef]

lemma rhoJ_pos (p : E1) : 0 < rhoJ p := by
  unfold rhoJ; positivity

lemma contDiff_rhoJ : ContDiff ℝ (⊤ : ℕ∞) rhoJ := by
  unfold rhoJ
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.re :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.im :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have h3 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => Real.exp (2 * p.2) := by fun_prop
  exact ((h1.pow 2).add (h2.pow 2)).add h3

lemma contDiff_Jmap : ContDiff ℝ (⊤ : ℕ∞) Jmap := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.re :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.im :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hi : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => (rhoJ p)⁻¹ :=
    contDiff_rhoJ.inv fun p => (rhoJ_pos p).ne'
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => ((-p.1.re * (rhoJ p)⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (h1.neg.mul hi)
  have hB : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => ((p.1.im * (rhoJ p)⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (h2.mul hi)
  have hC : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.2 - Real.log (rhoJ p) :=
    contDiff_snd.sub (contDiff_rhoJ.log fun p => (rhoJ_pos p).ne')
  exact (hA.add (hB.mul contDiff_const)).prodMk hC

lemma fderiv_Jmap (p h : E1) :
    fderiv ℝ Jmap p h =
      (((-h.1.re * (rhoJ p)⁻¹ + p.1.re * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) +
          ((h.1.im * (rhoJ p)⁻¹ - p.1.im * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * Complex.I,
        h.2 - sJ p h * (rhoJ p)⁻¹) := by
  have hne : rhoJ p ≠ 0 := (rhoJ_pos p).ne'
  have hre : HasFDerivAt (fun p : E1 => p.1.re)
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).hasFDerivAt
  have him : HasFDerivAt (fun p : E1 => p.1.im)
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : E1 => p.2) (ContinuousLinearMap.snd ℝ ℂ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt
  have hρ := ((hre.pow 2).add (him.pow 2)).add ((hsnd.const_mul 2).exp)
  have hρ' : HasFDerivAt rhoJ _ p := hρ
  have hI := (hasDerivAt_inv hne).comp_hasFDerivAt p hρ'
  have hA := (hre.neg).mul hI
  have hB := him.mul hI
  have hC := hsnd.sub (hρ'.log hne)
  have hx := (Complex.ofRealCLM.hasFDerivAt.comp p hA).add
    ((Complex.ofRealCLM.hasFDerivAt.comp p hB).mul_const Complex.I)
  have hJ : HasFDerivAt Jmap _ p := hx.prodMk hC
  rw [hJ.fderiv]
  apply Prod.ext
  · apply Complex.ext
    · simp [sJ]
      ring
    · simp [sJ]
      ring
  · simp [sJ]
    ring

lemma acoef_Jmap (k : Fin 3) (p : E1) :
    acoef k (Jmap p) = if k = 2 then 1 else Real.exp (2 * p.2) * ((rhoJ p)⁻¹) ^ 2 := by
  unfold acoef
  split_ifs
  · rfl
  · have : 2 * (Jmap p).2 = 2 * p.2 - 2 * Real.log (rhoJ p) := by
      simp [Jmap]; ring
    have h2 : Real.exp (2 * Real.log (rhoJ p)) = rhoJ p ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log (rhoJ_pos p)]; ring
    rw [this, Real.exp_sub, h2, div_eq_mul_inv, inv_pow]

lemma iso1_Jmap : Iso1 Jmap where
  smooth := contDiff_Jmap
  conf p α β := by
    have hα : ∀ (γ : E1 →L[ℝ] ℂ) (h : E1), γ (fderiv ℝ Jmap p h) =
        ((-h.1.re * (rhoJ p)⁻¹ + p.1.re * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * γ (e1 0) +
        ((h.1.im * (rhoJ p)⁻¹ - p.1.im * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * γ (e1 1) +
        ((h.2 - sJ p h * (rhoJ p)⁻¹ : ℝ) : ℂ) * γ (e1 2) := by
      intro γ h
      have hr : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a := fun a b => by simp
      have hi : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).im = b := fun a b => by simp
      rw [clm_decomp γ, fderiv_Jmap]
      simp only [hr, hi]
    simp only [hα, Fin.sum_univ_three, acoef_Jmap]
    have hE : Real.exp (2 * p.2) = rhoJ p - p.1.re ^ 2 - p.1.im ^ 2 := by
      unfold rhoJ; ring
    have hne : (rhoJ p : ℂ) ≠ 0 := by exact_mod_cast (rhoJ_pos p).ne'
    simp only [acoef, sJ, e1_zero, e1_one, e1_two, hE]
    generalize α (1, 0) = a0
    generalize α (Complex.I, 0) = a1
    generalize α (0, 1) = a2
    generalize β (1, 0) = b0
    generalize β (Complex.I, 0) = b1
    generalize β (0, 1) = b2
    generalize rhoJ p = r at hne ⊢
    generalize p.1.re = x1
    generalize p.1.im = x2
    simp
    field_simp
    ring

/-! ### Every element of `SL(2,ℂ)` acts by an `Iso1` -/

lemma nMat_mem_iso1 (b : ℂ) : nMat b ∈ iso1Submonoid := by
  refine ⟨fun p => (p.1 + b, p.2), Iso1.trans b, fun p => ?_⟩
  have h := nMat_smul b (chart1 p)
  apply H3.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma wMat_mem_iso1 : wMat ∈ iso1Submonoid := by
  refine ⟨Jmap, iso1_Jmap, fun p => ?_⟩
  have h := wMat_smul (chart1 p)
  have hn : nsq (chart1 p).coe = rhoJ p := by
    simp only [nsq, rhoJ, H3.coe_eq, chart1_x, chart1_v, Complex.normSq_apply]
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hpos := rhoJ_pos p
  apply H3.ext
  · have h1 : (wMat • chart1 p).x = -conj (inv3 (chart1 p).coe).1 := by
      have := congrArg Prod.fst h; exact this
    rw [h1, inv3_fst, hn]
    change _ = (Jmap p).1
    apply Complex.ext
    · simp [Jmap, H3.coe_eq, Complex.div_re, Complex.normSq_apply]
      field_simp
    · simp [Jmap, H3.coe_eq, Complex.div_im, Complex.normSq_apply]
      field_simp
  · have h2 : (wMat • chart1 p).v = (inv3 (chart1 p).coe).2 := by
      have := congrArg Prod.snd h; exact this
    rw [h2, inv3_snd, hn]
    change _ = Real.exp (Jmap p).2
    simp only [Jmap, H3.coe_eq, chart1_v]
    rw [Real.exp_sub, Real.exp_log hpos]

lemma wMat_inv_eq : wMat⁻¹ = wMat * wMat * wMat := by
  apply Subtype.ext
  rw [wMat_inv_coe]
  simp only [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Every element of `SL(2,ℂ)` acts in the chart by a conformal smooth map.** -/
theorem mem_iso1 (g : SL(2, ℂ)) : g ∈ iso1Submonoid := by
  have hn := nMat_mem_iso1
  have hw := wMat_mem_iso1
  have hwi : wMat⁻¹ ∈ iso1Submonoid := by
    rw [wMat_inv_eq]
    exact iso1Submonoid.mul_mem (iso1Submonoid.mul_mem hw hw) hw
  have key : ∀ g : SL(2, ℂ), g 1 0 ≠ 0 → g ∈ iso1Submonoid := by
    intro g hc
    rw [bruhat_of_ne hc]
    exact iso1Submonoid.mul_mem (iso1Submonoid.mul_mem (iso1Submonoid.mul_mem
      (iso1Submonoid.mul_mem (iso1Submonoid.mul_mem
      (iso1Submonoid.mul_mem (hn _) (hn _)) hwi) (hn _)) hw) (hn _)) (hn _)
  by_cases hc : g 1 0 = 0
  · have h1 : (g * wMat) 1 0 ≠ 0 := by
      have hd := det_eq g
      have : (g * wMat) 1 0 = g 1 1 := by
        rw [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this]
      intro h
      rw [hc, h] at hd
      simp at hd
    have : g = (g * wMat) * wMat⁻¹ := by group
    rw [this]
    exact iso1Submonoid.mul_mem (key _ h1) hwi
  · exact key g hc

/-! ### Isometries of the chart -/

variable {F : Type*} [Field F] [NumberField F]

/-- A product of one-factor conformal maps is an isometry of the chart. -/
theorem isoHalf_pi {φ : InfinitePlace F → E1 → E1} (h : ∀ w, Iso1 (φ w)) :
    IsoHalf (fun (y : Coord F) w => φ w (y w)) where
  smooth := contDiff_pi.2 fun w => (h w).smooth.comp (contDiff_apply ℝ E1 w)
  gam_comp U W y hU hW := by
    show gamE (fun z => U (fun w => φ w (z w))) (fun z => W (fun w => φ w (z w))) y =
      gamE U W (fun w => φ w (y w))
    have hΦ : HasFDerivAt (fun (y : Coord F) w => φ w (y w)) (ContinuousLinearMap.pi fun w =>
        (fderiv ℝ (φ w) (y w)).comp (ContinuousLinearMap.proj w)) y :=
      hasFDerivAt_pi.2 fun w =>
        (((h w).smooth.differentiable (by simp) (y w)).hasFDerivAt).comp y
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => E1) w).hasFDerivAt
    have key : ∀ (V : Coord F → ℂ), DifferentiableAt ℝ V (fun w => φ w (y w)) → ∀ w k,
        pd w k (fun z => V (fun w => φ w (z w))) y =
          ((fderiv ℝ V (fun w => φ w (y w))).comp
            (ContinuousLinearMap.single ℝ (fun _ : InfinitePlace F => E1) w))
            (fderiv ℝ (φ w) (y w) (e1 k)) := by
      intro V hV w k
      unfold pd
      have hcomp := (hV.hasFDerivAt.comp y hΦ).fderiv
      rw [show (fun z : Coord F => V (fun w => φ w (z w))) =
        V ∘ (fun (y : Coord F) w => φ w (y w)) from rfl, hcomp]
      simp only [ContinuousLinearMap.comp_apply]
      congr 1
      funext w'
      by_cases hw : w' = w
      · subst hw
        simp [bvec]
      · simp [bvec, Pi.single_apply, hw]
    unfold gamE
    refine Finset.sum_congr rfl fun w _ => ?_
    simp_rw [key U hU w, key W hW w]
    exact (h w).conf (y w) _ _

/-- Integrals against `muE` are Lebesgue integrals with the weight `rho`. -/
lemma integral_muE (f : Coord F → ℂ) : ∫ y, f y ∂muE F = ∫ y, (rho y : ℂ) * f y := by
  unfold muE
  rw [integral_withDensity_eq_integral_toReal_smul (by unfold rho; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (rho_pos y).le]
  rw [Complex.real_smul]

/-- **The Laplacian commutes with measure-preserving isometries** (weak proof). -/
theorem lapE_comp_of_iso {Φ Ψ : Coord F → Coord F} (hΦ : IsoHalf Φ) (hΨ : IsoHalf Ψ)
    (h1 : ∀ y, Φ (Ψ y) = y) (h2 : ∀ y, Ψ (Φ y) = y)
    (hμ : MeasurePreserving Φ (muE F) (muE F))
    {U : Coord F → ℂ} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (y : Coord F) :
    lapE (fun z => U (Φ z)) y = lapE U (Φ y) := by
  let e : Coord F ≃ₜ Coord F :=
    { toFun := Φ
      invFun := Ψ
      left_inv := h2
      right_inv := h1
      continuous_toFun := hΦ.smooth.continuous
      continuous_invFun := hΨ.smooth.continuous }
  have hUΦ : ContDiff ℝ (⊤ : ℕ∞) (fun z => U (Φ z)) := hU.comp hΦ.smooth
  have hrc : Continuous fun y : Coord F => (rho y : ℂ) :=
    Complex.continuous_ofReal.comp continuous_rho
  have hl1 : Continuous (lapE fun z => U (Φ z)) := (contDiff_lapE hUΦ).continuous
  have hl2 : Continuous fun y => lapE U (Φ y) :=
    (contDiff_lapE hU).continuous.comp hΦ.smooth.continuous
  set D : Coord F → ℂ := fun y => (rho y : ℂ) * (lapE (fun z => U (Φ z)) y - lapE U (Φ y))
    with hD
  have hDc : Continuous D := hrc.mul (hl1.sub hl2)
  have hzero : ∀ᵐ y ∂(volume : Measure (Coord F)), D y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDc.locallyIntegrable) fun g hg hgc => ?_
    set T : Coord F → ℂ := fun y => (g y : ℂ) with hT
    have hTs : ContDiff ℝ (⊤ : ℕ∞) T := Complex.ofRealCLM.contDiff.comp hg
    have hTc : HasCompactSupport T := hgc.comp_left Complex.ofReal_zero
    set S : Coord F → ℂ := fun z => T (Ψ z) with hS
    have hSs : ContDiff ℝ (⊤ : ℕ∞) S := hTs.comp hΨ.smooth
    have hSc : HasCompactSupport S := hTc.comp_isClosedEmbedding e.symm.isClosedEmbedding
    have hTS : T = fun z => S (Φ z) := by
      funext z; simp only [hS, h2]
    have two : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    have one : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    have step1 := green_E (hUΦ.of_le two) (hTs.of_le one) (Or.inl hTc)
    have step2 : ∀ y, gamE T (fun z => U (Φ z)) y = gamE S U (Φ y) := by
      intro y
      rw [hTS]
      exact hΦ.gam_comp S U y ((hSs.differentiable (by simp)) _) ((hU.differentiable (by simp)) _)
    have step3 : ∫ y, (rho y : ℂ) * gamE S U (Φ y) = ∫ y, (rho y : ℂ) * gamE S U y := by
      rw [← integral_muE, ← integral_muE]
      exact hμ.integral_comp e.measurableEmbedding _
    have step4 := green_E (hU.of_le two) (hSs.of_le one) (Or.inl hSc)
    have step5 : ∫ y, (rho y : ℂ) * (S y * lapE U y) =
        ∫ y, (rho y : ℂ) * (T y * lapE U (Φ y)) := by
      rw [← integral_muE, ← integral_muE]
      rw [← hμ.integral_comp e.measurableEmbedding (fun y => S y * lapE U y)]
      rw [hTS]
    have hsplit : ∀ y, g y • D y =
        (rho y : ℂ) * (T y * lapE (fun z => U (Φ z)) y) - (rho y : ℂ) * (T y * lapE U (Φ y)) := by
      intro y
      simp only [hD, hT, Complex.real_smul]
      ring
    simp_rw [hsplit]
    rw [integral_sub (integrable_cmul hrc hTs.continuous hl1 (Or.inl hTc))
      (integrable_cmul hrc hTs.continuous hl2 (Or.inl hTc)), step1]
    simp_rw [step2]
    rw [step3, ← step4, step5, sub_self]
  have hD0 : D = 0 := (hDc.ae_eq_iff_eq volume continuous_zero).1 hzero
  have := congrFun hD0 y
  simp only [hD, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero, (rho_pos y).ne',
    false_or] at this
  exact sub_eq_zero.1 this

/-! ### The action of `G∞` in the chart -/

lemma chart_actE (g : Ginf F) (y : Coord F) : chart F (actE g y) = g • chart F y := by
  simp [actE]

lemma actE_inv_actE (g : Ginf F) (y : Coord F) : actE g⁻¹ (actE g y) = y := by
  unfold actE
  rw [Homeomorph.apply_symm_apply, inv_smul_smul, Homeomorph.symm_apply_apply]

lemma actE_actE_inv (g : Ginf F) (y : Coord F) : actE g (actE g⁻¹ y) = y := by
  have := actE_inv_actE g⁻¹ y
  rwa [inv_inv] at this

theorem isoHalf_actE (g : Ginf F) : IsoHalf (actE g) := by
  choose φ hφ hg using fun w => mem_iso1 (g w)
  have : actE g = fun (y : Coord F) w => φ w (y w) := by
    funext y w
    change chart1.symm (g w • chart1 (y w)) = _
    rw [hg w, Homeomorph.symm_apply_apply]
  rw [this]
  exact isoHalf_pi hφ

theorem measurePreserving_actE (g : Ginf F) : MeasurePreserving (actE g) (muE F) (muE F) := by
  have h1 := measurePreserving_chart F
  have h2 := measurePreserving_Ginf_smul g
  have h3 : MeasurePreserving (chart F).symm (X.vol F) (muE F) :=
    h1.symm (chart F).toMeasurableEquiv
  exact h3.comp (h2.comp h1)

theorem lapE_actE (g : Ginf F) {U : Coord F → ℂ} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (y : Coord F) :
    lapE (fun z => U (actE g z)) y = lapE U (actE g y) :=
  lapE_comp_of_iso (isoHalf_actE g) (isoHalf_actE g⁻¹) (actE_actE_inv g) (actE_inv_actE g)
    (measurePreserving_actE g) hU y

/-! ### Calculus on `X` -/

lemma X.Smooth.comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) :
    X.Smooth fun P => u (g • P) := by
  unfold X.Smooth
  have : (fun y => u (g • chart F y)) = fun y => (fun z => u (chart F z)) (actE g y) := by
    funext y; simp only [chart_actE]
  rw [this]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  exact hu'.comp (isoHalf_actE g).smooth

/-- **The Laplacian commutes with `G∞`.** -/
theorem X.lap_comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) (P : X F) :
    X.lap (fun P => u (g • P)) P = X.lap u (g • P) := by
  unfold X.lap
  have : (fun y => u (g • chart F y)) = fun y => (fun z => u (chart F z)) (actE g y) := by
    funext y; simp only [chart_actE]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  rw [this, lapE_actE g hu']
  congr 1
  simp [actE]

/-- **The carré du champ is invariant under `G∞`.** -/
theorem X.gam_comp_Ginf {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) (g : Ginf F)
    (P : X F) : X.gam (fun P => u (g • P)) (fun P => w (g • P)) P = X.gam u w (g • P) := by
  unfold X.gam
  have h1 : ∀ v : X F → ℂ,
      (fun y => v (g • chart F y)) = fun y => (fun z => v (chart F z)) (actE g y) := by
    intro v; funext y; simp only [chart_actE]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  have hw' : ContDiff ℝ (⊤ : ℕ∞) fun y => w (chart F y) := hw
  rw [h1 u, h1 w, (isoHalf_actE g).gam_comp _ _ _ ((hu'.differentiable (by simp)) _)
    ((hw'.differentiable (by simp)) _)]
  congr 1
  simp [actE]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

/-- **A compact set of `X` meets only finitely many `SL(2,𝓞_F)`-translates of itself.** -/
theorem finite_return_of_isCompact {K : Set (X F)} (hK : IsCompact K) :
    {γ : SL(2, 𝓞 F) | ∃ P ∈ K, γ • P ∈ K}.Finite := by
  obtain ⟨n, hn⟩ := X.exists_box_of_isCompact hK
  exact (finite_return_box n).subset fun γ ⟨P, hP, hγP⟩ => ⟨P, hn hP, hn hγP⟩

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_QuotC
/-! # WP-X, file 8: unfolding for complex-valued functions (absolutely convergent case)

Complex versions of the Tonelli lemmas of `X_Quot`, under an absolute-integrability hypothesis
stated as finiteness of a lower integral.  Weights are the real numbers `(η a).toReal`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma IsPOU.le_one {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≤ 1 := by
  have h := ENNReal.le_tsum (f := fun g : G => η (g • a)) 1
  rwa [one_smul, hη.tsum_eq] at h

lemma IsPOU.ne_top {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≠ ⊤ :=
  ((hη.le_one a).trans_lt ENNReal.one_lt_top).ne

lemma IsPOU.enorm_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ‖(((η a).toReal : ℝ) : ℂ)‖ₑ = η a := by
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
  exact Real.enorm_toReal (hη.ne_top a)

lemma IsPOU.tsum_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ∑' g : G, (((η (g • a)).toReal : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq (fun g => hη.ne_top _), hη.tsum_eq]
  simp

lemma IsPOU.measurable_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    Measurable fun a => (((η a).toReal : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hη.measurable.ennreal_toReal

/-- **Complex Tonelli swap**: `∫ φ · Σ_g ψ(g a) = ∫ ψ · Σ_g φ(g a)` when
`∫ |φ| Σ_g |ψ(g a)| < ∞`. -/
theorem integral_tsum_swap {φ ψ : α → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hfin : ∫⁻ a, ‖φ a‖ₑ * ∑' g : G, ‖ψ (g • a)‖ₑ ∂μ ≠ ⊤) :
    ∫ a, φ a * ∑' g : G, ψ (g • a) ∂μ = ∫ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  have h1 : ∑' g : G, ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ ≠ ⊤ := by
    have : ∑' g : G, ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ = ∫⁻ a, ‖φ a‖ₑ * ∑' g : G, ‖ψ (g • a)‖ₑ ∂μ := by
      simp_rw [enorm_mul, ← ENNReal.tsum_mul_left]
      exact (lintegral_tsum fun g =>
        (hφ.enorm.mul (hψ.comp (hm g)).enorm).aemeasurable).symm
    rwa [this]
  have h2 : ∀ g : G, ∫⁻ a, ‖ψ a * φ (g⁻¹ • a)‖ₑ ∂μ = ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ := by
    intro g
    have hF : Measurable fun a => ‖ψ a * φ (g⁻¹ • a)‖ₑ := (hψ.mul (hφ.comp (hm g⁻¹))).enorm
    rw [← lintegral_comp_smul (μ := μ) g hF]
    refine lintegral_congr fun a => ?_
    simp [mul_comm]
  calc ∫ a, φ a * ∑' g : G, ψ (g • a) ∂μ
      = ∫ a, ∑' g : G, φ a * ψ (g • a) ∂μ := by simp_rw [tsum_mul_left]
    _ = ∑' g : G, ∫ a, φ a * ψ (g • a) ∂μ :=
        integral_tsum (f := fun (g : G) a => φ a * ψ (g • a))
          (fun g => (hφ.mul (hψ.comp (hm g))).aestronglyMeasurable) h1
    _ = ∑' g : G, ∫ a, ψ a * φ (g⁻¹ • a) ∂μ := by
        refine tsum_congr fun g => ?_
        rw [← integral_smul_eq_self (μ := μ) (fun a => ψ a * φ (g⁻¹ • a)) (g := g)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        change φ a * ψ (g • a) = ψ (g • a) * φ (g⁻¹ • g • a)
        rw [inv_smul_smul, mul_comm]
    _ = ∫ a, ∑' g : G, ψ a * φ (g⁻¹ • a) ∂μ :=
        (integral_tsum (f := fun (g : G) a => ψ a * φ (g⁻¹ • a))
          (fun g => (hψ.mul (hφ.comp (hm g⁻¹))).aestronglyMeasurable)
          (by simp_rw [h2]; exact h1)).symm
    _ = ∫ a, ψ a * ∑' g : G, φ (g⁻¹ • a) ∂μ := by simp_rw [tsum_mul_left]
    _ = ∫ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        change ψ a * _ = ψ a * _
        congr 1
        exact (Equiv.inv G).tsum_eq (fun g : G => φ (g • a))

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
/-! # WP-X2, file 4: Green's identity on `X` and averaging over `Γ`

* `X.green`: `∫_X φ Δu = ∫_X Γ(φ, u)` when `φ` or `u` has compact support;
* `X.avg Γ φ = ∑_{γ ∈ Γ} φ ∘ γ` for compactly supported `φ`: locally finite, smooth,
  `Δ (avg φ) = avg (Δ φ)`, `Γ(avg φ, u) = avg Γ(φ, u)` for `Γ`-invariant `u`;
* unfolding `∫ η · avg φ · g = ∫_X φ g` for invariant `g` (`integral_avg_mul`);
* **Green's identity on `Γ \ X`** for `w = avg φ` and any smooth invariant `u`
  (`X.qgreen`, `X.qgreen'`): `∫ η w Δu = ∫ η Γ(w, u) = ∫ η u Δw`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### Measure-theoretic instances -/

/-! ### Calculus on `X`: basic rules -/

lemma X.lap_chart (u : X F → ℂ) (y : Coord F) :
    X.lap u (chart F y) = lapE (fun z => u (chart F z)) y := by
  simp [X.lap]

lemma X.gam_chart (u w : X F → ℂ) (y : Coord F) :
    X.gam u w (chart F y) = gamE (fun z => u (chart F z)) (fun z => w (chart F z)) y := by
  simp [X.gam]

lemma X.Smooth.lap {u : X F → ℂ} (hu : X.Smooth u) : X.Smooth (X.lap u) := by
  unfold X.Smooth
  simp_rw [X.lap_chart]
  exact contDiff_lapE hu

lemma X.Smooth.gam {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) :
    X.Smooth (X.gam u w) := by
  unfold X.Smooth
  simp_rw [X.gam_chart]
  exact contDiff_gamE hu hw

lemma X.Smooth.conj {u : X F → ℂ} (hu : X.Smooth u) : X.Smooth fun P => conj (u P) :=
  Complex.conjCLE.contDiff.comp hu.contDiff

lemma eventuallyEq_chart {β : Type*} {u w : X F → β} {P : X F} (h : u =ᶠ[𝓝 P] w) :
    (fun y => u (chart F y)) =ᶠ[𝓝 ((chart F).symm P)] fun y => w (chart F y) := by
  have ht : Tendsto (chart F) (𝓝 ((chart F).symm P)) (𝓝 P) := by
    have := (chart F).continuous.continuousAt (x := (chart F).symm P)
    rwa [ContinuousAt, Homeomorph.apply_symm_apply] at this
  exact ht.eventually h

lemma X.lap_congr {u w : X F → ℂ} {P : X F} (h : u =ᶠ[𝓝 P] w) : X.lap u P = X.lap w P :=
  lapE_congr (eventuallyEq_chart h)

lemma X.gam_congr {u u' w w' : X F → ℂ} {P : X F} (h : u =ᶠ[𝓝 P] u') (h' : w =ᶠ[𝓝 P] w') :
    X.gam u w P = X.gam u' w' P :=
  gamE_congr (eventuallyEq_chart h) (eventuallyEq_chart h')

lemma lapE_zero (y : Coord F) : lapE (fun _ : Coord F => (0 : ℂ)) y = 0 := by
  simp [lapE, pd_const']

lemma gamE_zero_left (W : Coord F → ℂ) (y : Coord F) : gamE (fun _ : Coord F => (0 : ℂ)) W y = 0 := by
  simp [gamE, pd_const']

lemma X.lap_eq_zero_of_notMem_tsupport {u : X F → ℂ} {P : X F} (hP : P ∉ tsupport u) :
    X.lap u P = 0 := by
  have h : u =ᶠ[𝓝 P] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hP
  rw [X.lap_congr h]
  exact lapE_zero _

lemma X.gam_eq_zero_of_notMem_tsupport {u : X F → ℂ} (w : X F → ℂ) {P : X F}
    (hP : P ∉ tsupport u) : X.gam u w P = 0 := by
  have h : u =ᶠ[𝓝 P] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hP
  rw [X.gam_congr h (Filter.EventuallyEq.refl _ w)]
  exact gamE_zero_left _ _

lemma X.hasCompactSupport_lap {u : X F → ℂ} (hc : HasCompactSupport u) :
    HasCompactSupport (X.lap u) :=
  hc.mono' fun P hP => by
    by_contra h
    exact hP (X.lap_eq_zero_of_notMem_tsupport h)

lemma X.hasCompactSupport_gam {u : X F → ℂ} (w : X F → ℂ) (hc : HasCompactSupport u) :
    HasCompactSupport (X.gam u w) :=
  hc.mono' fun P hP => by
    by_contra h
    exact hP (X.gam_eq_zero_of_notMem_tsupport w h)

lemma X.gam_comm (u w : X F → ℂ) : X.gam u w = X.gam w u := by
  funext P
  unfold X.gam
  rw [gamE_comm]

lemma X.lap_conj (u : X F → ℂ) (P : X F) : X.lap (fun P => conj (u P)) P = conj (X.lap u P) :=
  lapE_conj _ _

lemma one_le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top

lemma X.Smooth.differentiable {u : X F → ℂ} (hu : X.Smooth u) :
    Differentiable ℝ fun y => u (chart F y) := hu.contDiff.differentiable (by simp)

/-- **Green's identity on `X`.** -/
theorem X.green {u φ : X F → ℂ} (hu : X.Smooth u) (hφ : X.Smooth φ)
    (hc : HasCompactSupport φ ∨ HasCompactSupport u) :
    ∫ P, φ P * X.lap u P ∂X.vol F = ∫ P, X.gam φ u P ∂X.vol F := by
  rw [integral_vol_eq, integral_vol_eq]
  simp_rw [X.lap_chart, X.gam_chart]
  refine green_E (hu.contDiff.of_le two_le_top) (hφ.contDiff.of_le one_le_top) ?_
  exact hc.imp (fun h => h.comp_isClosedEmbedding (chart F).isClosedEmbedding)
    (fun h => h.comp_isClosedEmbedding (chart F).isClosedEmbedding)

/-! ### Invariance -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

lemma X.IsInv.lap {u : X F → ℂ} (hinv : X.IsInv Γ u) (hu : X.Smooth u) : X.IsInv Γ (X.lap u) := by
  intro γ P
  have h := X.lap_comp_Ginf hu (gin (γ : SL(2, 𝓞 F))) P
  have h2 : (fun P => u (gin (γ : SL(2, 𝓞 F)) • P)) = u := funext fun Q => hinv γ Q
  rw [h2] at h
  exact h.symm

/-! ### Local finiteness and averaging -/

/-- Near any point, only finitely many `γ ∈ Γ` move points into a given compact set. -/
theorem exists_finset_nhds (Γ : Subgroup (SL(2, 𝓞 F))) {K : Set (X F)} (hK : IsCompact K)
    (P₀ : X F) : ∃ R : Finset Γ, ∃ N ∈ 𝓝 P₀, ∀ P ∈ N, ∀ γ : Γ, γ • P ∈ K → γ ∈ R := by
  set C : Set (X F) := (chart F).symm ⁻¹' Metric.closedBall ((chart F).symm P₀) 1 with hC
  have hCc : IsCompact C := (chart F).symm.isCompact_preimage.2 (isCompact_closedBall _ _)
  have hCn : C ∈ 𝓝 P₀ :=
    (chart F).symm.continuous.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ one_pos)
  have hfin := finite_return_of_isCompact (hCc.union hK)
  have hfin' : {γ : Γ | ∃ P ∈ C ∪ K, γ • P ∈ C ∪ K}.Finite :=
    hfin.preimage (f := fun γ : Γ => (γ : SL(2, 𝓞 F))) Subtype.val_injective.injOn
  exact ⟨hfin'.toFinset, C, hCn, fun P hP γ hγ =>
    hfin'.mem_toFinset.mpr ⟨P, Or.inl hP, Or.inr hγ⟩⟩

lemma exists_finset_avg (Γ : Subgroup (SL(2, 𝓞 F))) {φ : X F → ℂ} (hc : HasCompactSupport φ)
    (P₀ : X F) : ∃ R : Finset Γ, ∃ N ∈ 𝓝 P₀, ∀ P ∈ N, ∀ γ : Γ, γ ∉ R → γ • P ∉ tsupport φ := by
  obtain ⟨R, N, hN, h⟩ := exists_finset_nhds Γ hc P₀
  exact ⟨R, N, hN, fun P hP γ hγ hmem => hγ (h P hP γ hmem)⟩

lemma X.avg_eventuallyEq (Γ : Subgroup (SL(2, 𝓞 F))) {φ : X F → ℂ} (hc : HasCompactSupport φ)
    (P₀ : X F) : ∃ R : Finset Γ, (∀ γ : Γ, γ ∉ R → γ • P₀ ∉ tsupport φ) ∧
      X.avg Γ φ =ᶠ[𝓝 P₀] fun P => ∑ γ ∈ R, φ (γ • P) := by
  obtain ⟨R, N, hN, h⟩ := exists_finset_avg Γ hc P₀
  refine ⟨R, h P₀ (mem_of_mem_nhds hN), ?_⟩
  filter_upwards [hN] with P hP
  exact tsum_eq_sum fun γ hγ => image_eq_zero_of_notMem_tsupport (h P hP γ hγ)

lemma X.Smooth.comp_gamma {φ : X F → ℂ} (hφ : X.Smooth φ) (γ : Γ) :
    X.Smooth fun P => φ (γ • P) := hφ.comp_Ginf (gin (γ : SL(2, 𝓞 F)))

/-- `Δ (∑_γ φ ∘ γ) = ∑_γ (Δ φ) ∘ γ`. -/
theorem X.lap_avg {φ : X F → ℂ} (hφ : X.Smooth φ) (hc : HasCompactSupport φ) (P : X F) :
    X.lap (X.avg Γ φ) P = X.avg Γ (X.lap φ) P := by
  obtain ⟨R, hR0, hR⟩ := X.avg_eventuallyEq Γ hc P
  rw [X.lap_congr hR]
  have h1 : X.lap (fun P => ∑ γ ∈ R, φ (γ • P)) P = ∑ γ ∈ R, X.lap (fun P => φ (γ • P)) P := by
    unfold X.lap
    exact lapE_sum R (fun γ _ => (hφ.comp_gamma γ).contDiff.of_le two_le_top) _
  rw [h1]
  unfold X.avg
  rw [tsum_eq_sum (s := R) fun γ hγ => X.lap_eq_zero_of_notMem_tsupport (hR0 γ hγ)]
  exact Finset.sum_congr rfl fun γ _ => X.lap_comp_Ginf hφ (gin (γ : SL(2, 𝓞 F))) P

/-- `Γ(∑_γ φ ∘ γ, u) = ∑_γ Γ(φ, u) ∘ γ` for `Γ`-invariant `u`. -/
theorem X.gam_avg {φ u : X F → ℂ} (hφ : X.Smooth φ) (hc : HasCompactSupport φ)
    (hu : X.Smooth u) (hinv : X.IsInv Γ u) (P : X F) :
    X.gam (X.avg Γ φ) u P = X.avg Γ (X.gam φ u) P := by
  obtain ⟨R, hR0, hR⟩ := X.avg_eventuallyEq Γ hc P
  rw [X.gam_congr hR (Filter.EventuallyEq.refl _ u)]
  have h1 : X.gam (fun P => ∑ γ ∈ R, φ (γ • P)) u P =
      ∑ γ ∈ R, X.gam (fun P => φ (γ • P)) u P := by
    unfold X.gam
    exact gamE_sum_left R (fun γ _ => (hφ.comp_gamma γ).differentiable _)
  rw [h1]
  unfold X.avg
  rw [tsum_eq_sum (s := R) fun γ hγ => X.gam_eq_zero_of_notMem_tsupport u (hR0 γ hγ)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have h2 := X.gam_comp_Ginf hφ hu (gin (γ : SL(2, 𝓞 F))) P
  have h3 : (fun P => u (gin (γ : SL(2, 𝓞 F)) • P)) = u := funext fun Q => hinv γ Q
  rw [h3] at h2
  exact h2

/-! ### Unfolding -/

/-- **Unfolding**: `∫ η · (∑_γ φ ∘ γ) · g = ∫_X φ g` for `Γ`-invariant `g`. -/
theorem integral_avg_mul {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) {φ g : X F → ℂ}
    (hφ : Measurable φ) (hg : Measurable g) (hinv : X.IsInv Γ g)
    (hfin : ∫⁻ P, ‖φ P * g P‖ₑ ∂X.vol F ≠ ⊤) :
    ∫ P, (((η P).toReal : ℝ) : ℂ) * (X.avg Γ φ P * g P) ∂X.vol F = ∫ P, φ P * g P ∂X.vol F := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have h := integral_tsum_swap (G := Γ) (μ := X.vol F) (φ := fun P => φ P * g P)
    (ψ := fun P => (((η P).toReal : ℝ) : ℂ)) (hφ.mul hg) hη.measurable_toReal (by
      simp_rw [hη.enorm_toReal, hη.tsum_eq, mul_one]
      exact hfin)
  simp only [hη.tsum_toReal, mul_one] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [X.avg, hinv _ P]
  rw [tsum_mul_right]

/-! ### Green's identity on the quotient -/

/-- **Green's identity on `Γ \ X`**, first form: for `w = ∑_γ φ ∘ γ`, `φ ∈ C_c^∞(X)`, and `u`
smooth and `Γ`-invariant, `∫ η w Δu = ∫ η Γ(w, u)`. -/
theorem X.qgreen {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) {φ u : X F → ℂ} (hφ : X.Smooth φ)
    (hc : HasCompactSupport φ) (hu : X.Smooth u) (hinv : X.IsInv Γ u) :
    ∫ P, (((η P).toReal : ℝ) : ℂ) * (X.avg Γ φ P * X.lap u P) ∂X.vol F =
      ∫ P, (((η P).toReal : ℝ) : ℂ) * X.gam (X.avg Γ φ) u P ∂X.vol F := by
  rw [integral_avg_mul hη hφ.continuous.measurable hu.lap.continuous.measurable (hinv.lap hu)
    (lintegral_ne_top_of_continuous (hφ.continuous.mul hu.lap.continuous) hc.mul_right),
    X.green hu hφ (Or.inl hc)]
  have h := integral_avg_mul hη (hφ.gam hu).continuous.measurable
    (measurable_const (a := (1 : ℂ))) (fun _ _ => rfl) (by
      simp only [mul_one]
      exact lintegral_ne_top_of_continuous (hφ.gam hu).continuous (X.hasCompactSupport_gam u hc))
  simp only [mul_one] at h
  rw [← h]
  simp_rw [X.gam_avg hφ hc hu hinv]

/-- **Green's identity on `Γ \ X`**, second form: `∫ η u Δw = ∫ η Γ(w, u)`. -/
theorem X.qgreen' {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) {φ u : X F → ℂ} (hφ : X.Smooth φ)
    (hc : HasCompactSupport φ) (hu : X.Smooth u) (hinv : X.IsInv Γ u) :
    ∫ P, (((η P).toReal : ℝ) : ℂ) * (u P * X.lap (X.avg Γ φ) P) ∂X.vol F =
      ∫ P, (((η P).toReal : ℝ) : ℂ) * X.gam (X.avg Γ φ) u P ∂X.vol F := by
  have h1 := integral_avg_mul hη hφ.lap.continuous.measurable hu.continuous.measurable hinv
    (lintegral_ne_top_of_continuous (hφ.lap.continuous.mul hu.continuous)
      (X.hasCompactSupport_lap hc).mul_right)
  have h2 : ∫ P, X.lap φ P * u P ∂X.vol F = ∫ P, X.gam φ u P ∂X.vol F := by
    have := X.green hφ hu (Or.inr hc)
    rw [X.gam_comm u φ] at this
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun P => mul_comm _ _)
  have h := integral_avg_mul hη (hφ.gam hu).continuous.measurable
    (measurable_const (a := (1 : ℂ))) (fun _ _ => rfl) (by
      simp only [mul_one]
      exact lintegral_ne_top_of_continuous (hφ.gam hu).continuous (X.hasCompactSupport_gam u hc))
  simp only [mul_one] at h
  simp_rw [X.gam_avg hφ hc hu hinv]
  rw [h, ← h2, ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [X.lap_avg hφ hc]
  ring

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

/-- The pull-back of the class of `f` is `f` almost everywhere. -/
lemma X.lift_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) : X.lift Γ (X.toL2 Γ f h) =ᵐ[X.vol F] f := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have h1 := liftQ_ae_eq (X.isPOU_pou Γ) (MemLp.coeFn_toLp h.memLp)
  refine h1.trans (Filter.Eventually.of_forall fun P => ?_)
  exact X.desc_mk h.inv P

lemma X.integral_quotVol {h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ} (hh : Measurable h) :
    ∫ q, h q ∂X.quotVol Γ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * h (Quotient.mk _ P) ∂X.vol F := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  unfold X.quotVol quotMeasure
  rw [integral_map measurable_mk.aemeasurable hh.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (X.isPOU_pou Γ).measurable
      (Filter.Eventually.of_forall fun P => ((X.isPOU_pou Γ).ne_top P).lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [Complex.real_smul]

/-- Inner products with a class are integrals against the partition of unity. -/
theorem X.inner_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) (v : X.L2 Γ) :
    ⟪X.toL2 Γ f h, v⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (f P) * X.lift Γ v P) ∂X.vol F := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun q => ⟪(X.toL2 Γ f h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ) q, v q⟫_ℂ)
      =ᵐ[X.quotVol Γ] fun q => conj (X.desc Γ f q) * v q := by
    filter_upwards [MemLp.coeFn_toLp h.memLp] with q hq
    rw [show (X.toL2 Γ f h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ) q = X.desc Γ f q from hq]
    simp [mul_comm]
  have hm : Measurable fun q : Quotient (MulAction.orbitRel Γ (X F)) =>
      conj (X.desc Γ f q) * v q :=
    (Complex.continuous_conj.measurable.comp (X.measurable_desc h.meas h.inv)).mul
      (Lp.stronglyMeasurable v).measurable
  rw [integral_congr_ae h1, X.integral_quotVol hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [X.desc_mk h.inv]
  rfl

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

lemma X.avg_conj (φ : X F → ℂ) (P : X F) :
    X.avg Γ (fun P => conj (φ P)) P = conj (X.avg Γ φ P) := by
  unfold X.avg
  rw [Complex.conj_tsum]

lemma X.conj_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : (fun P => conj (w P)) ∈ X.core Γ := by
  obtain ⟨φ, hφ, hc, rfl⟩ := hw
  refine ⟨fun P => conj (φ P), hφ.conj, hc.comp_left (map_zero _), ?_⟩
  funext P
  exact (X.avg_conj φ P).symm

variable (Γ)

variable {Γ}

lemma X.coreLap_coe (w : X.core Γ) : ((X.coreLap Γ w : X.core Γ) : X F → ℂ) = X.lap w := rfl

lemma X.lift_coreL2 (w : X.core Γ) : X.lift Γ (X.coreL2 Γ w) =ᵐ[X.vol F] w :=
  X.lift_toL2 (X.l2Rep_of_mem_core w.2)

/-- `⟪a, v⟫ = ∫ η conj(a) v` for a core function `a`. -/
lemma X.inner_coreL2 (a : X.core Γ) (v : X.L2 Γ) :
    ⟪X.coreL2 Γ a, v⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj ((a : X F → ℂ) P) * X.lift Γ v P) ∂X.vol F :=
  X.inner_toL2 (X.l2Rep_of_mem_core a.2) v

/-- **Weak form of the Laplacian on the core**: `⟪Δa, u⟫ = ∫ η conj(a) Δu` for `a` in the core
and `u` smooth, `Γ`-invariant, with `uL` the class of `u`. -/
theorem X.inner_coreLap_eq (a : X.core Γ) {u : X F → ℂ} (hu : X.Smooth u) (hinv : X.IsInv Γ u)
    (uL : X.L2 Γ) (huL : X.lift Γ uL =ᵐ[X.vol F] u) :
    ⟪X.coreL2 Γ (X.coreLap Γ a), uL⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj ((a : X F → ℂ) P) * X.lap u P) ∂X.vol F := by
  obtain ⟨φ, hφ, hc, ha⟩ := X.conj_mem_core a.2
  rw [X.inner_coreL2]
  have h1 : (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) *
      (conj (((X.coreLap Γ a : X.core Γ) : X F → ℂ) P) * X.lift Γ uL P)) =ᵐ[X.vol F]
      fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * (u P * X.lap (X.avg Γ φ) P) := by
    filter_upwards [huL] with P hP
    rw [hP, X.coreLap_coe, ← ha, X.lap_conj]
    ring
  rw [integral_congr_ae h1, X.qgreen' (X.isPOU_pou Γ) hφ hc hu hinv,
    ← X.qgreen (X.isPOU_pou Γ) hφ hc hu hinv, ← ha]

theorem X.inner_coreLap_coreL2_oai (a b : X.core Γ) :
    ⟪X.coreL2 Γ (X.coreLap Γ a), X.coreL2 Γ b⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) *
        X.gam (fun P => conj ((a : X F → ℂ) P)) b P ∂X.vol F := by
  obtain ⟨φ, hφ, hc, ha⟩ := X.conj_mem_core a.2
  have ha' : ∀ P, conj ((a : X F → ℂ) P) = X.avg Γ φ P := congrFun ha
  rw [X.inner_coreLap_eq a (X.smooth_of_mem_core b.2) (X.isInv_of_mem_core b.2) _
    (X.lift_coreL2 b), ha]
  simp_rw [ha']
  rw [X.qgreen (X.isPOU_pou Γ) hφ hc (X.smooth_of_mem_core b.2) (X.isInv_of_mem_core b.2)]

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.inner_coreLap_coreL2_oai.{u_1} := @ArtinKP.X.X.inner_coreLap_coreL2_oai.{u_1}
