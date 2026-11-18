-- Prove2me | solution 1 for ArtinKP.GK.tau_eq_zero_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:01:04.799425+00:00
-- url     : https://prove2.me/submissions/2e977b37-1248-451d-bffe-1420c4bb8836

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_T_hasSeed
import Theorems.Thm_ArtinKP_T_integral_theta_of_hasCoef
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 9: `G ∈ L¹ ∩ L²(Γ\X)`, and compactness of the truncated space at the cusp `∞`

* `measurable_G`; `lintegral_G_pow_lt_top`: `∫_{Γ\X} G^k dμ < ∞` (in the partition-of-unity form of
  WP-X) for every `k`, from the boundedness of `G` and **finite volume of `Γ\X`** (hypothesis `hvol`).
* `H3.isCompact_box`, `X.isCompact_box`.
* `exists_reduced`: every point of `X` is `Γ_∞`-equivalent (`Γ_∞ ⊂ SL₂(𝓞_F)` upper triangular) to a point
  with `x` in the fundamental cell and balanced `v`; `siegel S' T` is compact; hence
  `subset_orbit_siegel`: the points whose top class is in the `SL₂(𝓞_F)`-orbit of `∞` and whose top
  height is in `[c, T]` lie in `SL₂(𝓞_F) · (compact)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Compactness of the truncated space at the cusp `∞` (item 5) -/

omit [NumberField F] [IsTotallyComplex F] in
lemma H3.isCompact_box {m M B : ℝ} (hm : 0 < m) : IsCompact (H3.box m M B) := by
  have hind : Topology.IsInducing (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) :=
    Topology.IsInducing.subtypeVal
  have himg : (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) '' (H3.box m M B) =
      Metric.closedBall (0 : ℂ) B ×ˢ Set.Icc m M := by
    ext ⟨z, t⟩
    constructor
    · rintro ⟨Q, ⟨h1, h2, h3⟩, hQ⟩
      have hz : H3.x Q = z := congrArg Prod.fst hQ
      have ht : H3.v Q = t := congrArg Prod.snd hQ
      rw [hz] at h1
      rw [ht] at h2 h3
      exact ⟨by simpa using h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' : ‖z‖ ≤ B := by simpa using h1
      exact ⟨⟨(z, t), lt_of_lt_of_le hm h2⟩, ⟨h1', h2, h3⟩, rfl⟩
  exact hind.isCompact_iff.mpr (himg ▸ (isCompact_closedBall 0 B).prod isCompact_Icc)

omit [IsTotallyComplex F] in
theorem isCompact_siegelBox {m M B : ℝ} (hm : 0 < m) : IsCompact (siegelBox F m M B) := by
  have : siegelBox F m M B = Set.pi Set.univ fun _ : InfinitePlace F => H3.box m M B := by
    ext P; simp [siegelBox]
  rw [this]
  exact isCompact_univ_pi fun _ => H3.isCompact_box hm

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

theorem continuous_archChar : Continuous archChar := by
  unfold archChar; fun_prop

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

lemma continuous_hyperbolicKernel (s : ℂ) : Continuous (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  apply Continuous.cpow
  · fun_prop
  · exact continuous_const
  · intro z
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, archChar_zero, mul_one]
    using integral_hyperbolicKernel s hs

/-! ## The Bessel form (ours, for `besselK`) -/

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

/-! ## The Jacquet integral -/

lemma height_cpow (s : ℂ) {v : ℝ} (hv : 0 < v) (x : ℂ) :
    ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) * hyperbolicKernel s (x / (v : ℂ)) := by
  unfold hyperbolicKernel
  have h1 : (v / (‖x‖ ^ 2 + v ^ 2) : ℝ) = v⁻¹ * (1 + ‖x / (v : ℂ)‖ ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + ‖x / (v : ℂ)‖ ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hv.le)
    (inv_nonneg.2 hpos.le), Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hv.le, Complex.inv_cpow_ofReal_nonneg hpos.le,
    Complex.cpow_neg, Complex.cpow_neg]

theorem jacquet_eq_sourceFourierKernel (s ν : ℂ) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (v : ℂ) ^ (2 - s) * sourceFourierKernel s (ν * v) := by
  unfold jacquet
  simp_rw [height_cpow s hv, mul_assoc]
  rw [integral_const_mul, traceIntegral_scale v hv s ν, ← mul_assoc]
  congr 1
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
  congr 1
  push_cast; ring

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma chart_x (y : Coord F) (w : InfinitePlace F) : (chart F y).x w = (y w).1 := rfl
lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

lemma coeFn_restrictL2 (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B) {m : ℝ≥0∞}
    (hmtop : m ≠ ⊤) (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m)
    (u : Lp ℂ 2 (quotMeasure G η μ)) :
    restrictL2 hη hB hmtop hm u =ᵐ[μ.restrict B] liftQ u :=
  MemLp.coeFn_toLp (memLp_liftQ_restrict hη hB hmtop hm u)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.coeFn_restrictBox (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    X.restrictBox Γ n u =ᵐ[(X.vol F).restrict (X.box n)] X.lift Γ u :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  coeFn_restrictL2 _ _ _ _ u

lemma X.coeFn_boxLp (n : ℕ) (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) :
    X.boxLp n ψ hψ C hC =ᵐ[(X.vol F).restrict (X.box n)] ψ :=
  MemLp.coeFn_toLp _

theorem X.coeffFunctional_apply (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (ψ : X F → ℂ)
    (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) (u : X.L2 Γ) :
    X.coeffFunctional Γ n ψ hψ C hC u = ∫ P in X.box n, conj (ψ P) * X.lift Γ u P ∂X.vol F := by
  unfold X.coeffFunctional
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [X.coeFn_restrictBox Γ n u, X.coeFn_boxLp n ψ hψ C hC] with P h1 h2
  rw [h1, h2]
  simp [mul_comm]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-X2, file 9: product coordinates `(x, v)` on `X` (stub S3 of WP-X)

`X.measurePreserving_xv`: the map `P ↦ (P.x, P.v) : X F → (ι → ℂ) × (ι → ℝ)` carries `X.vol F`
to `volume.prod (X.nuV F)`, `X.nuV F = ∏_w dv_w / v_w³` on `(0,∞)^ι`.  Hence integrals over `X`
and over strips `{x ∈ D}` are iterated integrals (`X.lintegral_xv`, `X.setLIntegral_strip`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

lemma amb_eq_prod : amb = (volume : Measure ℂ).prod nu1 := by
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold nu1
  rw [prod_withDensity_right (by fun_prop), h2]
  rfl

lemma measurePreserving_coe : MeasurePreserving H3.coe H3.vol ((volume : Measure ℂ).prod nu1) :=
  ⟨H3.measurableEmbedding_coe.measurable, map_val_vol.trans amb_eq_prod⟩

variable (F : Type*) [Field F] [NumberField F]

lemma X.nuV_eq : X.nuV F =
    (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun v => ∏ w, ENNReal.ofReal ((v w ^ 3)⁻¹)) := by
  unfold X.nuV nu1
  exact pi_withDensity _ _ (fun _ => by fun_prop)

/-- **Product coordinates**: `P ↦ (x, v)` carries the invariant measure to
`dx ⊗ ∏_w dv_w / v_w³`. -/
theorem X.measurePreserving_xv :
    MeasurePreserving (fun P : X F => (P.x, P.v)) (X.vol F)
      ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
  have h2 : MeasurePreserving (fun (P : X F) w => H3.coe (P w)) (X.vol F)
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ).prod nu1) :=
    measurePreserving_pi (fun _ => H3.vol) (fun _ => (volume : Measure ℂ).prod nu1)
      (fun _ => measurePreserving_coe)
  have h3 := measurePreserving_arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
    (fun _ => (volume : Measure ℂ)) (fun _ => nu1)
  exact h3.comp h2

variable {F}

lemma X.measurable_xv : Measurable fun P : X F => (P.x, P.v) :=
  (X.measurePreserving_xv F).measurable

/-- Integrals over `X` in product coordinates. -/
theorem X.lintegral_xv {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ P, f (P.x, P.v) ∂X.vol F = ∫⁻ x, ∫⁻ v, f (x, v) ∂X.nuV F := by
  rw [← lintegral_prod _ hf.aemeasurable]
  exact (X.measurePreserving_xv F).lintegral_comp hf

/-- Integrals over a strip `{x ∈ D}` are iterated integrals `∫_D dx ∫ ∏ dv/v³`. -/
theorem X.setLIntegral_strip {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P in (X.x ⁻¹' D : Set (X F)), f (P.x, P.v) ∂X.vol F =
      ∫⁻ x in D, ∫⁻ v, f (x, v) ∂X.nuV F := by
  have hm : MeasurableSet (X.x ⁻¹' D : Set (X F)) :=
    (measurable_fst.comp X.measurable_xv) hD
  rw [← lintegral_indicator hm, ← lintegral_indicator hD]
  have h1 : ∀ P : X F, (X.x ⁻¹' D : Set (X F)).indicator (fun P => f (P.x, P.v)) P =
      (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
        D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p) (P.x, P.v) := by
    intro P
    by_cases h : P.x ∈ D
    · simp [h]
    · simp [h]
  simp_rw [h1]
  refine (X.lintegral_xv (f := fun p => D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p)
    (((measurable_const.indicator hD).comp measurable_fst).mul hf)).trans ?_
  refine lintegral_congr fun x => ?_
  by_cases h : x ∈ D
  · simp [h]
  · simp [h]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 3: Fourier uniqueness on a strip of `X` (core of stub S1 (b))

Product coordinates `P ↦ (x, v) : X F → XV F = (ι → ℂ) × (ι → ℝ)` carry `X.vol` to Lebesgue
measure with density `dens v = ∏_w v_w⁻³` on `v > 0` (`map_xv`).  For a basis `bV` of `ι → ℂ`
(the lattice basis of the translations) and `n : ℕ`, the box
`{x ∈ cell bV} × [1/(n+1), n+1]^ι` lies in the cell of the basis `bE bV n = bV ⊕ (n+2)·e_w` of
`XV F`, whose characters are `chi bV m x · phiK n k v`.  Hence (`RF_Torus.ae_eq_zero_of_coeff`):

`measure_ne_zero_null`: a function on `X`, square integrable on that box, all of whose
coefficients against `chi bV m (x) · phiK n k (v)` over the box vanish, is `0` a.e. on the box.
No Fubini and no slicing: the `v`-directions are treated as further circle directions.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The density of `X.vol` in product coordinates -/

lemma measurableSet_posSet : MeasurableSet (posSet F) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

lemma measurable_dens : Measurable (dens : (InfinitePlace F → ℝ) → ℝ≥0∞) := by
  unfold dens
  refine Measurable.indicator ?_ measurableSet_posSet
  exact Finset.measurable_prod _ fun w _ => by fun_prop

lemma nuV_eq_withDensity : X.nuV F = (volume : Measure (InfinitePlace F → ℝ)).withDensity dens := by
  rw [X.nuV_eq]
  have h1 : (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0))
      = (volume : Measure (InfinitePlace F → ℝ)).restrict (posSet F) :=
    (Measure.restrict_pi_pi (fun _ : InfinitePlace F => (volume : Measure ℝ))
      (fun _ => Ioi (0 : ℝ))).symm
  rw [h1, ← withDensity_indicator measurableSet_posSet]
  rfl

lemma measurable_ofXV : Measurable (ofXV : XV F → X F) := by
  refine (chart F).continuous.measurable.comp (measurable_pi_lambda _ fun w => ?_)
  exact ((measurable_pi_apply w).comp measurable_fst).prodMk
    (Real.measurable_log.comp ((measurable_pi_apply w).comp measurable_snd))

/-! ### Boxes in `v` -/

lemma vBox_subset_posSet (n : ℕ) : vBox F n ⊆ posSet F := fun v hv w _ =>
  lt_of_lt_of_le (by positivity) (hv w).1

lemma dens_ne_zero {n : ℕ} {v : InfinitePlace F → ℝ} (hv : v ∈ vBox F n) : dens v ≠ 0 := by
  unfold dens
  rw [indicator_of_mem (vBox_subset_posSet n hv)]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  have h0 : 0 < v w := vBox_subset_posSet n hv w (mem_univ w)
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-! ### The basis of `XV F` adapted to a box -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 4: Fourier series along `x` on `Γ\X` (stub S1 of WP-X)

Setting of WP-X "Remaining stubs": `F` totally complex, `Γ ≤ SL(2,𝓞_F)` containing the
translations `n(β)`, `β ∈ 𝔫`; `Λ = {GammaN.shift γ}` the translation lattice in `ι → ℂ`;

* `pair ν x = Σ_w Re(ν_w x_w)`, `eChar ν x = exp(2πi · pair ν x)`,
  `dualLat Γ = {ν | pair ν λ ∈ ℤ for all λ ∈ Λ}`;
* `stripFn D ν φ P = 1_D(P.x) · e_ν(P.x) · φ(P.v)`, the function `ψ` of
  `X.coeffFunctional Γ n ψ …` for the `(ν, φ)`-Fourier coefficient;
* `exists_latBasis`: a basis of `ι → ℂ` whose `ℤ`-span is `Λ`; the characters `chi bV m` of
  `RF_Torus` are the `eChar ν`, `ν ∈ dualLat Γ` (`exists_dual_of_chi`);
* **`eq_zero_of_coeff`** (S1 (b)): `u : X.L2 Γ` with all coefficient functionals zero is zero;
* `ae_eq_zero_of_strip`: the same for any measurable `GammaN Γ`-invariant function which is
  square integrable on boxes.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The pairing and the characters -/

/-! ### A basis of the translation lattice -/

lemma mem_box_iff (n : ℕ) (P : X F) :
    P ∈ (X.box n : Set (X F)) ↔ (∀ w, ‖P.x w‖ ≤ n) ∧ P.v ∈ vBox F n := by
  simp only [X.box, H3.box, vBox, mem_ofPred_eq, X.x, X.v]
  exact forall_and

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 2: the shape of the constant term of `E_Ψ` at `∞` for `Re s > 2` (MATH2 §2.1(b))

* `Cell Γ D n₀`: `D` is a measurable fundamental domain of the translation lattice of `Γ`, contained
  in `{‖x_w‖ ≤ n₀}`.  `Cell.of_hfund` converts from the form used by WP-X/WP-RF (`hfund`);
  `exists_cell` gives one for every `Γ` of finite index.
* `cf D n φ f = ∫_{box n} conj (1_D(x) φ(v)) f`: the constant-term functional (it is
  `X.coeffFunctional Γ n (RF.stripFn D 0 φ) …` on `L²(Γ\X)`, `coeffFunctional_eq_cf`).
* `mD D Ψ s = vol(D)⁻¹ ∫_D tail Ψ s (x, 1) dx`: the coefficient of `ht^{2−s}`.
* **`cf_eis`**: for `Re s > 2`, `n ≥ n₀`,
  `cf D n φ (E_Ψ(·,s)) = Ψ_s(0,1) · cf D n φ (ht^s) + mD D Ψ s · cf D n φ (ht^{2−s})`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Cells -/

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

section lin

variable {D : Set (InfinitePlace F → ℂ)} {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

lemma cf_integrable (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (stripFn D 0 φ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := 1) hf
    (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D 0 hφ1 P

end lin

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

lemma ofXV_eq_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ofXV (x, v) = X.mk x v hv := by
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · simp [ofXV, chart_x]
  · simp [ofXV, chart_v, Real.exp_log (hv w)]

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.T_Arch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-T, file 2: the archimedean Whittaker function as a function on `X`

`WX s ν P = Winf s ν P.v = ∏_w jacquet s (−σ_w ν) v_w`.  For `Re s > 1`:

* `continuous_WX`, `differentiableOn_WX` (in `s`, `ν ≠ 0`), `exists_norm_WX_le` (bounded on
  `ball × box`);
* **`exists_WX_ne_zero`**: for every `s₁` (complex!) there is `δ > 0` with `WX s₁ ν P ≠ 0` whenever
  all `v_w < δ`.  (The Jacquet integral is `v^{2−s}·ĝ_s(νv)` with `ĝ_s` continuous and
  `ĝ_s(0) = π/(s−1) ≠ 0`; no information on zeros of `K_μ` of complex order is needed.)
* `phaseW s₁ ν`, a measurable test function of `v` of modulus `≤ 1` with
  `conj (phaseW s₁ ν P.v) * WX s₁ ν P = ‖WX s₁ ν P‖`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### One place -/

theorem continuous_sFK {s : ℂ} (hs : 1 < s.re) : Continuous (sourceFourierKernel s) := by
  unfold sourceFourierKernel
  refine continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖) (fun ξ => ?_)
    (fun ξ => ?_) (hyperbolicKernel_integrable s hs).norm ?_
  · have hchar : Continuous (fun z : ℂ => archChar (-ξ * z)) :=
      K.continuous_archChar.comp (by fun_prop)
    exact ((continuous_hyperbolicKernel s).mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by rw [norm_mul, archChar_norm, mul_one]
  · exact Eventually.of_forall fun z =>
      continuous_const.mul (K.continuous_archChar.comp (by fun_prop))

theorem sFK_zero_ne {s : ℂ} (hs : 1 < s.re) : sourceFourierKernel s 0 ≠ 0 := by
  rw [sourceFourierKernel_zero s hs]
  refine div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) fun h => ?_
  have := congrArg Complex.re h
  simp at this
  linarith

/-- Near frequency `0` the kernel does not vanish. -/
theorem exists_sFK_ne_zero {s : ℂ} (hs : 1 < s.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ < ε → sourceFourierKernel s ξ ≠ 0 := by
  have h := (continuous_sFK hs).continuousAt.eventually_ne (sFK_zero_ne hs)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ε, hε, fun ξ hξ => hb (by simpa using hξ)⟩

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

lemma WX_eq (s : ℂ) (ν : F) (P : X F) :
    WX s ν P = ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := by
  unfold WX Winf
  exact Finset.prod_congr rfl fun w _ => jacquet_eq_sourceFourierKernel s _ (P.v_pos w)

theorem continuous_WX {s : ℂ} (hs : 1 < s.re) (ν : F) : Continuous (WX s ν : X F → ℂ) := by
  have e : (WX s ν : X F → ℂ) = fun P => ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := funext fun P => WX_eq s ν P
  rw [e]
  refine continuous_finsetProd _ fun w _ => ?_
  have hv : Continuous fun P : X F => ((P.v w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (X.continuous_v w)
  refine (hv.cpow continuous_const fun P => Or.inl ?_).mul
    ((continuous_sFK hs).comp (continuous_const.mul hv))
  simpa using P.v_pos w

/-- **Non-vanishing near the cusp**, for every complex `s₁` with `Re s₁ > 1`. -/
theorem exists_WX_ne_zero (ν : F) {s₁ : ℂ} (hs₁ : 1 < s₁.re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : X F, (∀ w, P.v w < δ) → WX s₁ ν P ≠ 0 := by
  obtain ⟨ε, hε, hne⟩ := exists_sFK_ne_zero hs₁
  set m : ℝ := ∑ w : InfinitePlace F, ‖w.embedding ν‖ with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun w _ => norm_nonneg _
  refine ⟨ε / (m + 1), by positivity, fun P hP => ?_⟩
  rw [WX_eq]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero ?_ (hne _ ?_)
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (P.v_pos w).ne')]
    exact Complex.exp_ne_zero _
  · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (P.v_pos w)]
    have h1 : ‖w.embedding ν‖ ≤ m :=
      Finset.single_le_sum (f := fun w : InfinitePlace F => ‖w.embedding ν‖)
        (fun w _ => norm_nonneg _) (Finset.mem_univ w)
    have h2 : P.v w < ε / (m + 1) := hP w
    calc ‖w.embedding ν‖ * P.v w ≤ m * P.v w :=
          mul_le_mul_of_nonneg_right h1 (P.v_pos w).le
      _ ≤ (m + 1) * P.v w := by nlinarith [P.v_pos w]
      _ < (m + 1) * (ε / (m + 1)) := mul_lt_mul_of_pos_left h2 (by positivity)
      _ = ε := by field_simp

/-! ### The phase test function -/

variable [IsTotallyComplex F]

lemma measurable_unitPhase : Measurable unitPhase :=
  measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)

lemma norm_unitPhase_le (z : ℂ) : ‖unitPhase z‖ ≤ 1 := by
  unfold unitPhase
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

lemma conj_unitPhase_mul (z : ℂ) : conj (unitPhase z) * z = ((‖z‖ : ℝ) : ℂ) := by
  unfold unitPhase
  by_cases hz : z = 0
  · simp [hz]
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
  field_simp

lemma measurable_phaseW {s₁ : ℂ} (hs₁ : 1 < s₁.re) (ν : F) :
    Measurable (phaseW (F := F) s₁ ν) :=
  measurable_unitPhase.comp ((continuous_WX hs₁ ν).measurable.comp
    (measurable_ofXV.comp (measurable_const.prodMk measurable_id)))

lemma norm_phaseW_le (s₁ : ℂ) (ν : F) (v : InfinitePlace F → ℝ) : ‖phaseW s₁ ν v‖ ≤ 1 :=
  norm_unitPhase_le _

lemma phaseW_v (s₁ : ℂ) (ν : F) (P : X F) : phaseW s₁ ν P.v = unitPhase (WX s₁ ν P) := by
  unfold phaseW
  have h : (ofXV ((0 : InfinitePlace F → ℂ), P.v)).v = P.v := by
    rw [ofXV_eq_mk 0 (fun w => P.v_pos w)]
    rfl
  unfold WX
  rw [h]

lemma conj_phaseW_mul (s₁ : ℂ) (ν : F) (P : X F) :
    conj (phaseW s₁ ν P.v) * WX s₁ ν P = ((‖WX s₁ ν P‖ : ℝ) : ℂ) := by
  rw [phaseW_v, conj_unitPhase_mul]

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The frequency of `ν` in WP-RF's parametrization -/

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {hG hz6 Φ ν}

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-- `nuV` of a small box near `v = 0` is positive. -/
lemma nuV_Icc_ne_zero {n : ℕ} {lo hi : ℝ} (hlo : 1 / ((n : ℝ) + 1) ≤ lo) (hlh : lo < hi)
    (hhi : hi ≤ (n : ℝ) + 1) :
    X.nuV F (Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi)) ≠ 0 := by
  have hsub : Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) ⊆ vBox F n := by
    intro v hv w
    exact ⟨hlo.trans (hv.1 w), (hv.2 w).trans hhi⟩
  rw [nuV_eq_withDensity, withDensity_apply _ measurableSet_Icc]
  intro h
  rw [lintegral_eq_zero_iff RF.measurable_dens] at h
  have h1 : ∀ᵐ v ∂(volume : Measure (InfinitePlace F → ℝ)),
      v ∉ Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) := by
    have h2 := (ae_restrict_iff' measurableSet_Icc).mp h
    filter_upwards [h2] with v hv hmem
    exact dens_ne_zero (hsub hmem) (hv hmem)
  have h3 := measure_eq_zero_iff_ae_notMem.mpr h1
  rw [Real.volume_Icc_pi] at h3
  exact (Finset.prod_ne_zero_iff.mpr fun w _ =>
    (ENNReal.ofReal_pos.mpr (by linarith)).ne') h3

/-- **A test function seeing `W_{s₁}(ν; ·)`**, for every complex `s₁` with `Re s₁ > 1`. -/
theorem exists_Wc_ne_zero (ν : F) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {D : Set (InfinitePlace F → ℂ)}
    (hDm : MeasurableSet D) (hD0 : volume D ≠ 0) {n₀ : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) :
    ∃ n : ℕ, n₀ ≤ n ∧ Wc D n (phaseW s₁ ν) ν s₁ ≠ 0 := by
  obtain ⟨δ, hδ, hne⟩ := exists_WX_ne_zero (F := F) ν hs₁
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ')
  set n : ℕ := max n₀ m with hn
  have hnm : (m : ℝ) ≤ n := by exact_mod_cast le_max_right n₀ m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set lo : ℝ := 1 / ((n : ℝ) + 1) with hlo
  have hlo_lt : lo < δ' := by
    rw [hlo, one_div_lt (by positivity) hδ'0]
    linarith
  set hi : ℝ := (lo + δ') / 2 with hhi
  have hlh : lo < hi := by rw [hhi]; linarith
  have hhiδ : hi < δ := by
    have : δ' ≤ δ := min_le_left _ _
    rw [hhi]; linarith
  have hhin : hi ≤ (n : ℝ) + 1 := by
    have : δ' ≤ 1 := min_le_right _ _
    rw [hhi]; linarith
  refine ⟨n, le_max_left _ _, ?_⟩
  set V' : Set (InfinitePlace F → ℝ) :=
    Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) with hV'
  have hV'sub : V' ⊆ vBox F n := fun v hv w => ⟨hv.1 w, (hv.2 w).trans hhin⟩
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n := fun x hx w =>
    (hb x hx w).trans (by exact_mod_cast le_max_left n₀ m)
  set h : X F → ℝ := (X.x ⁻¹' D : Set (X F)).indicator (fun Q => ‖WX s₁ ν Q‖) with hh
  have hSm : MeasurableSet (X.x ⁻¹' D : Set (X F)) := X.measurable_x hDm
  have e : ∀ Q : X F, conj (stripFn D 0 (phaseW s₁ ν) Q) * WX s₁ ν Q = ((h Q : ℝ) : ℂ) := by
    intro Q
    rw [stripFn_zero, hh]
    by_cases hQ : Q.x ∈ D
    · rw [indicator_of_mem hQ, indicator_of_mem (show Q ∈ X.x ⁻¹' D from hQ), one_mul,
        conj_phaseW_mul]
    · rw [indicator_of_notMem hQ, indicator_of_notMem (show Q ∉ X.x ⁻¹' D from hQ)]
      simp
  have hWint : IntegrableOn (WX s₁ ν : X F → ℂ) (X.box n) (X.vol F) :=
    (continuous_WX hs₁ ν).continuousOn.integrableOn_compact (isCompact_box n)
  have hint0 := cf_integrable (n := n) hDm (measurable_phaseW hs₁ ν) (norm_phaseW_le s₁ ν) hWint
  have hint : IntegrableOn h (X.box n) (X.vol F) := by
    have := hint0.norm
    refine this.congr (Eventually.of_forall fun Q => ?_)
    change ‖conj (stripFn D 0 (phaseW s₁ ν) Q) * WX s₁ ν Q‖ = h Q
    rw [e Q, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    rw [hh]
    exact indicator_nonneg (fun Q _ => norm_nonneg _) Q
  have hnonneg : 0 ≤ᵐ[(X.vol F).restrict (X.box n)] h :=
    Eventually.of_forall fun Q => indicator_nonneg (fun Q _ => norm_nonneg _) Q
  have hWc : Wc D n (phaseW s₁ ν) ν s₁ = ((∫ Q in X.box n, h Q ∂X.vol F : ℝ) : ℂ) := by
    unfold Wc cf
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall e)
  rw [hWc]
  refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  -- the support contains `{x ∈ D, v ∈ V'}`, of positive measure
  set S' : Set (X F) := X.v ⁻¹' V' ∩ X.x ⁻¹' D with hS'
  have hVm : MeasurableSet (X.v ⁻¹' V' : Set (X F)) := X.measurable_v measurableSet_Icc
  have hS'sub : S' ⊆ Function.support h ∩ X.box n := by
    rintro Q ⟨hQv, hQx⟩
    refine ⟨?_, (mem_box_iff n Q).mpr ⟨hbn _ hQx, hV'sub hQv⟩⟩
    rw [Function.mem_support, hh, indicator_of_mem hQx]
    exact norm_ne_zero_iff.mpr (hne Q fun w => lt_of_le_of_lt (hQv.2 w) hhiδ)
  have hS'pos : X.vol F S' ≠ 0 := by
    have h1 := X.setLIntegral_strip (F := F) hDm
      (f := fun p => V'.indicator (fun _ => (1 : ℝ≥0∞)) p.2)
      ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)
    have h2 : ∫⁻ Q in (X.x ⁻¹' D : Set (X F)), V'.indicator (fun _ => (1 : ℝ≥0∞)) Q.v
        ∂X.vol F = X.vol F S' := by
      have e' : (fun Q : X F => V'.indicator (fun _ => (1 : ℝ≥0∞)) Q.v)
          = (X.v ⁻¹' V' : Set (X F)).indicator 1 := by
        funext Q
        by_cases hQ : Q.v ∈ V'
        · rw [indicator_of_mem hQ, indicator_of_mem (show Q ∈ X.v ⁻¹' V' from hQ)]; rfl
        · rw [indicator_of_notMem hQ, indicator_of_notMem (show Q ∉ X.v ⁻¹' V' from hQ)]
      rw [e', lintegral_indicator_one hVm, Measure.restrict_apply hVm]
    rw [← h2, h1]
    have h3 : ∀ x : InfinitePlace F → ℂ,
        ∫⁻ v, (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
          V'.indicator (fun _ => (1 : ℝ≥0∞)) p.2) (x, v) ∂X.nuV F = X.nuV F V' := fun _ =>
      lintegral_indicator_one measurableSet_Icc
    rw [lintegral_congr h3, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact mul_ne_zero (nuV_Icc_ne_zero (le_of_eq hlo.symm) hlh hhin) hD0
  rw [Measure.restrict_apply' (X.measurableSet_box n)]
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hS'pos) (measure_mono hS'sub)

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.GK_E
/-! # WP-GK, file 1: Theorem E without hypotheses, `hsm`, `hne`, Lemma KW

Setting of the cut: `hG : Good 𝔪`, `hz6`, `g : AllowedGen ι 𝔪`, `hgood` (every exterior prime is
`C3I.Good`), `hd : DD.DiffInS 𝔪`.  The theta functional is WP-T's `T.theta hG hz6`.

* `hsm`: the scalar law `SmulOn {Re s > 1}` of `T.theta` (G1's hypothesis `hsm`).
* `per_all`: cube periodicity at every exterior prime (from `F.per`).
* **`tau_eq_coefF'`** (Theorem E): `τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`;
  `tau_eq_Kir`: the same with G1's Kirillov function.
* **`hne`**: some Kirillov value is nonzero (G1's hypothesis `hne`).
* `tau_eq_zero_of_theta`: `θ_Φ = 0 ⇒ τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0` (converse of (C10′)).
* `theta_wSec_eq_zero`: `θ_Φ = 0 ⇒ θ_{wΦ} = 0` (Corollary N, `N2.theta_eq_zero_iff`).
* **`KW`**: MATH3's Lemma KW in G1's form `G1.KW hG hz6 (T.theta hG hz6)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### `θ = 0 ⇒ τ ≡ 0`, and `θ_Φ = 0 ⇒ θ_{wΦ} = 0` -/

/-- **Converse of (C10′)**: if `θ_{Φ.twist} = 0` (for one finite-index `Γ` fixing the twist), then
`τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0`. -/
theorem tau_eq_zero_of_theta_oai (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) (h : C5.theta Γ (Φ.twist hG hz6) = 0)
    {ν : SInt 𝔪} (hν : ν ≠ 0) : T.tau hG hz6 Φ ν = 0 := by
  obtain ⟨D, κ, n₀, hc, hκ, hDm, hD0, hb⟩ := T.hasSeed hG hz6 Φ hν
  have hs1 : (1 : ℝ) < (4 / 3 : ℂ).re := by norm_num
  obtain ⟨n, hn, hW⟩ := T.exists_Wc_ne_zero (ν : F) (s₁ := (4 / 3 : ℂ)) hs1 hDm hD0 hb
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n := fun x hx w => (hb x hx w).trans (by exact_mod_cast hn)
  have hφ := T.measurable_phaseW (F := F) (s₁ := (4 / 3 : ℂ)) hs1 (ν : F)
  have hφ1 := T.norm_phaseW_le (F := F) (4 / 3 : ℂ) (ν : F)
  have i := T.integral_theta_of_hasCoef hG hz6 Φ hν hΓ hc hDm hbn hφ hφ1
  rw [← X.coeffFunctional_apply Γ n _ (measurable_stripFn hDm _ hφ) 1
    (norm_stripFn_le _ _ hφ1), h, map_zero] at i
  rcases mul_eq_zero.mp i.symm with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hκ
    · exact h2
  · exact absurd h1 hW

/-! ### Lemma KW -/

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.tau_eq_zero_of_theta_oai.{u_1} := @ArtinKP.GK.tau_eq_zero_of_theta_oai.{u_1}
