-- Prove2me | solution 1 for ArtinKP.X.X.coreL2_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:58.966225+00:00
-- url     : https://prove2.me/submissions/5b21f4d1-c76f-472b-b557-c3b63e9293b2

import Mathlib
import Definitions.Def_ArtinKPB011
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
import Theorems.Thm_ArtinKP_X_X_smooth_of_mem_core

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

lemma volume_absolutelyContinuous_muE : (volume : Measure (Coord F)) ≪ muE F :=
  withDensity_absolutelyContinuous'
    (show Measurable fun y : Coord F => ENNReal.ofReal (rho y) from by
      unfold rho; fun_prop).aemeasurable
    (Filter.Eventually.of_forall fun y => by simpa using rho_pos y)

instance instIsOpenPosMeasureCoordMuE : (muE F).IsOpenPosMeasure := volume_absolutelyContinuous_muE.isOpenPosMeasure

instance instIsOpenPosMeasureXVol : (X.vol F).IsOpenPosMeasure :=
  ⟨fun U hU hne => by
    rw [← (measurePreserving_chart F).measure_preimage hU.nullMeasurableSet]
    exact (hU.preimage (chart F).continuous).measure_ne_zero _
      (hne.preimage (chart F).surjective)⟩

/-! ### Calculus on `X`: basic rules -/

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

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

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

lemma X.lift_coreL2 (w : X.core Γ) : X.lift Γ (X.coreL2 Γ w) =ᵐ[X.vol F] w :=
  X.lift_toL2 (X.l2Rep_of_mem_core w.2)

lemma X.coreL2_injective_oai : Function.Injective (X.coreL2 Γ) := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  have h0 : X.coreL2 Γ w = 0 := hw
  have h1 := X.lift_coreL2 w
  rw [h0] at h1
  have h2 : X.lift Γ (0 : X.L2 Γ) =ᵐ[X.vol F] 0 :=
    liftQ_ae_eq (X.isPOU_pou Γ) (Lp.coeFn_zero ℂ 2 (X.quotVol Γ))
  have h3 : (w : X F → ℂ) =ᵐ[X.vol F] 0 := h1.symm.trans h2
  have h4 := ((X.smooth_of_mem_core w.2).continuous.ae_eq_iff_eq (X.vol F) continuous_zero).1 h3
  exact Subtype.ext h4

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.coreL2_injective_oai.{u_1} := @ArtinKP.X.X.coreL2_injective_oai.{u_1}
