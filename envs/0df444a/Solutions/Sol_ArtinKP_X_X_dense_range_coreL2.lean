-- Prove2me | solution 1 for ArtinKP.X.X.dense_range_coreL2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:33:23.186193+00:00
-- url     : https://prove2.me/submissions/4cf4fb94-6570-4e2e-8a8a-5636b67499dc

import Mathlib
import Definitions.Def_ArtinKPB012
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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
-- module Solutions.Artin.KP.X_L2
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

lemma liftQ_smul (u : Lp ℂ 2 (quotMeasure G η μ)) (g : G) (a : α) :
    liftQ u (g • a) = liftQ u a := by
  unfold liftQ; rw [mk_smul]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
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

lemma X.lift_smul (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) (γ : Γ) (P : X F) :
    X.lift Γ u (γ • P) = X.lift Γ u P :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  liftQ_smul u γ P

lemma X.stronglyMeasurable_lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) :
    StronglyMeasurable (X.lift Γ u) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  stronglyMeasurable_liftQ u

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

/-! ### Invariance -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Local finiteness and averaging -/

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

/-- An element of `L²(Γ\X)` whose pull-back vanishes almost everywhere is zero. -/
lemma X.eq_zero_of_lift_ae_eq_zero (v : X.L2 Γ) (h : X.lift Γ v =ᵐ[X.vol F] 0) : v = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hm : MeasurableSet {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (Lp.stronglyMeasurable v).measurable (measurableSet_singleton 0)
  have key : ∀ᵐ q ∂(Measure.map (Quotient.mk (MulAction.orbitRel Γ (X F)))
      ((X.vol F).withDensity (X.pou Γ))),
      q ∈ {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (ae_map_iff measurable_mk.aemeasurable hm).2
      ((withDensity_absolutelyContinuous _ _).ae_le h)
  exact key

/-! ### Local integrability of pull-backs -/

lemma X.integrableOn_lift (v : X.L2 Γ) {K : Set (X F)} (hK : IsCompact K) :
    IntegrableOn (X.lift Γ v) K (X.vol F) := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  obtain ⟨n, hn⟩ := X.exists_box_of_isCompact hK
  have h1 : MemLp (X.lift Γ v) 2 ((X.vol F).restrict (X.box n)) :=
    memLp_liftQ_restrict (X.isPOU_pou Γ) (X.measurableSet_box n) (ENNReal.natCast_ne_top _)
      (X.tsum_indicator_box_le_boxMult Γ n) v
  have h2 : Integrable (X.lift Γ v) ((X.vol F).restrict (X.box n)) :=
    h1.integrable (by norm_num)
  exact IntegrableOn.mono_set h2 hn

lemma X.integrable_mul_lift (v : X.L2 Γ) {φ : X F → ℂ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : Integrable (fun P => φ P * X.lift Γ v P) (X.vol F) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  have h1 : IntegrableOn (fun P => φ P * X.lift Γ v P) (tsupport φ) (X.vol F) :=
    Integrable.bdd_mul (c := C) (X.integrableOn_lift v hc) hφ.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  refine (integrableOn_iff_integrable_of_support_subset fun P hP => ?_).1 h1
  by_contra hPn
  exact hP (by simp [image_eq_zero_of_notMem_tsupport hPn])

/-! ### The core -/

variable (Γ)

variable {Γ}

lemma X.avg_mem_core {φ : X F → ℂ} (hφ : X.Smooth φ) (hc : HasCompactSupport φ) :
    X.avg Γ φ ∈ X.core Γ := ⟨φ, hφ, hc, rfl⟩

lemma X.avg_conj (φ : X F → ℂ) (P : X F) :
    X.avg Γ (fun P => conj (φ P)) P = conj (X.avg Γ φ P) := by
  unfold X.avg
  rw [Complex.conj_tsum]

variable (Γ)

variable {Γ}

/-- `⟪a, v⟫ = ∫ η conj(a) v` for a core function `a`. -/
lemma X.inner_coreL2 (a : X.core Γ) (v : X.L2 Γ) :
    ⟪X.coreL2 Γ a, v⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj ((a : X F → ℂ) P) * X.lift Γ v P) ∂X.vol F :=
  X.inner_toL2 (X.l2Rep_of_mem_core a.2) v

/-! ### Density of the core -/

theorem X.dense_range_coreL2_oai : Dense ((LinearMap.range (X.coreL2 Γ) : Submodule ℂ (X.L2 Γ)) : Set (X.L2 Γ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_orthogonal] at hv
  apply X.eq_zero_of_lift_ae_eq_zero
  -- the pulled back function in the chart, with the density
  set h : Coord F → ℂ := fun y => (rho y : ℂ) * X.lift Γ v (chart F y) with hh
  have hloc : LocallyIntegrable h volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    have h1 : IntegrableOn (X.lift Γ v) (chart F '' k) (X.vol F) :=
      X.integrableOn_lift v (hk.image (chart F).continuous)
    have h2 : IntegrableOn (fun y => X.lift Γ v (chart F y)) k (muE F) :=
      ((measurePreserving_chart F).integrableOn_image (chart F).measurableEmbedding).1 h1
    unfold IntegrableOn muE at h2
    rw [restrict_withDensity hk.measurableSet,
      integrable_withDensity_iff_integrable_smul' (by unfold rho; fun_prop)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h2
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hh, ENNReal.toReal_ofReal (rho_pos y).le, Complex.real_smul]
  have hzero : ∀ᵐ y ∂(volume : Measure (Coord F)), h y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => ?_
    set φ : X F → ℂ := fun P => ((g ((chart F).symm P) : ℝ) : ℂ) with hφdef
    have hφs : X.Smooth φ := by
      unfold X.Smooth
      simp only [hφdef, Homeomorph.symm_apply_apply]
      exact Complex.ofRealCLM.contDiff.comp hg
    have hφc : HasCompactSupport φ :=
      (hgc.comp_isClosedEmbedding (chart F).symm.isClosedEmbedding).comp_left Complex.ofReal_zero
    have hφconj : ∀ P, conj (φ P) = φ P := fun P => Complex.conj_ofReal _
    have h0 := hv (X.coreL2 Γ ⟨X.avg Γ φ, X.avg_mem_core hφs hφc⟩) (LinearMap.mem_range_self _ _)
    rw [X.inner_coreL2] at h0
    have h1 : ∀ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (X.avg Γ φ P) * X.lift Γ v P) =
        (((X.pou Γ P).toReal : ℝ) : ℂ) * (X.avg Γ φ P * X.lift Γ v P) := by
      intro P
      rw [← X.avg_conj]
      simp_rw [hφconj]
    simp only [h1] at h0
    rw [integral_avg_mul (X.isPOU_pou Γ) hφs.continuous.measurable
      (X.stronglyMeasurable_lift Γ v).measurable (fun γ P => X.lift_smul Γ v γ P)
      (X.integrable_mul_lift v hφs.continuous hφc).2.ne, integral_vol_eq] at h0
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hh, hφdef, Homeomorph.symm_apply_apply, Complex.real_smul]
    ring
  have h2 : ∀ᵐ y ∂(muE F), X.lift Γ v (chart F y) = 0 := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [hzero] with y hy
    simpa [hh, (rho_pos y).ne'] using hy
  have h3 : ∀ᵐ P ∂(X.vol F), X.lift Γ v P = 0 := by
    rw [← (measurePreserving_chart F).map_eq]
    exact ((chart F).measurableEmbedding.ae_map_iff).2 h2
  exact h3

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.dense_range_coreL2_oai.{u_1} := @ArtinKP.X.X.dense_range_coreL2_oai.{u_1}
