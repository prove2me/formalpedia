-- Prove2me | solution 1 for ArtinKP.X.X.ims
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:39:42.310384+00:00
-- url     : https://prove2.me/submissions/114e4471-c722-4ef6-9ddd-62c94106e316

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_X_X_IsInv_lap
import Theorems.Thm_ArtinKP_X_X_inner_coreL2_coreLap_self
import Theorems.Thm_ArtinKP_X_X_integrable_pou_mul
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
import Theorems.Thm_ArtinKP_X_X_mem_core_of_support
import Theorems.Thm_ArtinKP_X_X_qgreen

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol
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
-- module Solutions.Artin.KP.X2_Calc
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

lemma pd_mul {U W : Coord F → ℂ} {y : Coord F} (hU : DifferentiableAt ℝ U y)
    (hW : DifferentiableAt ℝ W y) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun y => U y * W y) y = U y * pd w k W y + W y * pd w k U y := by
  unfold pd
  rw [fderiv_fun_mul hU hW]
  rfl

lemma pd_const (c : ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k (fun _ => c) y = 0 := by
  unfold pd
  simp

lemma pd_const' (c : ℂ) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun _ : Coord F => c) = fun _ => 0 := funext (pd_const c w k)

lemma pd_conj (U : Coord F → ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k (fun y => conj (U y)) y = conj (pd w k U y) := by
  unfold pd
  have h : (fun y => conj (U y)) = Complex.conjCLE ∘ U := rfl
  rw [h, Complex.conjCLE.comp_fderiv]
  rfl

lemma gamE_conj (U W : Coord F → ℂ) (y : Coord F) :
    gamE (fun y => conj (U y)) (fun y => conj (W y)) y = conj (gamE U W y) := by
  unfold gamE
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_conj, pd_conj]
  simp

lemma gamE_mul_left {U U' W : Coord F → ℂ} {y : Coord F} (hU : DifferentiableAt ℝ U y)
    (hU' : DifferentiableAt ℝ U' y) :
    gamE (fun y => U y * U' y) W y = U y * gamE U' W y + U' y * gamE U W y := by
  unfold gamE
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_mul hU hU']
  ring

/-- **Leibniz rule for the Laplacian.** -/
theorem lapE_mul {U W : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (hW : ContDiff ℝ 2 W) (y : Coord F) :
    lapE (fun y => U y * W y) y = U y * lapE W y + W y * lapE U y - 2 * gamE U W y := by
  have hd : ∀ {V : Coord F → ℂ}, ContDiff ℝ 2 V → Differentiable ℝ V :=
    fun h => h.differentiable (by simp)
  have hpd : ∀ {V : Coord F → ℂ}, ContDiff ℝ 2 V → ∀ w k, Differentiable ℝ (pd w k V) :=
    fun h w k => (contDiff_pd (m := 1) h (by norm_num) w k).differentiable (by simp)
  unfold lapE gamE
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : ∀ k, pd w k (fun y => U y * W y) = fun y => U y * pd w k W y + W y * pd w k U y :=
    fun k => funext fun z => pd_mul (hd hU z) (hd hW z) w k
  have h2 : ∀ k, pd w k (fun y => U y * pd w k W y + W y * pd w k U y) y =
      (U y * pd w k (pd w k W) y + pd w k W y * pd w k U y) +
        (W y * pd w k (pd w k U) y + pd w k U y * pd w k W y) := by
    intro k
    rw [pd_add (show DifferentiableAt ℝ (fun y => U y * pd w k W y) y from
        ((hd hU) y).mul (hpd hW w k y))
      (show DifferentiableAt ℝ (fun y => W y * pd w k U y) y from
        ((hd hW) y).mul (hpd hU w k y)),
      pd_mul (hd hU y) (hpd hW w k y), pd_mul (hd hW y) (hpd hU w k y)]
  simp_rw [h1, h2]
  simp only [Fin.sum_univ_three]
  ring

/-! ### The weights `ρ · a_k` -/

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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

/-! ### The action of `G∞` in the chart -/

lemma chart_actE (g : Ginf F) (y : Coord F) : chart F (actE g y) = g • chart F y := by
  simp [actE]

theorem isoHalf_actE (g : Ginf F) : IsoHalf (actE g) := by
  choose φ hφ hg using fun w => mem_iso1 (g w)
  have : actE g = fun (y : Coord F) w => φ w (y w) := by
    funext y w
    change chart1.symm (g w • chart1 (y w)) = _
    rw [hg w, Homeomorph.symm_apply_apply]
  rw [this]
  exact isoHalf_pi hφ

/-! ### Calculus on `X` -/

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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

lemma X.Smooth.mul {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) :
    X.Smooth fun P => u P * w P := ContDiff.mul hu.contDiff hw.contDiff

lemma X.Smooth.conj {u : X F → ℂ} (hu : X.Smooth u) : X.Smooth fun P => conj (u P) :=
  Complex.conjCLE.contDiff.comp hu.contDiff

lemma eventuallyEq_chart {β : Type*} {u w : X F → β} {P : X F} (h : u =ᶠ[𝓝 P] w) :
    (fun y => u (chart F y)) =ᶠ[𝓝 ((chart F).symm P)] fun y => w (chart F y) := by
  have ht : Tendsto (chart F) (𝓝 ((chart F).symm P)) (𝓝 P) := by
    have := (chart F).continuous.continuousAt (x := (chart F).symm P)
    rwa [ContinuousAt, Homeomorph.apply_symm_apply] at this
  exact ht.eventually h

lemma X.gam_congr {u u' w w' : X F → ℂ} {P : X F} (h : u =ᶠ[𝓝 P] u') (h' : w =ᶠ[𝓝 P] w') :
    X.gam u w P = X.gam u' w' P :=
  gamE_congr (eventuallyEq_chart h) (eventuallyEq_chart h')

lemma gamE_zero_left (W : Coord F → ℂ) (y : Coord F) : gamE (fun _ : Coord F => (0 : ℂ)) W y = 0 := by
  simp [gamE, pd_const']

lemma X.gam_eq_zero_of_notMem_tsupport {u : X F → ℂ} (w : X F → ℂ) {P : X F}
    (hP : P ∉ tsupport u) : X.gam u w P = 0 := by
  have h : u =ᶠ[𝓝 P] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hP
  rw [X.gam_congr h (Filter.EventuallyEq.refl _ w)]
  exact gamE_zero_left _ _

lemma X.gam_comm (u w : X F → ℂ) : X.gam u w = X.gam w u := by
  funext P
  unfold X.gam
  rw [gamE_comm]

lemma X.gam_conj (u w : X F → ℂ) (P : X F) :
    X.gam (fun P => conj (u P)) (fun P => conj (w P)) P = conj (X.gam u w P) :=
  gamE_conj _ _ _

lemma X.Smooth.differentiable {u : X F → ℂ} (hu : X.Smooth u) :
    Differentiable ℝ fun y => u (chart F y) := hu.contDiff.differentiable (by simp)

/-- Leibniz rule for the Laplacian on `X`. -/
lemma X.lap_mul {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) (P : X F) :
    X.lap (fun P => u P * w P) P = u P * X.lap w P + w P * X.lap u P - 2 * X.gam u w P := by
  unfold X.lap X.gam
  rw [lapE_mul (hu.contDiff.of_le two_le_top) (hw.contDiff.of_le two_le_top)]
  simp

lemma X.gam_mul_left {u u' w : X F → ℂ} (hu : X.Smooth u) (hu' : X.Smooth u') (P : X F) :
    X.gam (fun P => u P * u' P) w P = u P * X.gam u' w P + u' P * X.gam u w P := by
  unfold X.gam
  rw [gamE_mul_left (hu.differentiable _) (hu'.differentiable _)]
  simp

/-! ### Invariance -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

lemma X.IsInv.gam {u w : X F → ℂ} (hinv : X.IsInv Γ u) (hu : X.Smooth u)
    (hinv' : X.IsInv Γ w) (hw : X.Smooth w) : X.IsInv Γ (X.gam u w) := by
  intro γ P
  have h := X.gam_comp_Ginf hu hw (gin (γ : SL(2, 𝓞 F))) P
  have h2 : (fun P => u (gin (γ : SL(2, 𝓞 F)) • P)) = u := funext fun Q => hinv γ Q
  have h3 : (fun P => w (gin (γ : SL(2, 𝓞 F)) • P)) = w := funext fun Q => hinv' γ Q
  rw [h2, h3] at h
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

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

lemma X.gam_conj_self (u : X F → ℂ) (P : X F) :
    X.gam (fun P => conj (u P)) u P = (X.grad2 u P : ℂ) := by
  unfold X.gam X.grad2 gamE
  push_cast
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pd_conj, Complex.conj_mul']

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Weak
/-! # WP-X2, file 6: cut-offs; classical solutions are weak solutions in `H¹`

* `X.isClosed_saturation`: `Γ · K` is closed for compact `K`;
* `X.mem_core_of_support`: a smooth `Γ`-invariant function whose support lies in `Γ · K`,
  `K` compact, belongs to the core (it is `∑_γ φ ∘ γ` with `φ = ψ w / ∑_γ ψ ∘ γ`);
* `X.integrable_pou_mul`: `η · h` is integrable for `h` continuous, invariant, supported in
  `Γ · K`;
* `X.exists_weakSol`: **the height cut-off lemma** (MATH2 §1.6).  A smooth `Γ`-invariant `u`
  with `u ∈ L²(Γ\X)` and `Δu = λu + f` pointwise, `f ∈ L²(Γ\X)`, lies in `H¹(Γ\X)` and satisfies
  the weak equation `𝔇(u', u) − λ⟪u', u⟫ = ⟪u', f⟫` against all `u' ∈ H¹`, provided there are
  cut-offs `χ_n` (smooth, invariant, `0 ≤ χ_n ≤ 1`, compact support modulo `Γ`, `χ_n → 1`
  pointwise, `∑_w v_w²|∇_w χ_n|² ≤ ε_n → 0`).  Finite energy of `u` is a conclusion, not a
  hypothesis (IMS localisation formula).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Saturations of compact sets -/

/-- `Γ · K` is closed for compact `K`. -/
theorem X.isClosed_saturation (Γ : Subgroup (SL(2, 𝓞 F))) {K : Set (X F)} (hK : IsCompact K) :
    IsClosed {P : X F | ∃ γ : Γ, γ • P ∈ K} := by
  have h : {P : X F | ∃ γ : Γ, γ • P ∈ K} = ⋃ γ : Γ, (fun P : X F => γ • P) ⁻¹' K := by
    ext P; simp
  rw [h]
  refine LocallyFinite.isClosed_iUnion ?_ fun γ => hK.isClosed.preimage (continuous_const_smul γ)
  intro P₀
  obtain ⟨R, N, hN, hR⟩ := exists_finset_nhds Γ hK P₀
  refine ⟨N, hN, R.finite_toSet.subset ?_⟩
  rintro γ ⟨P, hP, hPN⟩
  exact hR P hPN γ hP

lemma X.tsupport_subset_saturation {β : Type*} [Zero β] {h : X F → β} {K : Set (X F)}
    (hK : IsCompact K) (hsupp : ∀ P, h P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) :
    tsupport h ⊆ {P : X F | ∃ γ : Γ, γ • P ∈ K} :=
  closure_minimal (fun P hP => hsupp P hP) (X.isClosed_saturation Γ hK)

/-! ### A bump function positive on a compact set -/

/-! ### Invariant functions supported in `Γ · K` are averages -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Cutoff
/-! # WP-X2, file 7: the height cut-off lemma

`X.exists_weakSol`: a smooth `Γ`-invariant `u ∈ L²(Γ\X)` with `Δu = λu + f` pointwise,
`f ∈ L²(Γ\X)`, lies in `H¹(Γ\X)` and is a weak solution against all of `H¹`, given cut-offs
`χ_n` (smooth, invariant, `0 ≤ χ_n ≤ 1`, compact support modulo `Γ`, `χ_n → 1` pointwise,
`∑_w v_w²|∇_w χ_n|² ≤ ε_n → 0`).  This is MATH2 §1.6; the only completeness input is the
existence of the cut-offs (MATH2 §1.4(d)).

The energy of `χ u` is computed by the IMS localisation formula (`X.ims`)
`∫ |∇(χu)|² = ∫ χ² Re(ū Δu) + ∫ |u|² |∇χ|²`, so finiteness of the energy of `u` is not assumed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

/-- **IMS localisation formula** on `Γ \ X`: for a real cut-off `c` (smooth, invariant, compact
support modulo `Γ`) and `u` smooth and invariant,
`∫ |∇(cu)|² = ∫ c² Re(ū Δu) + |u|² |∇c|²`. -/
theorem X.ims_oai {c : X F → ℝ} (hcs : X.Smooth fun P => (c P : ℂ)) (hcinv : X.IsInv Γ c)
    {K : Set (X F)} (hK : IsCompact K) (hcK : ∀ P, c P ≠ 0 → ∃ γ : Γ, γ • P ∈ K)
    {u : X F → ℂ} (hu : X.Smooth u) (hinv : X.IsInv Γ u)
    (a : X.core Γ) (ha : (a : X F → ℂ) = fun P => (c P : ℂ) * u P) :
    Integrable (fun P => (X.pou Γ P).toReal *
        (c P ^ 2 * (conj (u P) * X.lap u P).re +
          ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P)) (X.vol F) ∧
      ∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F =
        ∫ P, (X.pou Γ P).toReal *
          (c P ^ 2 * (conj (u P) * X.lap u P).re +
            ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P) ∂X.vol F := by
  set cC : X F → ℂ := fun P => (c P : ℂ) with hcC
  have hcCinv : X.IsInv Γ cC := fun γ P => by simp only [hcC, hcinv γ P]
  have hconjc : (fun P => conj (cC P)) = cC := funext fun P => Complex.conj_ofReal _
  have hsat : ∀ P, P ∈ tsupport cC → ∃ γ : Γ, γ • P ∈ K :=
    fun P hP => X.tsupport_subset_saturation hK
      (fun Q hQ => hcK Q (by simpa [hcC] using hQ)) hP
  have hz : ∀ P, P ∉ tsupport cC → cC P = 0 := fun P hP => image_eq_zero_of_notMem_tsupport hP
  -- the auxiliary core function `e = c |u|²`
  set e : X F → ℂ := fun P => cC P * (conj (u P) * u P) with he
  have hes : X.Smooth e := hcs.mul (hu.conj.mul hu)
  have heinv : X.IsInv Γ e := fun γ P => by simp only [he, hcCinv γ P, hinv γ P]
  have hecore : e ∈ X.core Γ :=
    X.mem_core_of_support hes heinv hK fun P hP => hcK P (by
      intro h0
      apply hP
      simp [he, hcC, h0])
  obtain ⟨φ, hφ, hφc, heφ⟩ := hecore
  have hq := X.qgreen (X.isPOU_pou Γ) hφ hφc hcs hcCinv
  rw [← heφ] at hq
  -- invariance and continuity of the pieces
  have hlapu_inv := hinv.lap hu
  have hlapc_inv := hcCinv.lap hcs
  have hgcc_inv := hcCinv.gam hcs hcCinv hcs
  have hguc_inv := hinv.gam hu hcCinv hcs
  have hconju_inv : X.IsInv Γ fun P => conj (u P) := fun γ P => by simp only [hinv γ P]
  have hgbc_inv := hconju_inv.gam hu.conj hcCinv hcs
  have hgec_inv := heinv.gam hes hcCinv hcs
  have c1 : Continuous cC := hcs.continuous
  have c2 : Continuous u := hu.continuous
  have c3 : Continuous (X.lap u) := hu.lap.continuous
  have c4 : Continuous (X.lap cC) := hcs.lap.continuous
  have c5 : Continuous (X.gam cC cC) := (hcs.gam hcs).continuous
  have c6 : Continuous (X.gam u cC) := (hu.gam hcs).continuous
  have c7 : Continuous (X.gam (fun P => conj (u P)) cC) := (hu.conj.gam hcs).continuous
  have c8 : Continuous (X.gam e cC) := (hes.gam hcs).continuous
  have c9 : Continuous fun P => conj (u P) := Complex.continuous_conj.comp c2
  set J : X F → ℂ := fun P => cC P ^ 2 * (conj (u P) * X.lap u P) +
      (conj (u P) * u P) * X.gam cC cC P +
      cC P * (u P * X.gam (fun P => conj (u P)) cC P - conj (u P) * X.gam u cC P) with hJ
  have hJint : Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * J P) (X.vol F) := by
    refine X.integrable_pou_mul (by fun_prop) (fun γ P => ?_) hK fun P hP => hsat P ?_
    · simp only [hJ, hcCinv γ P, hinv γ P, hlapu_inv γ P, hgcc_inv γ P, hguc_inv γ P,
        hgbc_inv γ P]
    · by_contra hPn
      apply hP
      simp [hJ, hz P hPn, X.gam_eq_zero_of_notMem_tsupport cC hPn]
  have h1int : Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * (e P * X.lap cC P))
      (X.vol F) := by
    refine X.integrable_pou_mul (by fun_prop) (fun γ P => ?_) hK fun P hP => hsat P ?_
    · simp only [heinv γ P, hlapc_inv γ P]
    · by_contra hPn
      apply hP
      simp [he, hz P hPn]
  have h2int : Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * X.gam e cC P)
      (X.vol F) := by
    refine X.integrable_pou_mul c8 hgec_inv hK fun P hP => hsat P ?_
    by_contra hPn
    apply hP
    rw [X.gam_comm]
    exact X.gam_eq_zero_of_notMem_tsupport e hPn
  -- the pointwise identity
  have hpt : ∀ P, conj ((a : X F → ℂ) P) * X.lap a P =
      J P + (e P * X.lap cC P - X.gam e cC P) := by
    intro P
    have e1 : X.lap a P = cC P * X.lap u P + u P * X.lap cC P - 2 * X.gam cC u P := by
      rw [ha]
      exact X.lap_mul hcs hu P
    have e2 : X.gam e cC P = cC P * X.gam (fun P => conj (u P) * u P) cC P +
        (conj (u P) * u P) * X.gam cC cC P := X.gam_mul_left hcs (hu.conj.mul hu) P
    have e3 : X.gam (fun P => conj (u P) * u P) cC P =
        conj (u P) * X.gam u cC P + u P * X.gam (fun P => conj (u P)) cC P :=
      X.gam_mul_left hu.conj hu P
    have e4 : X.gam cC u P = X.gam u cC P := by rw [X.gam_comm]
    have e5 : conj ((a : X F → ℂ) P) = cC P * conj (u P) := by
      rw [ha]
      simp [hcC]
    rw [e5, e1, e2, e3, e4]
    simp only [hJ, he]
    ring
  -- integrate
  have hmain : ((∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F : ℝ) : ℂ) =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * J P ∂X.vol F := by
    rw [← X.inner_coreL2_coreLap_self, X.inner_coreL2]
    have h3 : (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj ((a : X F → ℂ) P) *
        X.lift Γ (X.coreL2 Γ (X.coreLap Γ a)) P)) =ᵐ[X.vol F]
        fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * J P +
          ((((X.pou Γ P).toReal : ℝ) : ℂ) * (e P * X.lap cC P) -
            (((X.pou Γ P).toReal : ℝ) : ℂ) * X.gam e cC P) := by
      filter_upwards [X.lift_coreL2 (X.coreLap Γ a)] with P hP
      rw [hP, X.coreLap_coe, hpt]
      ring
    rw [integral_congr_ae h3, integral_add hJint
      (show Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * (e P * X.lap cC P) -
        (((X.pou Γ P).toReal : ℝ) : ℂ) * X.gam e cC P) (X.vol F) from h1int.sub h2int),
      integral_sub h1int h2int, hq, sub_self, add_zero]
  have hre : ∀ P, ((((X.pou Γ P).toReal : ℝ) : ℂ) * J P).re =
      (X.pou Γ P).toReal * (c P ^ 2 * (conj (u P) * X.lap u P).re +
        ‖u P‖ ^ 2 * X.grad2 cC P) := by
    intro P
    have g1 : X.gam cC cC P = (X.grad2 cC P : ℂ) := by
      have := X.gam_conj_self cC P
      rwa [hconjc] at this
    have g2 : X.gam (fun P => conj (u P)) cC P = conj (X.gam u cC P) := by
      have := X.gam_conj u cC P
      rwa [hconjc] at this
    have g3 : conj (u P) * u P = ((‖u P‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; norm_cast
    have hcP : cC P = (c P : ℂ) := rfl
    simp only [hJ]
    rw [g1, g2, g3, hcP]
    generalize X.grad2 cC P = G
    generalize X.gam u cC P = g
    generalize X.lap u P = l
    generalize u P = z
    generalize (X.pou Γ P).toReal = t
    generalize c P = s
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    ring
  constructor
  · have := hJint.re
    refine this.congr (Filter.Eventually.of_forall fun P => ?_)
    exact hre P
  · have h4 := congrArg Complex.re hmain
    rw [Complex.ofReal_re] at h4
    rw [h4]
    have h5 := integral_re hJint
    rw [show (∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * J P ∂X.vol F).re =
      RCLike.re (∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * J P ∂X.vol F) from rfl, ← h5]
    refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
    exact hre P

/-! ### Testing against the core -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.ims_oai.{u_1} := @ArtinKP.X.X.ims_oai.{u_1}
