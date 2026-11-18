-- Prove2me | solution 1 for ArtinKP.X.X.integrable_pou_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:39:43.384218+00:00
-- url     : https://prove2.me/submissions/1277ec57-a2c3-4077-8a97-02c90addd3eb

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_summable_comp_smul_of_hasCompactSupport

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

/-! ### Algebraic rules -/

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

lemma X.Smooth.comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) :
    X.Smooth fun P => u (g • P) := by
  unfold X.Smooth
  have : (fun y => u (g • chart F y)) = fun y => (fun z => u (chart F z)) (actE g y) := by
    funext y; simp only [chart_actE]
  rw [this]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  exact hu'.comp (isoHalf_actE g).smooth

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

lemma IsPOU.enorm_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ‖(((η a).toReal : ℝ) : ℂ)‖ₑ = η a := by
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
  exact Real.enorm_toReal (hη.ne_top a)

lemma IsPOU.measurable_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    Measurable fun a => (((η a).toReal : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hη.measurable.ennreal_toReal

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

lemma X.Smooth.sum {ι : Type*} (s : Finset ι) {u : ι → X F → ℂ} (hu : ∀ i ∈ s, X.Smooth (u i)) :
    X.Smooth fun P => ∑ i ∈ s, u i P := ContDiff.sum fun i hi => (hu i hi).contDiff

lemma eventuallyEq_chart {β : Type*} {u w : X F → β} {P : X F} (h : u =ᶠ[𝓝 P] w) :
    (fun y => u (chart F y)) =ᶠ[𝓝 ((chart F).symm P)] fun y => w (chart F y) := by
  have ht : Tendsto (chart F) (𝓝 ((chart F).symm P)) (𝓝 P) := by
    have := (chart F).continuous.continuousAt (x := (chart F).symm P)
    rwa [ContinuousAt, Homeomorph.apply_symm_apply] at this
  exact ht.eventually h

/-! ### Invariance -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

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

lemma X.smooth_avg {φ : X F → ℂ} (hφ : X.Smooth φ) (hc : HasCompactSupport φ) :
    X.Smooth (X.avg Γ φ) := by
  unfold X.Smooth
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨R, -, hR⟩ := X.avg_eventuallyEq Γ hc (chart F y)
  have h1 := eventuallyEq_chart hR
  rw [Homeomorph.symm_apply_apply] at h1
  have h2 : X.Smooth fun P => ∑ γ ∈ R, φ (γ • P) := X.Smooth.sum R fun γ _ => hφ.comp_gamma γ
  exact h2.contDiff.contDiffAt.congr_of_eventuallyEq h1

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Weak
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub
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

lemma exists_bump {K : Set (X F)} (hK : IsCompact K) :
    ∃ ψ : X F → ℝ, X.Smooth (fun P => (ψ P : ℂ)) ∧ HasCompactSupport ψ ∧ (∀ P, 0 ≤ ψ P) ∧
      ∀ P ∈ K, 0 < ψ P := by
  have hK' : IsCompact ((chart F).symm '' K) := hK.image (chart F).symm.continuous
  obtain ⟨R, hR⟩ := hK'.isBounded.subset_closedBall (0 : Coord F)
  let f : ContDiffBump (0 : Coord F) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun P => f ((chart F).symm P), ?_, ?_, fun P => f.nonneg, fun P hP => ?_⟩
  · unfold X.Smooth
    simp only [Homeomorph.symm_apply_apply]
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_isClosedEmbedding (chart F).symm.isClosedEmbedding
  · have h1 : (chart F).symm P ∈ Metric.closedBall (0 : Coord F) R := hR ⟨P, hP, rfl⟩
    have h2 : (chart F).symm P ∈ Metric.closedBall (0 : Coord F) f.rIn :=
      Metric.closedBall_subset_closedBall (by
        change R ≤ max R 0 + 1
        linarith [le_max_left R 0]) h1
    show 0 < f ((chart F).symm P)
    rw [f.one_of_mem_closedBall h2]
    exact one_pos

/-- A smooth compactly supported `ψ` whose `Γ`-average does not vanish on `Γ · K`. -/
lemma exists_bump_avg (Γ : Subgroup (SL(2, 𝓞 F))) {K : Set (X F)} (hK : IsCompact K) :
    ∃ ψ : X F → ℂ, X.Smooth ψ ∧ HasCompactSupport ψ ∧
      ∀ P, (∃ γ : Γ, γ • P ∈ K) → X.avg Γ ψ P ≠ 0 := by
  obtain ⟨ψ, hψs, hψc, hψ0, hψK⟩ := exists_bump hK
  have hc : HasCompactSupport fun P => (ψ P : ℂ) := hψc.comp_left Complex.ofReal_zero
  refine ⟨fun P => (ψ P : ℂ), hψs, hc, ?_⟩
  rintro P ⟨γ₀, hγ₀⟩
  have hsum : Summable fun γ : Γ => ψ (γ • P) :=
    Complex.summable_ofReal.1 (X.summable_comp_smul_of_hasCompactSupport Γ hc P)
  have h1 : X.avg Γ (fun P => (ψ P : ℂ)) P = ((∑' γ : Γ, ψ (γ • P) : ℝ) : ℂ) := by
    unfold X.avg
    rw [Complex.ofReal_tsum]
  rw [h1]
  have h2 : 0 < ∑' γ : Γ, ψ (γ • P) :=
    lt_of_lt_of_le (hψK _ hγ₀) (hsum.le_tsum γ₀ fun γ _ => hψ0 _)
  exact_mod_cast h2.ne'

/-! ### Invariant functions supported in `Γ · K` are averages -/

lemma X.rep_hasCompactSupport {ψ : X F → ℂ} (hψc : HasCompactSupport ψ) (h : X F → ℂ) :
    HasCompactSupport (X.rep Γ ψ h) :=
  hψc.mono fun P hP => by
    intro h0
    apply hP
    simp [X.rep, show ψ P = 0 from h0]

lemma X.avg_rep {ψ h : X F → ℂ} (hinv : X.IsInv Γ h)
    (hne : ∀ P, h P ≠ 0 → X.avg Γ ψ P ≠ 0) : X.avg Γ (X.rep Γ ψ h) = h := by
  funext P
  have h1 : ∀ γ : Γ, X.rep Γ ψ h (γ • P) = ψ (γ • P) * (h P / X.avg Γ ψ P) := by
    intro γ
    unfold X.rep
    rw [hinv γ P, X.avg_inv Γ ψ γ P, mul_div_assoc]
  unfold X.avg
  simp_rw [h1]
  rw [tsum_mul_right]
  by_cases h0 : h P = 0
  · simp [h0]
  · have h2 : X.avg Γ ψ P ≠ 0 := hne P h0
    show X.avg Γ ψ P * (h P / X.avg Γ ψ P) = h P
    field_simp

lemma X.rep_contDiff {ψ h : X F → ℂ} (hψ : X.Smooth ψ) (hψc : HasCompactSupport ψ)
    {n : WithTop ℕ∞} (hn : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    (hh : ContDiff ℝ n fun y => h (chart F y))
    (hne : ∀ P ∈ tsupport h, X.avg Γ ψ P ≠ 0) :
    ContDiff ℝ n fun y => X.rep Γ ψ h (chart F y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : chart F y ∈ tsupport h
  · have h1 : ContDiffAt ℝ n (fun y => ψ (chart F y) * h (chart F y)) y :=
      ((hψ.contDiff.of_le hn).mul hh).contDiffAt
    have h2 : ContDiffAt ℝ n (fun y => X.avg Γ ψ (chart F y)) y :=
      ((X.smooth_avg (Γ := Γ) hψ hψc).contDiff.of_le hn).contDiffAt
    exact (h1.mul (h2.inv (hne _ hy))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp [X.rep, div_eq_mul_inv])
  · have h0 : h =ᶠ[𝓝 (chart F y)] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : X.rep Γ ψ h =ᶠ[𝓝 (chart F y)] fun _ => 0 := by
      filter_upwards [h0] with P hP
      simp [X.rep, hP]
    have h2 := eventuallyEq_chart h1
    rw [Homeomorph.symm_apply_apply] at h2
    exact contDiffAt_const.congr_of_eventuallyEq h2

/-- `η · h` is integrable for `h` continuous, `Γ`-invariant, supported in `Γ · K`. -/
theorem X.integrable_pou_mul_oai {h : X F → ℂ} (hc : Continuous h) (hinv : X.IsInv Γ h)
    {K : Set (X F)} (hK : IsCompact K) (hsupp : ∀ P, h P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) :
    Integrable (fun P => (((X.pou Γ P).toReal : ℝ) : ℂ) * h P) (X.vol F) := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  obtain ⟨ψ, hψ, hψc, hψK⟩ := exists_bump_avg Γ hK
  have h1 : ContDiff ℝ 0 fun y => X.rep Γ ψ h (chart F y) :=
    X.rep_contDiff hψ hψc (by simp) (contDiff_zero.2 (hc.comp (chart F).continuous))
      fun P hP => hψK P (X.tsupport_subset_saturation hK hsupp hP)
  have h2 : Continuous (X.rep Γ ψ h) := by
    have : X.rep Γ ψ h = (fun y => X.rep Γ ψ h (chart F y)) ∘ (chart F).symm := by
      funext P; simp
    rw [this]
    exact (contDiff_zero.1 h1).comp (chart F).symm.continuous
  have h3 := X.avg_rep hinv fun P hP => hψK P (hsupp P hP)
  refine ⟨((X.isPOU_pou Γ).measurable_toReal.mul hc.measurable).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt ?_ (lintegral_ne_top_of_continuous h2
    (X.rep_hasCompactSupport hψc h)).lt_top
  refine le_trans (le_of_eq ?_) (lintegral_avg_le (X.isPOU_pou Γ) h2.measurable)
  refine lintegral_congr fun P => ?_
  rw [h3, enorm_mul, (X.isPOU_pou Γ).enorm_toReal, mul_comm]

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.integrable_pou_mul_oai.{u_1} := @ArtinKP.X.X.integrable_pou_mul_oai.{u_1}
