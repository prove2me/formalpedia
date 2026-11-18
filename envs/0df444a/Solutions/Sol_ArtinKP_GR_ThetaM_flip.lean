-- Prove2me | solution 1 for ArtinKP.GR.ThetaM_flip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:20.381521+00:00
-- url     : https://prove2.me/submissions/98ebbe8b-ec6c-442c-aee9-23989a6321a7

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
import Theorems.Thm_ArtinKP_G2a_exists_major
import Theorems.Thm_ArtinKP_G2a_thetaT_translate

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma smul_apply (γ : SL(2, F)) (P : X F) (w : InfinitePlace F) :
    (γ • P) w = sigma F γ w • P w := rfl

/-! ### Topology and measure -/

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.T_Arch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

lemma WX_mk (s : ℂ) (ν : F) (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ}
    (hv : ∀ w, 0 < v w) : WX s ν (X.mk x v hv) = Winf s ν v := rfl

/-! ### The phase test function -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Def
/-! # WP-G2a, file 3: the series `thetaS` (definition, convergence, continuity, linearity)

`term Φ ν Q = τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` (`Q = (x, v)`), `thetaS Φ Q = Σ_{ν ∈ R∖0} term Φ ν Q`.
Under Theorem E (`ThmE`) the series converges absolutely, uniformly on every set `vOpen n`
(`v ∈ (1/(n+1), n+1)^r`, any `x`), together with every polynomial weight `∏_w (1+|ν|_w)^p`;
`thetaS Φ` is continuous on `X F`, additive in `Φ` and homogeneous for `smulFun`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

omit [IsTotallyComplex F] in
lemma vOpen_subset_vBox {n : ℕ} {Q : X F} (hQ : Q ∈ vOpen F n) : Q.v ∈ vBox F n :=
  fun w => ⟨(hQ w).1.le, (hQ w).2.le⟩

omit [IsTotallyComplex F] in
lemma exists_mem_vOpen (Q : X F) : ∃ n : ℕ, Q ∈ vOpen F n := by
  obtain ⟨n, hn⟩ := exists_nat_ge
    (∑ w : InfinitePlace F, (Q.v w + (Q.v w)⁻¹))
  refine ⟨n, fun w => ?_⟩
  have hpos := Q.v_pos w
  have hle : Q.v w + (Q.v w)⁻¹ ≤ n :=
    (Finset.single_le_sum (f := fun w => Q.v w + (Q.v w)⁻¹)
      (fun w _ => add_nonneg (Q.v_pos w).le (inv_nonneg.mpr (Q.v_pos w).le))
      (Finset.mem_univ w)).trans hn
  have hinv : 0 < (Q.v w)⁻¹ := inv_pos.mpr hpos
  constructor
  · rw [one_div, inv_lt_comm₀ (by positivity) hpos]
    linarith
  · linarith

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.K_Weyl
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatComplexH3Vol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-K, file 4: the Weyl flip on `H³ = SL₂(ℂ)/SU(2)`, and Fourier terms

Model: WP-X's `ArtinKP.X.H3 = {(x, v) : ℂ × ℝ | 0 < v}` with its `SL(2,ℂ)`-action; a right
`SU(2)`-invariant function on `SL₂(ℂ)` is `g ↦ f (g • j0)`, `j0 = (0, 1)`.

For `g = n(x) a(y)` (`a(y) = diag(y, y⁻¹)`, `y ∈ ℂˣ`), the two curves through `g • j0 = (x, |y|²)`
* `ζ ↦ g n(ζ) • j0 = (x + y² ζ, |y|²)`                               (`curveN`, `orbit_N`),
* `ζ ↦ g w n(ζ) • j0 = (x − y² ζ̄/(1+|ζ|²), |y|²/(1+|ζ|²))`           (`curveW`, `orbit_W`)
have Wirtinger derivatives at `ζ = 0` related by

  `∂_ζ (f ∘ curveW) = −∂_ζ̄ (f ∘ curveN)`,  `∂_ζ̄ (f ∘ curveW) = −∂_ζ (f ∘ curveN)`   (`weyl_flip`):

right translation by `w` exchanges the derivatives of weight `+1` and `−1` along `n(ζ)`, up to
the sign `−1` (MATH §4.5 "Weyl element"; `Ad(w) X_ζ = Y_{−ζ} ≡ X_{−ζ̄}` mod `𝔰𝔲(2)`).
On a Fourier term `f(x, v) = e(Tr νx) W(v)`: `∂_ζ (f ∘ curveN) = 2πi ν y² f`,
`∂_ζ̄ (f ∘ curveN) = 2πi conj(ν y²) f` (`dz_fourierTerm_curveN`), hence
`∂_ζ (f ∘ curveW) = −2πi conj(ν y²) f`, `∂_ζ̄ (f ∘ curveW) = −2πi ν y² f` (`weyl_flip_fourierTerm`).
-/

open scoped MatrixGroups ComplexConjugate

namespace ArtinKP.K

open ArtinKP.X

noncomputable section

/-! ## Matrices and orbits -/

theorem smul_nMat (x : ℂ) (P : H3) : nMat x • P = H3.mk (P.x + x) P.v P.v_pos := by
  apply H3.ext
  · rw [X.smul_x]
    simp [H3.rowNum, den, H3.rowDen]
  · rw [X.smul_v]
    simp [den, H3.rowDen]

theorem smul_aMat (y : ℂˣ) (P : H3) :
    aMat y • P = H3.mk ((y : ℂ) ^ 2 * P.x) (‖(y : ℂ)‖ ^ 2 * P.v)
      (mul_pos (by have := norm_pos_iff.2 y.ne_zero; positivity) P.v_pos) := by
  have hy : (y : ℂ) ≠ 0 := y.ne_zero
  have hn : Complex.normSq (y : ℂ) ≠ 0 := (Complex.normSq_pos.2 hy).ne'
  apply H3.ext
  · have h : ((Complex.normSq (y : ℂ) : ℝ) : ℂ) = (y : ℂ) * conj (y : ℂ) := (Complex.mul_conj _).symm
    have hc : conj (y : ℂ) ≠ 0 := (map_ne_zero _).2 hy
    rw [X.smul_x]
    simp [H3.rowNum, den, H3.rowDen, h]
    field_simp
  · rw [X.smul_v]
    simp [den, H3.rowDen, Complex.sq_norm]
    field_simp

theorem smul_nbarMat_j0 (η : ℂ) :
    nbarMat η • j0 = H3.mk (conj η * (((1 + ‖η‖ ^ 2)⁻¹ : ℝ) : ℂ)) (1 * (1 + ‖η‖ ^ 2)⁻¹)
      (by positivity) := by
  apply H3.ext
  · rw [X.smul_x]
    simp [H3.rowNum, den, H3.rowDen, j0, Complex.sq_norm, div_eq_mul_inv]
  · rw [X.smul_v]
    simp [den, H3.rowDen, j0, Complex.sq_norm, div_eq_mul_inv]

theorem smul_wMat_j0 : wMat • j0 = j0 := by
  apply H3.ext
  · rw [X.smul_x]
    simp [H3.rowNum, den, H3.rowDen, j0]
  · rw [X.smul_v]
    simp [den, H3.rowDen, j0]

theorem wMat_mul_nMat (ζ : ℂ) : wMat * nMat ζ = nbarMat (-ζ) * wMat := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_nMat, coe_nbarMat, coe_wMat]
  simp

theorem orbit_N (x : ℂ) (y : ℂˣ) (ζ : ℂ) :
    ((nMat x * aMat y * nMat ζ) • j0).1 = curveN x y ζ := by
  rw [mul_smul, mul_smul, smul_nMat, smul_aMat, smul_nMat]
  simp [curveN, j0, H3.mk, H3.x, H3.v, add_comm]

theorem orbit_W (x : ℂ) (y : ℂˣ) (ζ : ℂ) :
    ((nMat x * aMat y * wMat * nMat ζ) • j0).1 = curveW x y ζ := by
  rw [mul_assoc (nMat x * aMat y), wMat_mul_nMat, mul_smul, mul_smul, mul_smul, smul_wMat_j0,
    smul_nbarMat_j0, smul_aMat, smul_nMat]
  simp only [curveW, H3.mk, H3.x, H3.v, map_neg, norm_neg]
  refine Prod.ext ?_ ?_
  · simp only; ring
  · simp only; ring

/-! ## Wirtinger derivatives and the flip -/

/-! ## Fourier terms -/

/-! ## The Whittaker function at `s = 4/3` and the profile `κ` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.G2a_Dx
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-G2a, file 8: the mixed first `x`-derivative `∂_m` and Fourier series

`∂^{(+1)} = ∂_x`, `∂^{(−1)} = ∂_x̄` (Wirtinger, `K.dz`, `K.dzbar`) in one coordinate `x_w` of
`x : InfinitePlace F → ℂ`; `∂_m = ∏_w ∂^{(m_w)}_{x_w}` (MATH3 §0), defined by iterating over a
list of places.

* `Dw m w f`: the Wirtinger derivative of type `m` in the `w`-th coordinate.
* `DList m l f`: iteration over the list `l`; `Dm m f := DList m Finset.univ.toList f`.
* **`DList_series`**: for a Fourier series `Σ_i c_i e_∞(ν_i x)` whose coefficients are summable
  against every power of `1 + ‖ν_i‖`, `DList m l` acts termwise:
  the `i`-th term is multiplied by `∏_{w ∈ l} (−2πi · ν_{i,w}^{(m_w)})`.
-/

open scoped ComplexConjugate Topology
open NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B

noncomputable section

/-! ### One complex variable -/

lemma linA_apply (a h : ℂ) : linA a h = 2 * Real.pi * Complex.I * (a * h + conj (a * h)) := by
  simp [linA]
  ring

lemma archChar_eq_exp_linA (a ζ : ℂ) : archChar (a * ζ) = Complex.exp (linA a ζ) := by
  rw [archChar, linA_apply]

lemma norm_linA_le (a : ℂ) : ‖linA a‖ ≤ 4 * Real.pi * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [linA_apply, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have : ‖a * h + conj (a * h)‖ ≤ 2 * (‖a‖ * ‖h‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [RCLike.norm_conj, norm_mul]
    linarith
  nlinarith [Real.pi_pos]

lemma hasFDerivAt_archChar (a b ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => archChar (a * (ζ - b))) (archChar (a * (ζ - b)) • linA a) ζ := by
  have h1 : HasFDerivAt (fun ζ : ℂ => linA a (ζ - b))
      ((linA a).comp (ContinuousLinearMap.id ℝ ℂ)) ζ :=
    (linA a).hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).sub_const b)
  rw [ContinuousLinearMap.comp_id] at h1
  have h2 := h1.cexp
  simp only [← archChar_eq_exp_linA] at h2
  exact h2

lemma dz_eq (φ : ℂ → ℂ) (ζ : ℂ) : dz φ ζ = dzL (fderiv ℝ φ ζ) := by simp [dz, dzL]

lemma dzbar_eq (φ : ℂ → ℂ) (ζ : ℂ) : dzbar φ ζ = dzbarL (fderiv ℝ φ ζ) := by
  simp [dzbar, dzbarL]
  ring

lemma dzL_smul_linA (t a : ℂ) : dzL (t • linA a) = t * (2 * Real.pi * Complex.I * a) := by
  simp only [dzL, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
    ContinuousLinearMap.apply_apply, linA_apply, smul_eq_mul, mul_one, map_mul, Complex.conj_I]
  linear_combination (-(t * Real.pi * Complex.I * (a - conj a))) * Complex.I_sq

lemma dzbarL_smul_linA (t a : ℂ) :
    dzbarL (t • linA a) = t * (2 * Real.pi * Complex.I * conj a) := by
  simp only [dzbarL, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
    ContinuousLinearMap.apply_apply, linA_apply, smul_eq_mul, mul_one, map_mul, Complex.conj_I]
  linear_combination (t * Real.pi * Complex.I * (a - conj a)) * Complex.I_sq

lemma norm_cj (m : ℤ) (z : ℂ) : ‖cj m z‖ = ‖z‖ := by
  unfold cj; split_ifs <;> simp

/-! ### Several variables -/

variable {W : Type*} [Fintype W] [DecidableEq W]

lemma norm_eW (ν x : W → ℂ) : ‖eW ν x‖ = 1 := by
  simp only [eW, norm_prod, archChar_norm, Finset.prod_const_one]

lemma eW_update (ν x : W → ℂ) (w : W) (ζ : ℂ) :
    eW ν (Function.update x w ζ) = eW ν x * archChar (-(ν w) * (ζ - x w)) := by
  unfold eW
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), ← Finset.mul_prod_erase _
    (fun w' => archChar (-(ν w' * x w'))) (Finset.mem_univ w), Function.update_self]
  have h : ∏ w' ∈ Finset.univ.erase w, archChar (-(ν w' * Function.update x w ζ w'))
      = ∏ w' ∈ Finset.univ.erase w, archChar (-(ν w' * x w')) :=
    Finset.prod_congr rfl fun w' hw' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  rw [h, show -(ν w * ζ) = -(ν w * x w) + -(ν w) * (ζ - x w) by ring, archChar_add]
  ring

variable {I : Type*}

/-- **One step**: the derivative of a Fourier series in one coordinate, termwise. -/
theorem Dw_series (c : I → ℂ) (ν : I → W → ℂ)
    (hs : Summable fun i => ‖c i‖ * (1 + ‖ν i‖)) (m : ℤ) (w : W) (x : W → ℂ) :
    Dw m w (fun x => ∑' i, c i * eW (ν i) x) x =
      ∑' i, c i * (-(2 * Real.pi * Complex.I) * cj m (ν i w)) * eW (ν i) x := by
  set f : I → ℂ → ℂ := fun i ζ => c i * eW (ν i) (Function.update x w ζ) with hf
  set f' : I → ℂ → (ℂ →L[ℝ] ℂ) := fun i ζ =>
    (c i * (eW (ν i) x * archChar (-(ν i w) * (ζ - x w)))) • linA (-(ν i w)) with hf'
  have hd : ∀ i ζ, HasFDerivAt (f i) (f' i ζ) ζ := by
    intro i ζ
    have e : f i = fun ζ => (c i * eW (ν i) x) * archChar (-(ν i w) * (ζ - x w)) := by
      funext ζ; simp only [hf, eW_update]; ring
    rw [e]
    have := (hasFDerivAt_archChar (-(ν i w)) (x w) ζ).const_mul (c i * eW (ν i) x)
    simpa only [hf', smul_smul, mul_assoc] using this
  set u : I → ℝ := fun i => 4 * Real.pi * (‖c i‖ * (1 + ‖ν i‖)) with hu
  have hus : Summable u := hs.mul_left _
  have hb : ∀ i ζ, ‖f' i ζ‖ ≤ u i := by
    intro i ζ
    rw [norm_smul, norm_mul, norm_mul, norm_eW, archChar_norm, mul_one, mul_one]
    have h1 := norm_linA_le (-(ν i w))
    rw [norm_neg] at h1
    have h2 : ‖ν i w‖ ≤ 1 + ‖ν i‖ := (norm_le_pi_norm (ν i) w).trans (by linarith)
    calc ‖c i‖ * ‖linA (-(ν i w))‖ ≤ ‖c i‖ * (4 * Real.pi * (1 + ‖ν i‖)) :=
          mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (norm_nonneg _)
      _ = u i := by rw [hu]; ring
  have h0 : Summable fun i => f i (x w) := by
    refine Summable.of_norm_bounded hs fun i => ?_
    rw [hf, norm_mul, norm_eW, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg (ν i)])
  have H := hasFDerivAt_tsum hus hd hb h0 (x w)
  have hsL : Summable fun i => f' i (x w) := Summable.of_norm_bounded hus fun i => hb i (x w)
  have hval : ∀ i, f' i (x w) = (c i * eW (ν i) x) • linA (-(ν i w)) := fun i => by
    simp only [hf', sub_self, mul_zero]
    rw [show archChar 0 = 1 by simp [archChar], mul_one]
  have hfun : (fun ζ => (fun x => ∑' i, c i * eW (ν i) x) (Function.update x w ζ))
      = fun ζ => ∑' i, f i ζ := rfl
  unfold Dw
  split_ifs with hm
  · rw [hfun, dz_eq, H.fderiv, ← (hsL.hasSum.mapL dzL).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hval, dzL_smul_linA, cj, if_pos hm]
    ring
  · rw [hfun, dzbar_eq, H.fderiv, ← (hsL.hasSum.mapL dzbarL).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hval, dzbarL_smul_linA, cj, if_neg hm, map_neg]
    ring

lemma eig_nil (m : W → ℤ) (ν : W → ℂ) : eig m [] ν = 1 := rfl

lemma eig_cons (m : W → ℤ) (w : W) (l : List W) (ν : W → ℂ) :
    eig m (w :: l) ν = -(2 * Real.pi * Complex.I) * cj (m w) (ν w) * eig m l ν := by
  simp [eig]

lemma norm_eig_le (m : W → ℤ) (l : List W) (ν : W → ℂ) :
    ‖eig m l ν‖ ≤ (2 * Real.pi * (1 + ‖ν‖)) ^ l.length := by
  induction l with
  | nil => simp [eig]
  | cons w l ih =>
    rw [eig_cons, norm_mul, List.length_cons, pow_succ']
    refine mul_le_mul ?_ ih (norm_nonneg _) (by positivity)
    rw [norm_mul, norm_neg, norm_cj, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm ν w).trans (by linarith)) (by positivity)

lemma eig_univ (m : W → ℤ) (ν : W → ℂ) :
    eig m Finset.univ.toList ν = ∏ w, (-(2 * Real.pi * Complex.I) * cj (m w) (ν w)) := by
  rw [eig, Finset.prod_map_toList]

/-- **Termwise action of the iterated Wirtinger derivatives on a Fourier series.** -/
theorem DList_series (m : W → ℤ) (l : List W) (c : I → ℂ) (ν : I → W → ℂ)
    (hs : ∀ p : ℕ, Summable fun i => ‖c i‖ * (1 + ‖ν i‖) ^ p) :
    DList m l (fun x => ∑' i, c i * eW (ν i) x) =
      fun x => ∑' i, c i * eig m l (ν i) * eW (ν i) x := by
  induction l with
  | nil => funext x; simp [DList, eig_nil]
  | cons w l ih =>
    funext x
    have hs' : Summable fun i => ‖c i * eig m l (ν i)‖ * (1 + ‖ν i‖) := by
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        ((hs (l.length + 1)).mul_left ((2 * Real.pi) ^ l.length))
      rw [norm_mul]
      have h1 := norm_eig_le m l (ν i)
      have h0 : (0 : ℝ) ≤ 1 + ‖ν i‖ := by positivity
      calc ‖c i‖ * ‖eig m l (ν i)‖ * (1 + ‖ν i‖)
          ≤ ‖c i‖ * (2 * Real.pi * (1 + ‖ν i‖)) ^ l.length * (1 + ‖ν i‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h0
        _ = (2 * Real.pi) ^ l.length * (‖c i‖ * (1 + ‖ν i‖) ^ (l.length + 1)) := by
            rw [mul_pow, pow_succ]; ring
    show Dw (m w) w (DList m l fun x => ∑' i, c i * eW (ν i) x) x = _
    rw [ih, Dw_series (fun i => c i * eig m l (ν i)) ν hs' (m w) w x]
    refine tsum_congr fun i => ?_
    rw [eig_cons]
    ring

/-! ### Constants are killed -/

omit [Fintype W] in
lemma Dw_const_add (m : ℤ) (w : W) (C : ℂ) (g : (W → ℂ) → ℂ) :
    Dw m w (fun x => C + g x) = Dw m w g := by
  funext x
  simp only [Dw, dz, dzbar, fderiv_const_add]

omit [Fintype W] in
/-- A constant added to the function does not change `DList m l`, `l ≠ []`. -/
lemma DList_const_add (m : W → ℤ) (l : List W) (hl : l ≠ []) (C : ℂ) (g : (W → ℂ) → ℂ) :
    DList m l (fun x => C + g x) = DList m l g := by
  induction l with
  | nil => exact absurd rfl hl
  | cons w l ih =>
    by_cases h : l = []
    · subst h
      exact Dw_const_add (m w) w C g
    · show Dw (m w) w (DList m l fun x => C + g x) = Dw (m w) w (DList m l g)
      rw [ih h]

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Fwd
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 9: `∂_m θ̃_Φ` termwise and the forward field (MATH3 §1.1)

* `thetaX Φ v hv x = θ̃_Φ(x, v)` as a function of `x` at fixed height `v`.
* **`Dm_thetaX`**: `∂_m θ̃_Φ(·, v)` is the termwise series; the constant term is killed and the
  `ν`-th term is multiplied by `∏_w (−2πi·ν_w^{(m_w)})`.
* `ThetaM m Φ X Y := ∏_w Y_w^{(m_w)} · (∂_m θ̃_Φ)(X, |Y|)` (MATH3's `Θ_m^Φ(X, Y)`).
* `place_kappaB`: `(νY)^{(m)}·jacquet (4/3) (−ν) |Y| = C0·|ν|^{−2/3}·ω_m(νY)·κ(|νY|²)`,
  `κ = K.kappaB (4π)`, `C0 = (2π)^{4/3}/Γ(4/3)`.
* **`ThetaM_tau`**: the expansion with coefficient `τ_Φ(ν)` (no Theorem E beyond convergence);
* **`ThetaM_forward`** = MATH3 (1.1):
  `Θ_m^Φ(X,Y) = kapC·C_a^r·Σ_ν coef^S(ν)·ξ_Φ(ν)·e_∞(νX)·∏_w ω_{m_w}(ν_wY_w)·κ(|ν_wY_w|²)`,
  `C_a = −2πi·C0`, with `summable_forward`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

/-! ### One place -/

lemma cj_mul (m : ℤ) (a b : ℂ) : cj m (a * b) = cj m a * cj m b := by
  unfold cj; split_ifs <;> simp

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

lemma eW_emb (ν : F) (x : InfinitePlace F → ℂ) : eW (emb ν) x = eInf (emb ν * x) := rfl

lemma thetaX_eq (Φ : GSection ι P 𝔪) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    thetaX hG hz6 Φ v hv = fun x => zc hG hz6 Φ * htC (2 / 3) (X.mk 0 v hv) +
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        (kapC F * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v)) *
          eW (emb ((ν : SInt 𝔪) : F)) x := by
  funext x
  unfold thetaX thetaT thetaS
  rw [← tsum_mul_left]
  congr 1
  refine tsum_congr fun ν => ?_
  rw [eW_emb]
  simp only [term, X.x_mk, T.WX_mk]
  ring

omit [IsTotallyComplex F] in
lemma one_add_norm_emb_le (ν : F) :
    1 + ‖(emb ν : InfinitePlace F → ℂ)‖ ≤ ∏ w : InfinitePlace F, (1 + w ν) := by
  have h1 : (1 : ℝ) ≤ ∏ w : InfinitePlace F, (1 + w ν) := by
    calc (1 : ℝ) = ∏ _w : InfinitePlace F, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
        fun w _ => by linarith [apply_nonneg w ν]
  have h2 : ‖(emb ν : InfinitePlace F → ℂ)‖ ≤ ∏ w : InfinitePlace F, (1 + w ν) - 1 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro w
    rw [emb_apply, InfinitePlace.norm_embedding_eq]
    have : (1 + w ν) = ∏ w' : InfinitePlace F, (if w' = w then 1 + w ν else 1) := by
      rw [Finset.prod_ite_eq' Finset.univ w, if_pos (Finset.mem_univ w)]
    have h3 : 1 + w ν ≤ ∏ w' : InfinitePlace F, (1 + w' ν) := by
      rw [this]
      refine Finset.prod_le_prod (fun w' _ => by split_ifs <;> positivity) fun w' _ => ?_
      split_ifs with h
      · rw [h]
      · linarith [apply_nonneg w' ν]
    linarith
  linarith

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- The coefficients of `θ̃_Φ(·, v)` are summable against every power of `1 + ‖ν‖`. -/
theorem summable_coef_pow (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (p : ℕ) :
    Summable fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      ‖kapC F * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v)‖ *
        (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) ^ p := by
  obtain ⟨n₀, hn₀⟩ := exists_mem_vOpen (X.mk 0 v hv)
  have hvb : v ∈ vBox F n₀ := vOpen_subset_vBox hn₀
  obtain ⟨u, hu, -, hle⟩ := exists_major hE Φ p n₀
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) (hu.mul_left ‖kapC F‖)
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (hle ν v hvb)
  rw [mul_comm, Finset.prod_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (one_add_norm_emb_le _) p) (norm_nonneg _)

/-- **`∂_m θ̃_Φ(·, v)`, termwise.** -/
theorem Dm_thetaX (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    Dm m (thetaX hG hz6 Φ v hv) x = kapC F * ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
      T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v *
        (∏ w : InfinitePlace F, (-(2 * Real.pi * Complex.I) *
          cj (m w) (w.embedding ((ν : SInt 𝔪) : F)))) * eInf (emb ((ν : SInt 𝔪) : F) * x) := by
  have hne : (Finset.univ : Finset (InfinitePlace F)).toList ≠ [] := by
    rw [ne_eq, Finset.toList_eq_nil]
    exact Finset.univ_nonempty.ne_empty
  rw [thetaX_eq, Dm, DList_const_add m _ hne,
    DList_series m _ _ _ (summable_coef_pow hE Φ v hv), ← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [eig_univ, eW_emb]
  simp only [emb_apply]
  ring

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.GR_Flip
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-GR, file 2: MATH3 (2.3) — cusp change and Weyl flip for `Θ_m^Φ`

* `Dm_thetaX_affine`: the chain rule `∂_m[ζ ↦ θ̃_Φ(X₀ + Aζ, v)]_{ζ=0} = ∏_w A_w^{(m_w)}·(∂_m θ̃_Φ)(X₀, v)`
  (termwise on the Fourier series, `G2a.DList_series`).
* `orbit_cusp`: `γ·n(ξ)a(y)n(ζ)·j = n(a/c)·a(1/(cy))·w·n(ζ)·j` for `ξ = −d/c` (the K-part is
  exactly `w`); `smul_curveN`: the same on `X F`, in the coordinates `K.curveN`, `K.curveW`.
* `WeylFlip P hG hz6`: **named hypothesis** = the statement of the stub `G2a.weyl_flip_thetaT`
  (owner WP-GW), for all `m` with values `±1`.
* **`ThetaM_flip`** = MATH3 (2.3):
  `Θ_m^Φ(emb ξ, y²) = (−1)^r · Θ_{−m}^{γΦ}(emb(a/c), 1/(cy)²)`, `γΦ = translate γ Φ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

/-! ### One place: the orbit identity -/

lemma neg_smul_H3 (g : SL(2, ℂ)) (Q : H3) : (-g) • Q = g • Q := by
  apply H3.ext
  · rw [X.smul_x, X.smul_x]
    have h : ∀ z : ℂ, Complex.normSq (-z) = Complex.normSq z := Complex.normSq_neg
    simp only [H3.rowNum, den, H3.rowDen, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
      map_neg, h, neg_mul, ← neg_add]
    ring
  · rw [X.smul_v, X.smul_v]
    have h : ∀ z : ℂ, Complex.normSq (-z) = Complex.normSq z := Complex.normSq_neg
    simp only [den, H3.rowDen, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, h, neg_mul,
      ← neg_add]

/-- `γ·n(ξ)·a(y) = −n(a/c)·a(1/(cy))·w` for `ξ = −d/c`. -/
lemma mat_cusp (g : SL(2, ℂ)) {c : ℂ} (hc : c ≠ 0) (hg : g 1 0 = c) (y : ℂˣ) :
    g * K.nMat (-(g 1 1) / c) * K.aMat y =
      -(K.nMat (g 0 0 / c) * K.aMat ((Units.mk0 c hc * y)⁻¹) * K.wMat) := by
  have hdet := X.det_eq g
  have hy : (y : ℂ) ≠ 0 := y.ne_zero
  rw [hg] at hdet
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_neg]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_nMat, coe_aMat, K.coe_wMat]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    linear_combination -hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hg]
    try field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hg]
    try field_simp
    try ring

/-- **The orbit identity**: `γ·n(ξ)a(y)n(ζ)·j = n(a/c)·a(1/(cy))·w·n(ζ)·j`, `ξ = −d/c`. -/
lemma orbit_cusp (g : SL(2, ℂ)) {c : ℂ} (hc : c ≠ 0) (hg : g 1 0 = c) (y : ℂˣ) (ζ : ℂ) :
    g • ((K.nMat (-(g 1 1) / c) * K.aMat y * K.nMat ζ) • j0) =
      (K.nMat (g 0 0 / c) * K.aMat ((Units.mk0 c hc * y)⁻¹) * K.wMat * K.nMat ζ) • j0 := by
  rw [← mul_smul, ← mul_assoc, ← mul_assoc, mat_cusp g hc hg y, neg_mul, neg_smul_H3]

lemma H3_curveN (x : ℂ) {y : ℂ} (hy : y ≠ 0) (ζ : ℂ) :
    H3.mk (curveN x y ζ).1 (curveN x y ζ).2 (curveN_pos x hy ζ) =
      (K.nMat x * K.aMat (Units.mk0 y hy) * K.nMat ζ) • j0 :=
  Subtype.ext (orbit_N x (Units.mk0 y hy) ζ).symm

lemma H3_curveW (x : ℂ) {y : ℂ} (hy : y ≠ 0) (ζ : ℂ) :
    H3.mk (curveW x y ζ).1 (curveW x y ζ).2 (curveW_pos x hy ζ) =
      (K.nMat x * K.aMat (Units.mk0 y hy) * K.wMat * K.nMat ζ) • j0 :=
  Subtype.ext (orbit_W x (Units.mk0 y hy) ζ).symm

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The cusp change on `X F` in curve coordinates: for `γ = [[a,b],[c,d]] ∈ SL₂(R)`, `c ≠ 0`,
`γ • (curveN (−d/c) y ζ) = curveW (a/c) (1/(cy)) ζ` at every place. -/
theorem smul_curveN (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
    (y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) (ζ : InfinitePlace F → ℂ) :
    toF 𝔪 γ • (X.mk
        (fun w => (curveN (emb (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) w)
          (y w) (ζ w)).1)
        (fun w => (curveN (emb (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) w)
          (y w) (ζ w)).2)
        (fun w => curveN_pos _ (hy w) _) : X F) =
      X.mk
        (fun w => (curveW (emb (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) w)
          ((w.embedding ((γ.1 1 0 : SInt 𝔪) : F) * y w)⁻¹) (ζ w)).1)
        (fun w => (curveW (emb (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) w)
          ((w.embedding ((γ.1 1 0 : SInt 𝔪) : F) * y w)⁻¹) (ζ w)).2)
        (fun w => curveW_pos _
          (inv_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (hy w))) _) := by
  funext w
  have hcw : w.embedding ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0 := (map_ne_zero _).mpr hc
  rw [X.smul_apply]
  show sigma F (toF 𝔪 γ) w • H3.mk _ _ (curveN_pos _ (hy w) _) = H3.mk _ _ (curveW_pos _
    (inv_ne_zero (mul_ne_zero hcw (hy w))) _)
  rw [H3_curveN _ (hy w), H3_curveW _ (inv_ne_zero (mul_ne_zero hcw (hy w)))]
  have h10 : (sigma F (toF 𝔪 γ) w) 1 0 = w.embedding ((γ.1 1 0 : SInt 𝔪) : F) := rfl
  have h11 : (sigma F (toF 𝔪 γ) w) 1 1 = w.embedding ((γ.1 1 1 : SInt 𝔪) : F) := rfl
  have h00 : (sigma F (toF 𝔪 γ) w) 0 0 = w.embedding ((γ.1 0 0 : SInt 𝔪) : F) := rfl
  have h := orbit_cusp (sigma F (toF 𝔪 γ) w) hcw h10 (Units.mk0 (y w) (hy w)) (ζ w)
  rw [h11, h00] at h
  have e1 : emb (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) w =
      -(w.embedding ((γ.1 1 1 : SInt 𝔪) : F)) / w.embedding ((γ.1 1 0 : SInt 𝔪) : F) := by
    rw [emb_apply, map_div₀, map_neg]
  have e2 : emb (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) w =
      w.embedding ((γ.1 0 0 : SInt 𝔪) : F) / w.embedding ((γ.1 1 0 : SInt 𝔪) : F) := by
    rw [emb_apply, map_div₀]
  rw [e1, e2, h]
  congr 4
  congr 1
  apply Units.ext
  simp

variable [IsTotallyComplex F] {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### The chain rule along an affine map -/

lemma eW_affine {W : Type*} [Fintype W] (ν X₀ A ζ : W → ℂ) :
    eW ν (fun w => X₀ w + A w * ζ w) = eW ν X₀ * eW (fun w => ν w * A w) ζ := by
  unfold eW
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_add]
  congr 1
  ring

lemma eW_zero {W : Type*} [Fintype W] (ν : W → ℂ) : eW ν 0 = 1 := by
  simp [eW, archChar]

lemma norm_mul_pi_le {W : Type*} [Fintype W] (a b : W → ℂ) :
    ‖fun w => a w * b w‖ ≤ ‖a‖ * ‖b‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro w
  rw [norm_mul]
  exact mul_le_mul (norm_le_pi_norm a w) (norm_le_pi_norm b w) (norm_nonneg _) (norm_nonneg _)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- **Chain rule** for `∂_m` of `θ̃_Φ(·, v)` along `ζ ↦ X₀ + A·ζ` (coordinatewise), at `ζ = 0`. -/
theorem Dm_thetaX_affine (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (X₀ A : InfinitePlace F → ℂ) :
    Dm m (fun ζ : InfinitePlace F → ℂ => thetaX hG hz6 Φ v hv (fun w => X₀ w + A w * ζ w)) 0 =
      (∏ w, cj (m w) (A w)) * Dm m (thetaX hG hz6 Φ v hv) X₀ := by
  have hne : (Finset.univ : Finset (InfinitePlace F)).toList ≠ [] := by
    rw [ne_eq, Finset.toList_eq_nil]
    exact Finset.univ_nonempty.ne_empty
  set c : {ν : SInt 𝔪 // ν ≠ 0} → ℂ := fun ν =>
    kapC F * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v) with hc
  have hfun : (fun ζ : InfinitePlace F → ℂ =>
      thetaX hG hz6 Φ v hv (fun w => X₀ w + A w * ζ w)) =
      fun ζ => zc hG hz6 Φ * htC (2 / 3) (X.mk 0 v hv) +
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, (c ν * eW (emb ((ν : SInt 𝔪) : F)) X₀) *
          eW (fun w => emb ((ν : SInt 𝔪) : F) w * A w) ζ := by
    funext ζ
    rw [thetaX_eq hG hz6 Φ v hv]
    refine congrArg₂ (· + ·) rfl (tsum_congr fun ν => ?_)
    rw [eW_affine]
    ring
  have hs : ∀ p : ℕ, Summable fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
      ‖c ν * eW (emb ((ν : SInt 𝔪) : F)) X₀‖ *
        (1 + ‖fun w => emb ((ν : SInt 𝔪) : F) w * A w‖) ^ p := by
    intro p
    refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
      ((summable_coef_pow hE Φ v hv p).mul_left ((1 + ‖A‖) ^ p))
    rw [norm_mul, norm_eW, mul_one]
    have h1 : 1 + ‖fun w => emb ((ν : SInt 𝔪) : F) w * A w‖ ≤
        (1 + ‖A‖) * (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖) := by
      have := norm_mul_pi_le (emb ((ν : SInt 𝔪) : F)) A
      nlinarith [norm_nonneg A, norm_nonneg (emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)]
    calc ‖c ν‖ * (1 + ‖fun w => emb ((ν : SInt 𝔪) : F) w * A w‖) ^ p
        ≤ ‖c ν‖ * ((1 + ‖A‖) * (1 + ‖(emb ((ν : SInt 𝔪) : F) : InfinitePlace F → ℂ)‖)) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) (norm_nonneg _)
      _ = _ := by rw [mul_pow]; ring
  rw [Dm_thetaX hE, hfun]
  unfold Dm
  rw [DList_const_add m _ hne, DList_series m _ _ _ hs]
  simp only [eW_zero, mul_one]
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [eig_univ, eW_emb]
  have hp : ∏ w : InfinitePlace F, (-(2 * Real.pi * Complex.I) *
      cj (m w) (emb ((ν : SInt 𝔪) : F) w * A w)) =
      (∏ w, cj (m w) (A w)) * ∏ w : InfinitePlace F, (-(2 * Real.pi * Complex.I) *
        cj (m w) (w.embedding ((ν : SInt 𝔪) : F))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [cj_mul, emb_apply]
    ring
  rw [hp, hc]
  ring

/-! ### The Weyl flip (named hypothesis) and MATH3 (2.3) -/

variable (hG hz6 P)

variable {hG hz6 P}

lemma thetaT_mk_congr (Φ : GSection ι P 𝔪) {x x' : InfinitePlace F → ℂ}
    {v v' : InfinitePlace F → ℝ} (hx : x = x') (hvv : v = v') (hv : ∀ w, 0 < v w)
    (hv' : ∀ w, 0 < v' w) :
    thetaT hG hz6 Φ (X.mk x v hv) = thetaT hG hz6 Φ (X.mk x' v' hv') := by
  subst hx; subst hvv; rfl

/-- `Θ_m^Φ(X₀, y²)` as the `ζ`-derivative at `0` along `K.curveN X₀ y`. -/
theorem ThetaM_eq_curveN (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (X₀ y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) :
    ThetaM hG hz6 m Φ X₀ (fun w => y w ^ 2) (fun w => pow_ne_zero 2 (hy w)) =
      Dm m (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Φ
        (X.mk (fun w => (curveN (X₀ w) (y w) (ζ w)).1) (fun w => (curveN (X₀ w) (y w) (ζ w)).2)
          (fun w => curveN_pos (X₀ w) (hy w) (ζ w)))) 0 := by
  rw [ThetaM, ← Dm_thetaX_affine hE]
  refine congrArg (fun f : (InfinitePlace F → ℂ) → ℂ => Dm m f 0) ?_
  funext ζ
  unfold thetaX
  refine thetaT_mk_congr Φ ?_ ?_ _ _
  · funext w; simp [curveN]
  · funext w; simp [curveN]

/-- **MATH3 (2.3).** For `γ = [[a,b],[c,d]] ∈ SL₂(R)`, `c ≠ 0`, `ξ = −d/c`, and `y_w ≠ 0`:
`Θ_m^Φ(emb ξ, y²) = (−1)^r · Θ_{−m}^{γΦ}(emb(a/c), (cy)⁻²)`. -/
theorem ThetaM_flip_oai (hE : ThmE hG hz6 g P)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (hW : WeylFlip (ι := ι) P hG hz6) (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1)
    (Φ : GSection ι P 𝔪) (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
    (y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0) :
    ThetaM hG hz6 m Φ (emb (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
        (fun w => y w ^ 2) (fun w => pow_ne_zero 2 (hy w)) =
      (-1) ^ Fintype.card (InfinitePlace F) *
        ThetaM hG hz6 (fun w => -m w) (S2.GSection.translate hG γ Φ)
          (emb (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
          (fun w => ((w.embedding ((γ.1 1 0 : SInt 𝔪) : F) * y w)⁻¹) ^ 2)
          (fun w => pow_ne_zero 2
            (inv_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (hy w)))) := by
  have hy' : ∀ w : InfinitePlace F, (w.embedding ((γ.1 1 0 : SInt 𝔪) : F) * y w)⁻¹ ≠ 0 :=
    fun w => inv_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (hy w))
  rw [ThetaM_eq_curveN hE m Φ _ y hy, ThetaM_eq_curveN hE (fun w => -m w) _ _ _ hy',
    ← hW m hm _ _ _ hy']
  refine congrArg (fun f : (InfinitePlace F → ℂ) → ℂ => Dm m f 0) ?_
  funext ζ
  rw [thetaT_translate hE hdiff, ← smul_curveN γ hc y hy ζ, map_inv, inv_smul_smul]

end

end ArtinKP.GR
end

theorem solution.{u_1} : type_of% @ArtinKP.GR.ThetaM_flip_oai.{u_1} := @ArtinKP.GR.ThetaM_flip_oai.{u_1}
