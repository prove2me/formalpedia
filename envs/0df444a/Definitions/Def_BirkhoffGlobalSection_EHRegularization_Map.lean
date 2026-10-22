-- Prove2me | Definitions.Def_BirkhoffGlobalSection_EHRegularization_Map
-- name    : BirkhoffGlobalSection_EHRegularization_Map
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-02T10:38:51.063583+00:00
-- url     : https://prove2.me/theorems/da1ff8dc-b5b7-41e1-aa9c-5247a9100b6e
-- title:
--   Explicit Levi-Civita to elliptic-hyperbolic coordinate change
-- statement:
--   `EHReg.toEH`: $(z,w)\mapsto(\xi,y)$ with $\xi=2\operatorname{arsinh}(-i\sqrt2 z)$, $y=\sqrt2\,\overline{S}(-iw+(\tfrac12-\mu)\bar z)$, $S=\sqrt{1-2z^2}$, and its inverse `fromEH`, on `sourceEH` $=\{2|z|^2<1\}$ and `targetEH` $=\{|x_2|<\pi,|\sinh(\xi/2)|^2<1\}$. Proved: mutual inverses, smoothness, oddness, collision point to collision point; `G_toEH`: $G_{\mu,c}\circ\Phi=2\sqrt{D}\,K_{\mu,c}$; `toEH_symplectic`: $\omega(D\Phi v,D\Phi w)=4\omega(v,w)$; `vectorField_toEH`: $D\Phi\,X_K=(4/2\sqrt D)\,X_G\circ\Phi$ on $\{K=0\}$; `dG_comp_dPhi`.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS2 (elliptic-hyperbolic regularization, Section 9.2); explicit transport to the platform's Levi-Civita normalization constructed and verified here (momentum shift p -> p + (0, 1/2 - mu) between the barycentric rotating frame and the elliptic centre).

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical
import Definitions.Def_BirkhoffGlobalSection_EHRegularization_Analysis
import Definitions.Def_BirkhoffGlobalSection_EHRegularization_Poly

/-! The explicit Levi-Civita → elliptic-hyperbolic coordinate change. -/

namespace BirkhoffGlobalSection

namespace EHReg

open Complex EHArsinh

noncomputable section

/-- Complex position `z = s₀ + i s₁`. -/
def zC (s : Phase) : ℂ := ⟨s 0, s 1⟩

/-- Complex momentum `w = s₂ + i s₃`. -/
def wC (s : Phase) : ℂ := ⟨s 2, s 3⟩

/-- Real coordinates of a pair of complex numbers. -/
def ofC (a b : ℂ) : Phase := ![a.re, a.im, b.re, b.im]

/-- `a = -i √2 z`, so that `sinh (ξ/2) = a`. -/
def aOf (s : Phase) : ℂ := -I * (Real.sqrt 2 : ℂ) * zC s

/-- `S = √(1 + a²) = √(1 - 2 z²) = cosh (ξ/2)`. -/
def SOf (s : Phase) : ℂ := csqrt (1 + aOf s ^ 2)

/-- The coordinate change `(z, w) ↦ (ξ, y)`:
`ξ = 2 arsinh(-i√2 z)`, `y = √2 · conj S · (-i w + (1/2 - μ) z̄)`. -/
def toEH (μ : ℝ) (s : Phase) : Phase :=
  ofC (2 * arsinhC (aOf s))
    ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (SOf s) *
      (-I * wC s + ((1 / 2 - μ : ℝ) : ℂ) * (starRingEnd ℂ) (zC s)))

theorem one_add_aOf_sq (s : Phase) :
    1 + aOf s ^ 2 = ⟨1 - 2 * (s 0 ^ 2 - s 1 ^ 2), -(4 * s 0 * s 1)⟩ := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  apply Complex.ext
  · simp [aOf, zC, sq, mul_re, mul_im]; linear_combination (-(s 0 ^ 2 - s 1 ^ 2)) * h
  · simp [aOf, zC, sq, mul_re, mul_im]; linear_combination (-2 * s 0 * s 1) * h

theorem re_one_add_aOf_sq_pos {s : Phase} (hs : 2 * zNormSq s < 1) :
    0 < (1 + aOf s ^ 2).re := by
  rw [one_add_aOf_sq]; simp only [zNormSq] at hs; nlinarith [sq_nonneg (s 1)]

theorem SOf_sq (s : Phase) : SOf s ^ 2 = 1 + aOf s ^ 2 := csqrt_sq _

/-- The EH Hamiltonian at the transported point is the polynomial `GP`. -/
theorem G_toEH_eq_GP (μ c : ℝ) {s : Phase} (hs : 2 * zNormSq s < 1) :
    ehLeftHamiltonian μ c (toEH μ s) =
      EHPoly.GP (s 0) (s 1) (s 2) (s 3) (SOf s).re (SOf s).im (Real.sqrt 2) μ c := by
  have hw := re_one_add_aOf_sq_pos hs
  set L := arsinhC (aOf s) with hL
  have hsh : sinh L = aOf s := sinh_arsinhC hw
  have hch : cosh L = SOf s := cosh_arsinhC hw
  have hhalf : 2 * L / 2 = L := by ring
  have hA : Real.cosh (2 * L).re = normSq (SOf s) + normSq (aOf s) := by
    have h1 := EHTrig.cosh_add_cos (2 * L)
    have h2 := EHTrig.cosh_sub_cos (2 * L)
    rw [hhalf, hch] at h1; rw [hhalf, hsh] at h2
    linarith
  have hB : Real.cos (2 * L).im = normSq (SOf s) - normSq (aOf s) := by
    have h1 := EHTrig.cosh_add_cos (2 * L)
    have h2 := EHTrig.cosh_sub_cos (2 * L)
    rw [hhalf, hch] at h1; rw [hhalf, hsh] at h2
    linarith
  have hsx : sinh (2 * L) = 2 * aOf s * SOf s := by rw [sinh_two_mul, hsh, hch]
  have hcx : cosh (2 * L) = 2 * SOf s ^ 2 - 1 := by
    rw [cosh_two_mul, hsh, hch, SOf_sq]; ring
  have hC := EHTrig.sinh_two_re (2 * L)
  have hD := EHTrig.sin_two_im (2 * L)
  rw [hsx, hcx] at hC hD
  simp only [ehLeftHamiltonian, toEH, ofC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hA, hB, hC, hD]
  simp only [EHPoly.GP, normSq_apply, mul_re, mul_im, sub_re, sub_im, conj_re, conj_im,
    aOf, zC, wC, neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im, add_re, add_im,
    one_re, one_im, sq, re_ofNat, im_ofNat]
  ring

theorem SOf_re_im (s : Phase) :
    (SOf s).re ^ 2 - (SOf s).im ^ 2 = 1 - 2 * (s 0 ^ 2 - s 1 ^ 2) ∧
      2 * (SOf s).re * (SOf s).im = -(4 * s 0 * s 1) := by
  have h := SOf_sq s
  rw [one_add_aOf_sq] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [sq, mul_re, mul_im] at h1 h2
  constructor <;> linarith

theorem normSq_SOf (s : Phase) :
    normSq (SOf s) = Real.sqrt (secondCollisionDistanceSq s) := by
  have hsq : normSq (SOf s) ^ 2 = secondCollisionDistanceSq s := by
    rw [sq, ← normSq_mul, ← sq, SOf_sq, one_add_aOf_sq, normSq_mk, secondCollisionDistanceSq]
    ring
  rw [← hsq, Real.sqrt_sq (normSq_nonneg _)]

theorem secondCollisionDistanceSq_pos {s : Phase} (hs : 2 * zNormSq s < 1) :
    0 < secondCollisionDistanceSq s := by
  unfold secondCollisionDistanceSq; simp only [zNormSq] at hs
  have : 0 < 1 - 2 * (s 0 ^ 2 - s 1 ^ 2) := by nlinarith [sq_nonneg (s 1)]
  nlinarith [sq_nonneg (4 * s 0 * s 1)]

/-- **The regularization identity**: `G ∘ Φ = 2 √D · K` on `2|z|² < 1`. -/
theorem G_toEH (μ c : ℝ) {s : Phase} (hs : 2 * zNormSq s < 1) :
    ehLeftHamiltonian μ c (toEH μ s) =
      2 * Real.sqrt (secondCollisionDistanceSq s) * leviCivitaHamiltonian μ c s := by
  rw [G_toEH_eq_GP μ c hs]
  obtain ⟨h1, h2⟩ := SOf_re_im s
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [EHPoly.G_poly_identity _ _ _ _ _ _ _ _ _ h1 h2 h3]
  have hr : normSq (SOf s) = (SOf s).re ^ 2 + (SOf s).im ^ 2 := by rw [normSq_apply]; ring
  rw [← hr, normSq_SOf]
  have hD : 0 < Real.sqrt (secondCollisionDistanceSq s) :=
    Real.sqrt_pos.2 (secondCollisionDistanceSq_pos hs)
  simp only [EHPoly.KP, leviCivitaHamiltonian, zNormSq, wNormSq]
  field_simp
  ring

/-- The inverse map `(ξ, y) ↦ (z, w)`. -/
def fromEH (μ : ℝ) (t : Phase) : Phase :=
  ofC (I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ))
    (I * (wC t / ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (cosh (zC t / 2))) -
      ((1 / 2 - μ : ℝ) : ℂ) * (starRingEnd ℂ) (I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ))))

def sourceEH : Set Phase := {s | 2 * zNormSq s < 1}

def targetEH : Set Phase :=
  {t | |(zC t).im| < Real.pi ∧ normSq (sinh (zC t / 2)) < 1}

@[simp] theorem zC_ofC (a b : ℂ) : zC (ofC a b) = a := by
  apply Complex.ext <;> simp [zC, ofC]

@[simp] theorem wC_ofC (a b : ℂ) : wC (ofC a b) = b := by
  apply Complex.ext <;> simp [wC, ofC]

theorem ofC_zC_wC (s : Phase) : ofC (zC s) (wC s) = s := by
  ext i; fin_cases i <;> simp [ofC, zC, wC]

theorem sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [ne_eq, ofReal_eq_zero]; positivity

theorem sqrt2_mul_sqrt2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem normSq_aOf (s : Phase) : normSq (aOf s) = 2 * zNormSq s := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  simp [aOf, zC, normSq_apply, zNormSq, mul_re, mul_im]
  linear_combination (s 0 ^ 2 + s 1 ^ 2) * h

theorem re_SOf_pos {s : Phase} (hs : 2 * zNormSq s < 1) : 0 < (SOf s).re :=
  re_csqrt_pos (re_one_add_aOf_sq_pos hs)

theorem toEH_mem_target (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) : toEH μ s ∈ targetEH := by
  have hw := re_one_add_aOf_sq_pos hs
  refine ⟨?_, ?_⟩
  · simp only [toEH, zC_ofC]
    have := abs_im_arsinhC_lt hw
    rw [show (2 * arsinhC (aOf s)).im = 2 * (arsinhC (aOf s)).im by simp, abs_mul]
    norm_num; linarith
  · simp only [toEH, zC_ofC, show 2 * arsinhC (aOf s) / 2 = arsinhC (aOf s) by ring,
      sinh_arsinhC hw, normSq_aOf]
    exact hs

theorem fromEH_mem_source (μ : ℝ) {t : Phase} (ht : t ∈ targetEH) : fromEH μ t ∈ sourceEH := by
  have h := ht.2
  show 2 * zNormSq (fromEH μ t) < 1
  have : 2 * zNormSq (fromEH μ t) = normSq (sinh (zC t / 2)) := by
    have hz : zNormSq (fromEH μ t) = normSq (zC (fromEH μ t)) := by
      simp [zNormSq, normSq_apply, zC, fromEH, ofC]; ring
    rw [hz, fromEH, zC_ofC, normSq_div, normSq_mul, normSq_I, normSq_ofReal,
      Real.mul_self_sqrt (by norm_num)]
    ring
  linarith

theorem fromEH_toEH (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) : fromEH μ (toEH μ s) = s := by
  have hw := re_one_add_aOf_sq_pos hs
  have hS : (starRingEnd ℂ) (SOf s) ≠ 0 := by
    rw [map_ne_zero]; intro h; have := re_SOf_pos hs; rw [h] at this; simp at this
  have hhalf : 2 * arsinhC (aOf s) / 2 = arsinhC (aOf s) := by ring
  have hz : I * sinh (zC (toEH μ s) / 2) / (Real.sqrt 2 : ℂ) = zC s := by
    rw [toEH, zC_ofC, hhalf, sinh_arsinhC hw, aOf]
    field_simp [sqrt2_ne]
    ring_nf
    rw [I_sq]; ring
  conv_rhs => rw [← ofC_zC_wC s]
  rw [fromEH, hz]
  congr 1
  simp only [toEH, wC_ofC, zC_ofC, hhalf, cosh_arsinhC hw]
  rw [show csqrt (1 + aOf s ^ 2) = SOf s from rfl]
  field_simp [sqrt2_ne, hS]
  ring_nf
  simp [I_sq]

theorem toEH_fromEH (μ : ℝ) {t : Phase} (ht : t ∈ targetEH) : toEH μ (fromEH μ t) = t := by
  have hstrip : |(zC t / 2).im| < Real.pi / 2 := by
    have := ht.1; rw [div_ofNat_im, abs_div, abs_two]; linarith
  have ha : aOf (fromEH μ t) = sinh (zC t / 2) := by
    simp only [aOf, fromEH, zC_ofC]
    field_simp [sqrt2_ne]
    ring_nf; simp [I_sq]
  have hc : 0 < (cosh (zC t / 2)).re := by
    rw [EHTrig.cosh_eq_mk]
    exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [abs_lt.1 hstrip], by linarith [abs_lt.1 hstrip]⟩)
  have hSc : SOf (fromEH μ t) = cosh (zC t / 2) := by
    rw [SOf, ha, show 1 + sinh (zC t / 2) ^ 2 = cosh (zC t / 2) ^ 2 by
      rw [← cosh_sq_sub_sinh_sq (zC t / 2)]; ring, csqrt_sq_of_re_pos hc]
  have hC : (starRingEnd ℂ) (cosh (zC t / 2)) ≠ 0 := by
    rw [map_ne_zero]; intro h; rw [h] at hc; simp at hc
  conv_rhs => rw [← ofC_zC_wC t]
  rw [toEH, ha, arsinhC_sinh hstrip, hSc]
  congr 1
  · ring
  · simp only [fromEH, wC_ofC, zC_ofC]
    field_simp [sqrt2_ne, hC]
    ring_nf; simp [I_sq]

theorem toEH_neg (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) : toEH μ (-s) = -toEH μ s := by
  have hw := re_one_add_aOf_sq_pos hs
  have hza : aOf (-s) = -aOf s := by simp [aOf, zC]; apply Complex.ext <;> simp
  have hz : zC (-s) = -zC s := by apply Complex.ext <;> simp [zC]
  have hwc : wC (-s) = -wC s := by apply Complex.ext <;> simp [wC]
  have hS : SOf (-s) = SOf s := by rw [SOf, hza, neg_sq]; rfl
  rw [toEH, toEH, hza, arsinhC_neg hw, hS, hz, hwc]
  ext i; fin_cases i <;> simp [ofC] <;> ring

theorem toEH_leftCollisionPoint {μ : ℝ} (hμ1 : μ < 1) :
    toEH μ (leftCollisionPoint μ) = ehLeftCollisionPoint μ := by
  have hz : zC (leftCollisionPoint μ) = 0 := by
    apply Complex.ext <;> simp [zC, leftCollisionPoint]
  have ha : aOf (leftCollisionPoint μ) = 0 := by simp [aOf, hz]
  have hS : SOf (leftCollisionPoint μ) = 1 := by simp [SOf, ha, csqrt]
  have h0 : arsinhC 0 = 0 := by simp [arsinhC, csqrt]
  rw [toEH, ha, h0, hS, hz]
  ext i; fin_cases i <;>
    simp [ofC, ehLeftCollisionPoint, wC, leftCollisionPoint, mul_re, mul_im]

end

end EHReg

end BirkhoffGlobalSection

/-! Derivative, smoothness and conformal symplecticity of `toEH`. -/

namespace BirkhoffGlobalSection

namespace EHReg

open Complex EHArsinh

noncomputable section

/-- `zC` as a continuous `ℝ`-linear map. -/
def zCLM : Phase →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.proj 1))

/-- `wC` as a continuous `ℝ`-linear map. -/
def wCLM : Phase →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj 2).prod (ContinuousLinearMap.proj 3))

@[simp] theorem zCLM_apply (v : Phase) : zCLM v = zC v := by
  apply Complex.ext <;> simp [zCLM, zC]

@[simp] theorem wCLM_apply (v : Phase) : wCLM v = wC v := by
  apply Complex.ext <;> simp [wCLM, wC]

/-- `ofC` as a linear map. -/
def ofLM : (ℂ × ℂ) →ₗ[ℝ] Phase where
  toFun p := ofC p.1 p.2
  map_add' p q := by ext i; fin_cases i <;> simp [ofC]
  map_smul' r p := by ext i; fin_cases i <;> simp [ofC]

def ofCLM : (ℂ × ℂ) →L[ℝ] Phase := LinearMap.toContinuousLinearMap ofLM

@[simp] theorem ofCLM_apply (p : ℂ × ℂ) : ofCLM p = ofC p.1 p.2 := rfl

/-- The symplectic form in complex coordinates. -/
theorem omega_ofC (a b c d : ℂ) :
    phaseSymplecticForm (ofC a b) (ofC c d) =
      ((starRingEnd ℂ) a * d - (starRingEnd ℂ) c * b).re := by
  simp [phaseSymplecticForm, ofC, mul_re]; ring

theorem omega_eq (v w : Phase) :
    phaseSymplecticForm v w =
      ((starRingEnd ℂ) (zC v) * wC w - (starRingEnd ℂ) (zC w) * wC v).re := by
  rw [← omega_ofC, ofC_zC_wC, ofC_zC_wC]

def c0 : ℂ := -I * (Real.sqrt 2 : ℂ)

def mC (μ : ℝ) : ℂ := ((1 / 2 - μ : ℝ) : ℂ)

/-- `P = -i w + m z̄`. -/
def PC (μ : ℝ) (s : Phase) : ℂ := -I * wC s + mC μ * (starRingEnd ℂ) (zC s)

theorem aOf_eq (s : Phase) : aOf s = c0 * zC s := by simp [aOf, c0]

theorem toEH_eq (μ : ℝ) (s : Phase) :
    toEH μ s = ofC (2 * arsinhC (aOf s))
      ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) * PC μ s) := by
  rfl

theorem mem_arsinhDom {s : Phase} (hs : s ∈ sourceEH) : aOf s ∈ arsinhDom :=
  re_one_add_aOf_sq_pos hs

theorem hasFDerivAt_aOf (s : Phase) : HasFDerivAt aOf (c0 • zCLM) s := by
  have h := zCLM.hasFDerivAt (x := s)
  have : aOf = fun s => c0 * zCLM s := by funext s; simp [aOf_eq]
  rw [this]; exact h.const_mul c0

/-- Derivative of `ξ = 2 arsinh (a)`. -/
def Xi' (s : Phase) : Phase →L[ℝ] ℂ :=
  (2 : ℂ) • (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    (1 / csqrt (1 + aOf s ^ 2))).restrictScalars ℝ).comp (c0 • zCLM))

theorem hasFDerivAt_xi {s : Phase} (hs : s ∈ sourceEH) :
    HasFDerivAt (fun s => 2 * arsinhC (aOf s)) (Xi' s) s := by
  have h := ((hasDerivAt_arsinhC (mem_arsinhDom hs)).hasFDerivAt.restrictScalars ℝ).comp s
    (hasFDerivAt_aOf s)
  exact h.const_mul 2

/-- Derivative of `S = csqrt (1 + a²)`. -/
def S' (s : Phase) : Phase →L[ℝ] ℂ :=
  ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    (aOf s / csqrt (1 + aOf s ^ 2))).restrictScalars ℝ).comp (c0 • zCLM)

theorem hasFDerivAt_S {s : Phase} (hs : s ∈ sourceEH) :
    HasFDerivAt (fun s => csqrt (1 + aOf s ^ 2)) (S' s) s :=
  ((EHArsinh.hasDerivAt_S (mem_arsinhDom hs)).hasFDerivAt.restrictScalars ℝ).comp s
    (hasFDerivAt_aOf s)

def PCLM (μ : ℝ) : Phase →L[ℝ] ℂ :=
  (-I) • wCLM + mC μ • ((Complex.conjCLE.toContinuousLinearMap).comp zCLM)

theorem PC_eq (μ : ℝ) (s : Phase) : PC μ s = PCLM μ s := by
  simp [PC, PCLM]

theorem hasFDerivAt_PC (μ : ℝ) (s : Phase) : HasFDerivAt (PC μ) (PCLM μ) s := by
  have : PC μ = fun s => PCLM μ s := funext (PC_eq μ)
  rw [this]; exact (PCLM μ).hasFDerivAt

/-- Derivative of `y = √2 · conj S · P`. -/
def Y' (μ : ℝ) (s : Phase) : Phase →L[ℝ] ℂ :=
  ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2))) • PCLM μ +
    PC μ s • ((Real.sqrt 2 : ℂ) • ((Complex.conjCLE.toContinuousLinearMap).comp (S' s)))

theorem hasFDerivAt_y (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) :
    HasFDerivAt (fun s => (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) * PC μ s)
      (Y' μ s) s := by
  have hc : HasFDerivAt (fun s => (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)))
      ((Complex.conjCLE.toContinuousLinearMap).comp (S' s)) s :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp s (hasFDerivAt_S hs)
  exact (hc.const_mul (Real.sqrt 2 : ℂ)).mul (hasFDerivAt_PC μ s)

theorem hasFDerivAt_toEH (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) :
    HasFDerivAt (toEH μ) (ofCLM.comp ((Xi' s).prod (Y' μ s))) s := by
  have h := ofCLM.hasFDerivAt.comp s ((hasFDerivAt_xi hs).prodMk (hasFDerivAt_y μ hs))
  have : toEH μ = ofCLM ∘ fun s => (2 * arsinhC (aOf s),
      (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) * PC μ s) := by
    funext s; rw [toEH_eq]; rfl
  rw [this]; exact h

theorem fderiv_toEH_apply (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) (v : Phase) :
    fderiv ℝ (toEH μ) s v = ofC (Xi' s v) (Y' μ s v) := by
  rw [(hasFDerivAt_toEH μ hs).fderiv]; rfl

/-- **Conformal symplecticity**: `ω(DΦ v, DΦ w) = 4 ω(v, w)` on the source. -/
theorem toEH_symplectic (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) (v w : Phase) :
    phaseSymplecticForm (fderiv ℝ (toEH μ) s v) (fderiv ℝ (toEH μ) s w) =
      4 * phaseSymplecticForm v w := by
  rw [fderiv_toEH_apply μ hs, fderiv_toEH_apply μ hs, omega_ofC, omega_eq]
  have hS : csqrt (1 + aOf s ^ 2) ≠ 0 := csqrt_ne_zero (mem_arsinhDom hs)
  have hS' : (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) ≠ 0 := (map_ne_zero _).2 hS
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := sqrt2_mul_sqrt2
  have key : (starRingEnd ℂ) (Xi' s v) * Y' μ s w - (starRingEnd ℂ) (Xi' s w) * Y' μ s v =
      4 * ((starRingEnd ℂ) (zC v) * wC w - (starRingEnd ℂ) (zC w) * wC v) := by
    simp only [Xi', Y', S', PCLM, c0, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, zCLM_apply, wCLM_apply, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, map_add, map_neg,
      map_div₀, map_one, map_ofNat, conj_I, conj_ofReal, conj_conj]
    field_simp
    rw [show (Real.sqrt 2 : ℂ) ^ 2 = 2 by rw [sq]; exact h2]
    linear_combination (-4 * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) ^ 2 *
      ((starRingEnd ℂ) (zC v) * wC w - (starRingEnd ℂ) (zC w) * wC v)) * I_sq
  rw [key]
  simp [mul_re]

end

end EHReg

end BirkhoffGlobalSection

/-! Smoothness of the coordinate maps and of the EH Hamiltonian; openness of the domains. -/

namespace BirkhoffGlobalSection

namespace EHReg

open Complex EHArsinh

noncomputable section

theorem isOpen_sourceEH : IsOpen sourceEH := by
  apply isOpen_lt _ continuous_const
  unfold zNormSq; fun_prop

theorem continuous_zC : Continuous zC := by
  have : zC = fun s => zCLM s := funext fun s => (zCLM_apply s).symm
  rw [this]; exact zCLM.continuous

theorem isOpen_targetEH : IsOpen targetEH := by
  apply IsOpen.inter
  · exact isOpen_lt ((continuous_abs.comp Complex.continuous_im).comp continuous_zC)
      continuous_const
  · exact isOpen_lt (Complex.continuous_normSq.comp
      (Complex.continuous_sinh.comp (continuous_zC.div_const 2))) continuous_const

theorem contDiff_aOf {n : WithTop ℕ∞} : ContDiff ℝ n aOf := by
  have : aOf = fun s => (c0 • zCLM) s := by funext s; simp [aOf_eq]
  rw [this]; exact (c0 • zCLM).contDiff

theorem contDiffOn_toEH (μ : ℝ) {n : WithTop ℕ∞} : ContDiffOn ℝ n (toEH μ) sourceEH := by
  have hmaps : Set.MapsTo aOf sourceEH arsinhDom := fun s hs => mem_arsinhDom hs
  have hxi : ContDiffOn ℝ n (fun s => 2 * arsinhC (aOf s)) sourceEH :=
    contDiffOn_const.mul ((contDiffOn_arsinhC.restrict_scalars ℝ).comp
      contDiff_aOf.contDiffOn hmaps)
  have hS : ContDiffOn ℝ n (fun s => csqrt (1 + aOf s ^ 2)) sourceEH :=
    (contDiffOn_S.restrict_scalars ℝ).comp contDiff_aOf.contDiffOn hmaps
  have hc : ContDiffOn ℝ n (fun s => (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2))) sourceEH :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hS
  have hP : ContDiffOn ℝ n (PC μ) sourceEH := by
    have : PC μ = fun s => PCLM μ s := funext (PC_eq μ)
    rw [this]; exact (PCLM μ).contDiff.contDiffOn
  have hy : ContDiffOn ℝ n
      (fun s => (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) * PC μ s) sourceEH :=
    (contDiffOn_const.mul hc).mul hP
  have : toEH μ = fun s => ofCLM (2 * arsinhC (aOf s),
      (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (csqrt (1 + aOf s ^ 2)) * PC μ s) := by
    funext s; rw [toEH_eq]; rfl
  rw [this]
  exact ofCLM.contDiff.comp_contDiffOn (hxi.prodMk hy)

theorem re_cosh_half_pos {t : Phase} (ht : t ∈ targetEH) : 0 < (cosh (zC t / 2)).re := by
  have hstrip : |(zC t / 2).im| < Real.pi / 2 := by
    have := ht.1; rw [div_ofNat_im, abs_div, abs_two]; linarith
  rw [EHTrig.cosh_eq_mk]
  exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [abs_lt.1 hstrip], by linarith [abs_lt.1 hstrip]⟩)

theorem contDiffOn_fromEH (μ : ℝ) {n : WithTop ℕ∞} : ContDiffOn ℝ n (fromEH μ) targetEH := by
  have hz : ContDiff ℝ n (fun t : Phase => zC t / 2) := by
    have : (fun t : Phase => zC t / 2) = fun t => ((2 : ℂ)⁻¹ • zCLM) t := by
      funext t; simp [div_eq_inv_mul]
    rw [this]; exact ((2 : ℂ)⁻¹ • zCLM).contDiff
  have hsh : ContDiff ℝ n (fun t : Phase => sinh (zC t / 2)) :=
    (Complex.contDiff_sinh.restrict_scalars ℝ).comp hz
  have hch : ContDiff ℝ n (fun t : Phase => (starRingEnd ℂ) (cosh (zC t / 2))) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp
      ((Complex.contDiff_cosh.restrict_scalars ℝ).comp hz)
  have hw : ContDiff ℝ n wC := by
    have : wC = fun t => wCLM t := funext fun t => (wCLM_apply t).symm
    rw [this]; exact wCLM.contDiff
  have hinv : ContDiffOn ℝ n
      (fun t : Phase => ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (cosh (zC t / 2)))⁻¹) targetEH := by
    refine (contDiff_const.mul hch).contDiffOn.inv fun t ht => ?_
    refine mul_ne_zero sqrt2_ne ((map_ne_zero _).2 fun h => ?_)
    have := re_cosh_half_pos ht; rw [h] at this; simp at this
  have hzz : ContDiff ℝ n (fun t : Phase => I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ)) :=
    (contDiff_const.mul hsh).div_const _
  have hzc : ContDiff ℝ n
      (fun t : Phase => (starRingEnd ℂ) (I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ))) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp hzz
  have hww : ContDiffOn ℝ n (fun t : Phase => I * (wC t / ((Real.sqrt 2 : ℂ) *
      (starRingEnd ℂ) (cosh (zC t / 2))) - ((1 / 2 - μ : ℝ) : ℂ) *
      (starRingEnd ℂ) (I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ)))) targetEH := by
    simp only [div_eq_mul_inv]
    exact contDiffOn_const.mul ((hw.contDiffOn.mul hinv).sub
      (contDiffOn_const.mul (by simpa only [div_eq_mul_inv] using hzc.contDiffOn)))
  have : fromEH μ = fun t => ofCLM (I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ),
      I * (wC t / ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (cosh (zC t / 2))) -
        ((1 / 2 - μ : ℝ) : ℂ) * (starRingEnd ℂ) (I * sinh (zC t / 2) / (Real.sqrt 2 : ℂ)))) := by
    funext t; rfl
  rw [this]
  exact ofCLM.contDiff.comp_contDiffOn (hzz.contDiffOn.prodMk hww)

theorem contDiff_G (μ c : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (ehLeftHamiltonian μ c) := by
  unfold ehLeftHamiltonian
  fun_prop

end

end EHReg

end BirkhoffGlobalSection

/-! The vector-field relation `DΦ · X_K = (4/κ) · X_G ∘ Φ` on the zero level. -/

namespace BirkhoffGlobalSection

namespace EHReg

open Complex EHArsinh

noncomputable section

theorem fderiv_eq_sum (F : Phase → ℝ) (p v : Phase) :
    fderiv ℝ F p v = ∑ i, v i * partialDerivative F p i := by
  have hv : v = ∑ i, v i • coordinateVector i := by
    ext j; fin_cases j <;> simp [coordinateVector, Fin.sum_univ_four]
  conv_lhs => rw [hv]
  simp [map_sum, partialDerivative]

theorem omega_X (F : Phase → ℝ) (p v : Phase) :
    phaseSymplecticForm (hamiltonianVectorField F p) v = fderiv ℝ F p v := by
  rw [fderiv_eq_sum, Fin.sum_univ_four]
  simp [phaseSymplecticForm, hamiltonianVectorField]; ring

theorem omega_sub_left (a b y : Phase) :
    phaseSymplecticForm (a - b) y = phaseSymplecticForm a y - phaseSymplecticForm b y := by
  simp [phaseSymplecticForm]; ring

theorem omega_smul_left (r : ℝ) (a y : Phase) :
    phaseSymplecticForm (r • a) y = r * phaseSymplecticForm a y := by
  simp [phaseSymplecticForm]; ring

theorem omega_nondeg {x : Phase} (h : ∀ y, phaseSymplecticForm x y = 0) : x = 0 := by
  have h0 := h (coordinateVector 2); have h1 := h (coordinateVector 3)
  have h2 := h (coordinateVector 0); have h3 := h (coordinateVector 1)
  simp [phaseSymplecticForm, coordinateVector] at h0 h1 h2 h3
  ext j; fin_cases j <;> simp <;> linarith

/-- `κ = 2 √D`. -/
def kappa (s : Phase) : ℝ := 2 * Real.sqrt (secondCollisionDistanceSq s)

theorem kappa_pos {s : Phase} (hs : s ∈ sourceEH) : 0 < kappa s := by
  unfold kappa; have := Real.sqrt_pos.2 (secondCollisionDistanceSq_pos hs); linarith

theorem leviCivitaHamiltonian_contDiffAt' (μ c : ℝ) {y : Phase}
    (hy : 0 < secondCollisionDistanceSq y) :
    ContDiffAt ℝ ⊤ (leviCivitaHamiltonian μ c) y := by
  have hd : ContDiff ℝ ⊤ secondCollisionDistanceSq := by
    unfold secondCollisionDistanceSq; fun_prop
  have hs : ContDiffAt ℝ ⊤ (fun s => Real.sqrt (secondCollisionDistanceSq s)) y :=
    hd.contDiffAt.sqrt hy.ne'
  have hpos : Real.sqrt (secondCollisionDistanceSq y) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  unfold leviCivitaHamiltonian wNormSq zNormSq
  refine ContDiffAt.sub ?_ ((contDiffAt_const.mul (by fun_prop)).div hs hpos)
  fun_prop

theorem leviCivitaHamiltonian_differentiableAt (μ c : ℝ) {s : Phase}
    (hy : 0 < secondCollisionDistanceSq s) :
    DifferentiableAt ℝ (leviCivitaHamiltonian μ c) s :=
  (leviCivitaHamiltonian_contDiffAt' μ c hy).differentiableAt (by simp)

theorem kappa_differentiableAt {s : Phase} (hs : s ∈ sourceEH) :
    DifferentiableAt ℝ kappa s := by
  have hd : Differentiable ℝ secondCollisionDistanceSq := by
    unfold secondCollisionDistanceSq; fun_prop
  unfold kappa
  exact (differentiableAt_const _).mul ((hd s).sqrt (secondCollisionDistanceSq_pos hs).ne')

/-- `dG(Φ s) ∘ DΦ(s) = κ(s) dK(s)` at a zero of `K`. -/
theorem dG_comp_dPhi (μ c : ℝ) {s : Phase} (hs : s ∈ sourceEH)
    (hK : leviCivitaHamiltonian μ c s = 0) (v : Phase) :
    fderiv ℝ (ehLeftHamiltonian μ c) (toEH μ s) (fderiv ℝ (toEH μ) s v) =
      kappa s * fderiv ℝ (leviCivitaHamiltonian μ c) s v := by
  have hev : (ehLeftHamiltonian μ c ∘ toEH μ) =ᶠ[nhds s]
      fun s => kappa s * leviCivitaHamiltonian μ c s :=
    Filter.eventuallyEq_of_mem (isOpen_sourceEH.mem_nhds hs) fun s' hs' => by
      simp only [Function.comp, kappa]; exact G_toEH μ c hs'
  have hG : DifferentiableAt ℝ (ehLeftHamiltonian μ c) (toEH μ s) :=
    (contDiff_G μ c (n := 1)).differentiable one_ne_zero _
  have hchain := hG.hasFDerivAt.comp s (hasFDerivAt_toEH μ hs)
  have hK' := (leviCivitaHamiltonian_differentiableAt μ c
    (secondCollisionDistanceSq_pos hs)).hasFDerivAt
  have hprod := (kappa_differentiableAt hs).hasFDerivAt.mul hK'
  have := (hchain.congr_of_eventuallyEq hev.symm).unique hprod
  have hv := congrArg (fun L => L v) this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hK, zero_mul, add_zero] at hv
  rw [(hasFDerivAt_toEH μ hs).fderiv]
  exact hv

/-- `DΦ(s)` is surjective on the source. -/
theorem dPhi_surjective (μ : ℝ) {s : Phase} (hs : s ∈ sourceEH) (y : Phase) :
    ∃ u, fderiv ℝ (toEH μ) s u = y := by
  have ht := toEH_mem_target μ hs
  have hev : (toEH μ ∘ fromEH μ) =ᶠ[nhds (toEH μ s)] id :=
    Filter.eventuallyEq_of_mem (isOpen_targetEH.mem_nhds ht) fun t ht' =>
      toEH_fromEH μ ht'
  have hfd : DifferentiableAt ℝ (fromEH μ) (toEH μ s) :=
    ((contDiffOn_fromEH μ (n := 1)).differentiableOn one_ne_zero _ ht).differentiableAt
      (isOpen_targetEH.mem_nhds ht)
  have hback : fromEH μ (toEH μ s) = s := fromEH_toEH μ hs
  have hT : HasFDerivAt (toEH μ) (fderiv ℝ (toEH μ) s) (fromEH μ (toEH μ s)) := by
    rw [hback, (hasFDerivAt_toEH μ hs).fderiv]; exact hasFDerivAt_toEH μ hs
  have hchain := hT.comp (toEH μ s) hfd.hasFDerivAt
  have hid := (hchain.congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id (toEH μ s))
  refine ⟨fderiv ℝ (fromEH μ) (toEH μ s) y, ?_⟩
  have := congrArg (fun L => L y) hid
  simpa using this

/-- **Vector-field relation**: `DΦ · X_K = (4/κ) · X_G(Φ)` on the zero level. -/
theorem vectorField_toEH (μ c : ℝ) {s : Phase} (hs : s ∈ sourceEH)
    (hK : leviCivitaHamiltonian μ c s = 0) :
    fderiv ℝ (toEH μ) s (hamiltonianVectorField (leviCivitaHamiltonian μ c) s) =
      (4 / kappa s) • hamiltonianVectorField (ehLeftHamiltonian μ c) (toEH μ s) := by
  rw [← sub_eq_zero]
  apply omega_nondeg
  intro y
  obtain ⟨u, rfl⟩ := dPhi_surjective μ hs y
  rw [omega_sub_left, toEH_symplectic μ hs, omega_smul_left, omega_X, omega_X,
    dG_comp_dPhi μ c hs hK]
  have := kappa_pos hs
  field_simp
  ring

end

end EHReg

end BirkhoffGlobalSection


