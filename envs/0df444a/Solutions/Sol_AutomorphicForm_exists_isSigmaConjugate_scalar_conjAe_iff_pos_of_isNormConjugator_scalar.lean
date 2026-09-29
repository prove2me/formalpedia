-- Prove2me | solution 1 for AutomorphicForm.exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4f3d9e8d-b09e-515f-9539-18ce6cbff345

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar

set_option autoImplicit false

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal ComplexConjugate

noncomputable section

namespace P2mKindSignCx

abbrev Ecx : Type := ℂ ⊗[ℝ] ℝ

abbrev Mcx : Type := Matrix (Fin 2) (Fin 2) Ecx

abbrev Gcx : Type := GL (Fin 2) Ecx

def ridE : Ecx ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ridE_tmul (l : ℂ) (a : ℝ) : ridE (l ⊗ₜ[ℝ] a) = a • l := rfl

def iotaE (a : ℝ) : Ecx := (1 : ℂ) ⊗ₜ[ℝ] a

theorem ridE_iotaE (a : ℝ) : ridE (iotaE a) = (a : ℂ) := by
  rw [iotaE, ridE_tmul, Complex.real_smul, mul_one]

theorem ridE_symm_ofReal (a : ℝ) : ridE.symm (a : ℂ) = iotaE a := by
  rw [← ridE_iotaE, RingEquiv.symm_apply_apply]

theorem iotaE_eq_algebraMap (a : ℝ) : iotaE a = algebraMap ℝ Ecx a := rfl

theorem iotaE_mul (a b : ℝ) : iotaE (a * b) = iotaE a * iotaE b := by
  rw [iotaE_eq_algebraMap, iotaE_eq_algebraMap, iotaE_eq_algebraMap, map_mul]

theorem iotaE_one : iotaE 1 = 1 := rfl

theorem real_smul_eq (r : ℝ) (e : Ecx) : r • e = iotaE r * e := Algebra.smul_def r e

scoped instance instIsScalarTowerEcx : IsScalarTower ℝ Ecx Ecx :=
  ⟨fun r a b => by
    change (r • a) * b = r • (a * b)
    rw [real_smul_eq, real_smul_eq, mul_assoc]⟩

scoped instance instSMulCommClassEcx : SMulCommClass ℝ Ecx Ecx :=
  ⟨fun r a b => by
    change r • (a * b) = a * (r • b)
    rw [real_smul_eq, real_smul_eq, mul_left_comm]⟩

abbrev sigE : Ecx →+* Ecx := sigmaTensor ℝ ℂ ℝ Complex.conjAe

theorem sigE_tmul (l : ℂ) (a : ℝ) : sigE (l ⊗ₜ[ℝ] a) = (conj l) ⊗ₜ[ℝ] a := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem ridE_sigE (e : Ecx) : ridE (sigE e) = conj (ridE e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigE_tmul, ridE_tmul, ridE_tmul, Complex.real_smul, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem sigE_iotaE (a : ℝ) : sigE (iotaE a) = iotaE a := by
  rw [iotaE, sigE_tmul, map_one]

theorem sigE_sigE (e : Ecx) : sigE (sigE e) = e := by
  apply ridE.injective
  rw [ridE_sigE, ridE_sigE, Complex.conj_conj]

theorem sigE_eq_self_iff (e : Ecx) : sigE e = e ↔ ∃ a : ℝ, e = iotaE a := by
  constructor
  · intro h
    have h1 : conj (ridE e) = ridE e := by rw [← ridE_sigE, h]
    refine ⟨(ridE e).re, ?_⟩
    apply ridE.injective
    rw [ridE_iotaE]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  · rintro ⟨a, rfl⟩
    exact sigE_iotaE a

def lamE (l : ℂ) : Ecx := l ⊗ₜ[ℝ] (1 : ℝ)

theorem ridE_lamE (l : ℂ) : ridE (lamE l) = l := by
  rw [lamE, ridE_tmul, one_smul]

theorem sigE_lamE (l : ℂ) : sigE (lamE l) = lamE (conj l) := by
  rw [lamE, sigE_tmul, lamE]

theorem isUnit_iff_ridE_ne_zero (e : Ecx) : IsUnit e ↔ ridE e ≠ 0 := by
  constructor
  · intro h h0
    have := h.map ridE
    rw [h0] at this
    exact not_isUnit_zero this
  · intro h
    have hu : IsUnit (ridE e) := isUnit_iff_ne_zero.mpr h
    have := hu.map ridE.symm
    rwa [RingEquiv.symm_apply_apply] at this

theorem smul_mul_M (r : ℝ) (X Y : Mcx) : (r • X) * Y = r • (X * Y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, real_smul_eq, Finset.mul_sum, mul_assoc]

theorem mul_smul_M (r : ℝ) (X Y : Mcx) : X * (r • Y) = r • (X * Y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, real_smul_eq, Finset.mul_sum, mul_left_comm]

theorem trace_smul_M (r : ℝ) (X : Mcx) : Matrix.trace (r • X) = r • Matrix.trace X := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, real_smul_eq, Finset.mul_sum]

abbrev sigM : Mcx →+* Mcx := (sigE).mapMatrix

theorem sigM_apply (X : Mcx) : sigM X = X.map sigE := rfl

theorem sigM_sigM (X : Mcx) : sigM (sigM X) = X := by
  ext i j
  simp [sigE_sigE]

theorem coe_sigmaGL (g : Gcx) :
    ((sigmaGL ℝ ℂ ℝ Complex.conjAe g : Gcx) : Mcx) = sigM (g : Mcx) := rfl

def iotaM (Y : Matrix (Fin 2) (Fin 2) ℝ) : Mcx := Y.map fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ)

theorem iotaM_apply (Y : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) : iotaM Y i j = iotaE (Y i j) := rfl

theorem sigM_eq_self_iff (X : Mcx) : sigM X = X ↔ X ∈ Set.range iotaM := by
  constructor
  · intro h
    have h' : ∀ i j, sigE (X i j) = X i j := fun i j => by
      have := congrFun (congrFun h i) j
      simpa using this
    choose a ha using fun i j => (sigE_eq_self_iff (X i j)).mp (h' i j)
    refine ⟨Matrix.of fun i j => a i j, ?_⟩
    ext i j
    rw [iotaM_apply, Matrix.of_apply, ← ha]
  · rintro ⟨Y, rfl⟩
    ext i j
    simp [iotaM_apply, sigE_iotaE]

def lamM (l : ℂ) : Mcx := Matrix.diagonal fun _ => lamE l

theorem sigM_lamM (l : ℂ) : sigM (lamM l) = lamM (conj l) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [lamM, sigE_lamE]
  · simp [lamM, Matrix.diagonal_apply_ne _ h]

abbrev RM : Mcx →+* Matrix (Fin 2) (Fin 2) ℂ := (ridE : Ecx →+* ℂ).mapMatrix

theorem RM_lamM (l : ℂ) : RM (lamM l) = l • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [lamM, ridE_lamE]
  · simp [lamM, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem det_RM (X : Mcx) : (RM X).det = ridE X.det :=
  (RingHom.map_det (ridE : Ecx →+* ℂ) X).symm

theorem isUnit_iff_det_RM_ne_zero (X : Mcx) : IsUnit X ↔ (RM X).det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ridE_ne_zero, det_RM]

theorem det_smul_one_add_smul (a b : ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + b • D).det =
      a ^ 2 + a * b * (D 0 0 + D 1 1) + b ^ 2 * (D 0 0 * D 1 1 - D 0 1 * D 1 0) := by
  rw [Matrix.det_fin_two]
  simp [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring

theorem exists_det_ne_zero (D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ p : ℂ × ℂ, p ∈ ({((1 : ℂ), (1 : ℂ)), (Complex.I, -Complex.I), (1 + Complex.I, 1 - Complex.I)} :
      Set (ℂ × ℂ)) ∧ (p.1 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + p.2 • D).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon (1, 1) (by simp)
  have h2 := hcon (Complex.I, -Complex.I) (by simp)
  have h3 := hcon (1 + Complex.I, 1 - Complex.I) (by simp)
  simp only at h1 h2 h3
  rw [det_smul_one_add_smul] at h1 h2 h3
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have key : (1 + Complex.I) ^ 2 + (1 + Complex.I) * (1 - Complex.I) * (D 0 0 + D 1 1) +
      (1 - Complex.I) ^ 2 * (D 0 0 * D 1 1 - D 0 1 * D 1 0) = 4 * Complex.I := by
    linear_combination (1 - Complex.I) * h1 + (1 + Complex.I) * h2 +
      (-Complex.I + Complex.I * (D 0 0 + D 1 1) - Complex.I * (D 0 0 * D 1 1 - D 0 1 * D 1 0)) * hI2
  rw [key] at h3
  have : (4 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact this h3

def scM (a : Ecx) : Mcx := Matrix.diagonal fun _ => a

theorem scM_eq_smul_one (a : Ecx) : scM a = a • (1 : Mcx) :=
  (Matrix.smul_one_eq_diagonal a).symm

theorem lamM_eq_scM (l : ℂ) : lamM l = scM (lamE l) := rfl

theorem scM_comm (a : Ecx) (X : Mcx) : scM a * X = X * scM a := by
  rw [scM_eq_smul_one]
  calc a • (1 : Mcx) * X = a • ((1 : Mcx) * X) := Matrix.smul_mul a 1 X
    _ = a • (X * 1) := by rw [one_mul, mul_one]
    _ = X * (a • (1 : Mcx)) := (Matrix.mul_smul X a 1).symm

def Zof (u : ℝˣ) : Gcx := toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) u)

theorem coe_toTensorGL (g : GL (Fin 2) ℝ) :
    ((toTensorGL ℝ ℂ ℝ g : Gcx) : Mcx) = iotaM (g : Matrix (Fin 2) (Fin 2) ℝ) := rfl

theorem coe_Zof (u : ℝˣ) : ((Zof u : Gcx) : Mcx) = scM (iotaE (u : ℝ)) := by
  rw [Zof, coe_toTensorGL]
  ext i j
  by_cases h : i = j
  · subst h
    simp [iotaM_apply, scM, Matrix.GeneralLinearGroup.scalar, iotaE]
  · simp [iotaM_apply, scM, Matrix.diagonal_apply_ne _ h, Matrix.GeneralLinearGroup.scalar, iotaE]

theorem Zof_comm (u : ℝˣ) (g : Gcx) : Zof u * g = g * Zof u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_Zof]
  exact scM_comm _ _

theorem sigmaGL_Zof (u : ℝˣ) : sigmaGL ℝ ℂ ℝ Complex.conjAe (Zof u) = Zof u := by
  apply Units.ext
  rw [coe_sigmaGL, coe_Zof]
  ext i j
  by_cases h : i = j
  · subst h; simp [scM, sigE_iotaE]
  · simp [scM, Matrix.diagonal_apply_ne _ h]

theorem Zof_mul (u v : ℝˣ) : Zof (u * v) = Zof u * Zof v := by
  rw [Zof, Zof, Zof, map_mul, map_mul]

theorem coe_Zof_mul_scM (u : ℝˣ) (X : Mcx) : ((Zof u : Gcx) : Mcx) * X = X * ((Zof u : Gcx) : Mcx) := by
  rw [coe_Zof]; exact scM_comm _ _

theorem coe_mul_sigma (δ : Gcx) :
    ((δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ : Gcx) : Mcx) = (δ : Mcx) * sigM (δ : Mcx) := rfl

theorem hilbert90 (c : ℝˣ) (hc : 0 < (c : ℝ)) (δ : Gcx)
    (hN : δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ = Zof c) :
    ∃ (r : ℝˣ) (x : Gcx), 0 < (r : ℝ) ∧ r * r = c ∧
      δ = x⁻¹ * Zof r * sigmaGL ℝ ℂ ℝ Complex.conjAe x := by
  set σ := sigmaGL ℝ ℂ ℝ Complex.conjAe with hσ
  have hr0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  let r : ℝˣ := Units.mk0 (Real.sqrt c) hr0.ne'
  have hrr : r * r = c := by
    apply Units.ext
    simp only [Units.val_mul, r, Units.val_mk0]
    exact Real.mul_self_sqrt hc.le

  set δ₁ : Gcx := δ * (Zof r)⁻¹ with hδ₁
  have h1 : δ₁ * σ δ₁ = 1 := by
    have e1 : σ (Zof r)⁻¹ = (Zof r)⁻¹ := by rw [map_inv, sigmaGL_Zof]
    calc δ₁ * σ δ₁ = δ * (Zof r)⁻¹ * (σ δ * (Zof r)⁻¹) := by rw [hδ₁, map_mul, e1]
      _ = δ * σ δ * ((Zof r)⁻¹ * (Zof r)⁻¹) := by
          have : (Zof r)⁻¹ * σ δ = σ δ * (Zof r)⁻¹ := by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, Zof_comm, mul_assoc, mul_inv_cancel, mul_one]
          rw [mul_assoc, ← mul_assoc (Zof r)⁻¹, this]
          simp only [mul_assoc]
      _ = Zof c * (Zof r * Zof r)⁻¹ := by rw [hN, mul_inv_rev]
      _ = 1 := by rw [← Zof_mul, hrr, mul_inv_cancel]
  have h1M : (δ₁ : Mcx) * sigM (δ₁ : Mcx) = 1 := by
    have := congrArg (fun g : Gcx => (g : Mcx)) h1
    simp only [coe_mul_sigma, Units.val_one] at this
    exact this

  set D : Matrix (Fin 2) (Fin 2) ℂ := RM (δ₁ : Mcx) with hD
  obtain ⟨p, hp, hdet⟩ := exists_det_ne_zero D
  have hp2 : p.2 = conj p.1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · simp
    · simp
    · simp [map_add, sub_eq_add_neg]
  set l : ℂ := p.1 with hl
  set u : Mcx := lamM l + (δ₁ : Mcx) * lamM (conj l) with hu
  have hRMu : RM u = p.1 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + p.2 • D := by
    rw [hu, map_add, map_mul, RM_lamM, RM_lamM, hp2, ← hD, Matrix.mul_smul, mul_one]
  have hunit : IsUnit u := by
    rw [isUnit_iff_det_RM_ne_zero, hRMu]
    exact hdet

  have hkey : (δ₁ : Mcx) * sigM u = u := by
    rw [hu, map_add, map_mul, sigM_lamM, sigM_lamM, Complex.conj_conj, mul_add, ← mul_assoc, h1M,
      one_mul, add_comm]
  obtain ⟨ux, hux⟩ := hunit
  refine ⟨r, ux⁻¹, hr0, hrr, ?_⟩
  have h2 : δ₁ * σ ux = ux := by
    apply Units.ext
    rw [Units.val_mul, coe_sigmaGL, hux]
    exact hkey
  have h3 : δ₁ = ux * (σ ux)⁻¹ := eq_mul_inv_of_mul_eq h2
  calc δ = δ₁ * Zof r := by rw [hδ₁, inv_mul_cancel_right]
    _ = ux * (σ ux)⁻¹ * Zof r := by rw [h3]
    _ = ux * Zof r * (σ ux)⁻¹ := by rw [mul_assoc, ← Zof_comm, ← mul_assoc]
    _ = (ux⁻¹)⁻¹ * Zof r * σ ux⁻¹ := by rw [inv_inv, map_inv]

theorem conj_criterion {R : Type*} [Monoid R] (σ : R →* R) (x z s : Rˣ)
    (hz : ∀ A : R, (z : R) * A = A * z) (hs : σ (x : R) = s) (hsi : σ ((x⁻¹ : Rˣ) : R) = ((s⁻¹ : Rˣ) : R))
    (X : R) :
    X * ((x⁻¹ : Rˣ) * z * s : R) = ((x⁻¹ : Rˣ) * z * s : R) * σ X ↔
      σ ((x : R) * X * (x⁻¹ : Rˣ)) = (x : R) * X * (x⁻¹ : Rˣ) := by
  have eσ : σ ((x : R) * X * (x⁻¹ : Rˣ)) = (s : R) * σ X * (s⁻¹ : Rˣ) := by
    rw [map_mul, map_mul, hs, hsi]
  rw [eσ]
  constructor
  · intro h

    have h2 : (x : R) * X * (x⁻¹ : Rˣ) * z * s = (z : R) * s * σ X := by
      calc (x : R) * X * (x⁻¹ : Rˣ) * z * s = (x : R) * (X * ((x⁻¹ : Rˣ) * z * s)) := by
            simp only [mul_assoc]
        _ = (x : R) * ((x⁻¹ : Rˣ) * z * s * σ X) := by rw [h]
        _ = (z : R) * s * σ X := by
            simp only [mul_assoc, Units.mul_inv_cancel_left]
    have h3 : (x : R) * X * (x⁻¹ : Rˣ) * z = (z : R) * s * σ X * (s⁻¹ : Rˣ) := by
      calc (x : R) * X * (x⁻¹ : Rˣ) * z = (x : R) * X * (x⁻¹ : Rˣ) * z * s * (s⁻¹ : Rˣ) := by
            rw [Units.mul_inv_cancel_right]
        _ = (z : R) * s * σ X * (s⁻¹ : Rˣ) := by rw [h2]
    rw [← hz] at h3
    have h4 : (z : R) * ((x : R) * X * (x⁻¹ : Rˣ)) = (z : R) * ((s : R) * σ X * (s⁻¹ : Rˣ)) := by
      simpa only [mul_assoc] using h3
    exact ((Units.mul_right_inj z).1 h4).symm
  · intro h

    have h4 : (z : R) * ((x : R) * X * (x⁻¹ : Rˣ)) = (z : R) * ((s : R) * σ X * (s⁻¹ : Rˣ)) := by rw [h]
    have h3 : (x : R) * X * (x⁻¹ : Rˣ) * z = (z : R) * s * σ X * (s⁻¹ : Rˣ) := by
      rw [← hz]; simpa only [mul_assoc] using h4
    have h2 : (x : R) * X * (x⁻¹ : Rˣ) * z * s = (z : R) * s * σ X := by
      have := congrArg (fun A : R => A * s) h3
      simpa only [mul_assoc, Units.inv_mul, mul_one] using this
    have h5 : (x : R) * (X * ((x⁻¹ : Rˣ) * z * s)) = (x : R) * ((x⁻¹ : Rˣ) * z * s * σ X) := by
      calc (x : R) * (X * ((x⁻¹ : Rˣ) * z * s)) = (x : R) * X * (x⁻¹ : Rˣ) * z * s := by
            simp only [mul_assoc]
        _ = (z : R) * s * σ X := h2
        _ = (x : R) * ((x⁻¹ : Rˣ) * z * s * σ X) := by
            simp only [mul_assoc, Units.mul_inv_cancel_left]
    exact (Units.mul_right_inj x).1 h5

def twAlg (δ : Gcx) : Set Mcx :=
  {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
    (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)}

def conjM (x : Gcx) (X : Mcx) : Mcx := (x : Mcx) * X * ((x⁻¹ : Gcx) : Mcx)

theorem mem_twAlg_iff (r : ℝˣ) (x δ : Gcx) (hδ : δ = x⁻¹ * Zof r * sigmaGL ℝ ℂ ℝ Complex.conjAe x)
    (X : Mcx) : X ∈ twAlg δ ↔ conjM x X ∈ Set.range iotaM := by
  rw [← sigM_eq_self_iff]
  have hcoe : (δ : Mcx) = ((x⁻¹ : Gcx) : Mcx) * ((Zof r : Gcx) : Mcx) *
      ((sigmaGL ℝ ℂ ℝ Complex.conjAe x : Gcx) : Mcx) := by
    rw [hδ, Units.val_mul, Units.val_mul]
  have hsi : sigM ((x⁻¹ : Gcx) : Mcx) = (((sigmaGL ℝ ℂ ℝ Complex.conjAe x)⁻¹ : Gcx) : Mcx) := by
    rw [← map_inv]; rfl
  have key := conj_criterion (sigM : Mcx →+* Mcx).toMonoidHom x (Zof r) (sigmaGL ℝ ℂ ℝ Complex.conjAe x)
    (coe_Zof_mul_scM r) rfl hsi X
  rw [twAlg, Set.mem_setOf_eq, hcoe]
  exact key

theorem conjM_injective (x : Gcx) : Function.Injective (conjM x) := by
  intro X Y h
  have h1 := (Units.mul_left_inj x⁻¹).1 h
  exact (Units.mul_right_inj x).1 h1

theorem image_conjM_twAlg (r : ℝˣ) (x δ : Gcx) (hδ : δ = x⁻¹ * Zof r * sigmaGL ℝ ℂ ℝ Complex.conjAe x) :
    conjM x '' twAlg δ = Set.range iotaM := by
  ext U
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (mem_twAlg_iff r x δ hδ X).1 hX
  · intro hU
    refine ⟨((x⁻¹ : Gcx) : Mcx) * U * (x : Mcx), ?_, ?_⟩
    · rw [mem_twAlg_iff r x δ hδ]
      convert hU using 1
      simp only [conjM, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
    · simp only [conjM, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

theorem normString_two (δ : Gcx) :
    normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  simp [normString, Complex.finrank_real_complex, List.range_succ]

theorem toTensorGL_scalar (c : ℝˣ) :
    toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = Zof c := rfl

end P2mKindSignCx
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.P2mKindSignCx"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.P2mKindSignCx"

open P2mKindSignCx in
theorem solution
    (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    (∃ z : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      0 < (c : ℝ) := by

  have hN : δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ = Zof c := by
    have h1 : normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := normString_two δ
    have h2 : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        y⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * y := hδ
    rw [toTensorGL_scalar, h1] at h2
    have h3 : δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ = y * Zof c * y⁻¹ := by
      rw [h2]; group
    rw [h3, ← Zof_comm, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · rintro ⟨z, x, hx⟩

    set σ := sigmaGL ℝ ℂ ℝ Complex.conjAe with hσ
    have hσσ : ∀ g : Gcx, σ (σ g) = g := by
      intro g
      refine Units.ext ?_
      rw [hσ, coe_sigmaGL, coe_sigmaGL]
      exact sigM_sigM _
    have hδ' : δ = x * Matrix.GeneralLinearGroup.scalar (Fin 2) z * (σ x)⁻¹ := by
      rw [hx]; group
    have hsc : σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigE : Ecx →* Ecx) z) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [hσ, coe_sigmaGL]
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
      split_ifs <;> simp
    have hzc : ((z : Ecx) * sigE (z : Ecx)) = iotaE (c : ℝ) := by
      have h := hN
      rw [hδ'] at h
      rw [map_mul, map_mul, map_inv, hσσ, hsc] at h

      have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) z *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigE : Ecx →* Ecx) z) = x⁻¹ * Zof c * x := by
        rw [← h]; group
      have h2 : Matrix.GeneralLinearGroup.scalar (Fin 2) z *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigE : Ecx →* Ecx) z) = Zof c := by
        rw [h1, mul_assoc, Zof_comm c x, ← mul_assoc, inv_mul_cancel, one_mul]
      have h'' := congrArg (fun g : Gcx => (g : Mcx) 0 0) h2
      simp only [Units.val_mul, coe_Zof] at h''
      rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : Gcx) : Mcx) = scM (z : Ecx) from rfl,
        show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigE : Ecx →* Ecx) z) : Gcx) : Mcx) =
          scM (sigE (z : Ecx)) from rfl] at h''
      simpa [scM, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_two] using h''

    have hr := congrArg ridE hzc
    rw [map_mul, ridE_sigE, ridE_iotaE] at hr
    have hz0 : ridE (z : Ecx) ≠ 0 := (isUnit_iff_ridE_ne_zero _).1 z.isUnit
    have hre : ((c : ℝ) : ℂ) = (Complex.normSq (ridE (z : Ecx)) : ℂ) := by
      rw [← hr, Complex.mul_conj]
    have : (c : ℝ) = Complex.normSq (ridE (z : Ecx)) := by exact_mod_cast hre
    rw [this]
    exact Complex.normSq_pos.2 hz0
  · intro hc
    obtain ⟨r, x, hr, hrr, hx⟩ := hilbert90 c hc δ hN
    refine ⟨Units.map (algebraMap ℝ Ecx).toMonoidHom r, x⁻¹, ?_⟩
    have hZ : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℝ Ecx).toMonoidHom r) = Zof r := by
      refine Units.ext ?_
      rw [coe_Zof]
      rfl
    rw [hZ, hx, map_inv]
    group

end S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
end P2MW
export P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar (solution)
