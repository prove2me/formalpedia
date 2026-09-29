-- Prove2me | solution 1 for AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3e2a2e25-9310-5dde-9f75-b8ee1cc91eee

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal ComplexConjugate

noncomputable section

namespace P2mGramCoupled

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

section Gram

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [MeasurableSpace V] [BorelSpace V]

def coordMap {n : ℕ} (e : Fin n → V) : (Fin n → ℝ) → V := fun c => ∑ i, c i • e i

theorem continuous_coordMap {n : ℕ} (e : Fin n → V) : Continuous (coordMap e) := by
  unfold coordMap
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i).smul continuous_const

theorem measurable_coordMap {n : ℕ} (e : Fin n → V) : Measurable (coordMap e) :=
  (continuous_coordMap e).measurable

def gramDet (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : ℝ :=
  (Matrix.of fun i j : Fin n => B (e i) (e j)).det

def gramMeasure (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : Measure V :=
  ENNReal.ofReal (Real.sqrt |gramDet B e|) • Measure.map (coordMap e) volume

theorem coordMap_eq_comp {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    coordMap e' = coordMap e ∘ (Matrix.toLin' P) := by
  funext c
  simp only [coordMap, Function.comp_apply, Matrix.toLin'_apply]
  calc ∑ j, c j • e' j = ∑ j, ∑ i, (c j * P i j) • e i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hP j, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
    _ = ∑ i, ∑ j, (c j * P i j) • e i := Finset.sum_comm
    _ = ∑ i, (P.mulVec c) i • e i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        change ∑ j, c j * P i j = ∑ j, P i j * c j
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gramDet_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    gramDet B e' = P.det ^ 2 * gramDet B e := by
  have hG : (Matrix.of fun i j : Fin n => B (e' i) (e' j)) =
      P.transpose * (Matrix.of fun i j : Fin n => B (e i) (e j)) * P := by
    ext j k
    have hjk : B (e' j) (e' k) = ∑ i, ∑ l, P i j * P l k * B (e i) (e l) := by
      have h1 : B (e' j) = ∑ i, P i j • B (e i) := by rw [hP j, map_sum]; simp only [map_smul]
      rw [h1, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, hP k, map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hjk, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [gramDet, gramDet, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gramMeasure_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) (hdet : P.det ≠ 0) :
    gramMeasure B e' = gramMeasure B e := by
  rw [gramMeasure, gramMeasure, coordMap_eq_comp e e' P hP, gramDet_eq_of_comp B e e' P hP,
    ← Measure.map_map (measurable_coordMap e) (Matrix.toLin' P).continuous_of_finiteDimensional.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), abs_mul, abs_pow, Real.sqrt_mul' _ (abs_nonneg _),
    Real.sqrt_sq (abs_nonneg _), abs_inv]
  congr 1
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_mul]

theorem exists_matrix_of_span_eq {n : ℕ} (e e' : Fin n → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') ≤ Submodule.span ℝ (Set.range e)) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, (∀ j, e' j = ∑ i, P i j • e i) ∧ P.det ≠ 0 := by
  have hmem : ∀ j, e' j ∈ Submodule.span ℝ (Set.range e) := fun j =>
    hspan (Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem j)
  refine ⟨Matrix.of fun i j => c j i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]; exact (hc j).symm
  · intro hdet
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hP : ∀ j, e' j = ∑ i, (Matrix.of fun i j => c j i) i j • e i := fun j => by
      simp only [Matrix.of_apply]; exact (hc j).symm
    have h0 : coordMap e' v = 0 := by
      rw [coordMap_eq_comp e e' _ hP, Function.comp_apply, Matrix.toLin'_apply, hPv]
      simp [coordMap]
    apply hv
    funext j
    exact Fintype.linearIndependent_iff.mp he' v h0 j

theorem card_eq_of_span_eq {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) : n' = n := by
  have h1 := finrank_span_eq_card he
  have h2 := finrank_span_eq_card he'
  rw [hspan, h1, Fintype.card_fin, Fintype.card_fin] at h2
  exact h2.symm

theorem map_gramMeasure (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : V →ₗ[ℝ] V) (hA : Continuous A)
    (hB : ∀ u v, B (A u) (A v) = B u v) {n : ℕ} (e : Fin n → V) :
    Measure.map A (gramMeasure B e) = gramMeasure B (A ∘ e) := by
  rw [gramMeasure, gramMeasure, Measure.map_smul, Measure.map_map hA.measurable (measurable_coordMap e)]
  have h1 : (A : V → V) ∘ coordMap e = coordMap (A ∘ e) := by
    funext c
    simp [coordMap, map_sum, map_smul]
  have h2 : gramDet B (A ∘ e) = gramDet B e := by
    unfold gramDet
    congr 1
    ext i j
    simp [hB]
  rw [h1, h2]

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (μ : Measure α) {ρ : β → ℝ≥0∞} (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = (Measure.map f μ).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hρ hf]
  rfl

theorem map_injective_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) {μ ν : Measure α}
    (h : Measure.map f μ = Measure.map f ν) : μ = ν := by
  ext s hs
  have h1 : μ s = Measure.map f μ (f '' s) := by
    rw [hf.map_apply, hf.injective.preimage_image]
  have h2 : ν s = Measure.map f ν (f '' s) := by
    rw [hf.map_apply, hf.injective.preimage_image]
  rw [h1, h2, h]

end Gram

section Instances

scoped instance instIsTopologicalRingEcx : IsTopologicalRing Ecx := isTopologicalRing_tensor ℝ ℂ ℝ
scoped instance instT2Ecx : T2Space Ecx := t2Space_tensor ℝ ℂ ℝ
scoped instance instT2Mcx : T2Space Mcx := inferInstanceAs (T2Space (Fin 2 → Fin 2 → Ecx))
scoped instance instMeasMcx : MeasurableSpace Mcx := borel _
scoped instance instBorelMcx : BorelSpace Mcx := ⟨rfl⟩
scoped instance instMeasGcx : MeasurableSpace Gcx := glBorelOf Ecx
scoped instance instBorelGcx : BorelSpace Gcx := borelSpace_glBorelOf Ecx
scoped instance instTopGroupGcx : IsTopologicalGroup Gcx := isTopologicalGroup_tensorGL ℝ ℂ ℝ
scoped instance instT2Gcx : T2Space Gcx := t2Space_tensorGL ℝ ℂ ℝ
scoped instance instMeasTw (δ : Gcx) : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
  twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
scoped instance instBorelTw (δ : Gcx) : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
scoped instance instMeasCent (γ : GL (Fin 2) ℝ) :
    MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := centralizerBorel ℝ γ
scoped instance instBorelCent (γ : GL (Fin 2) ℝ) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩

def coordHomeo {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ W) : W ≃ₜ (ι → ℝ) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := b.equivFun.toLinearMap.continuous_of_finiteDimensional
  continuous_invFun := b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional

theorem polishSpace_Mcx : PolishSpace Mcx :=
  (coordHomeo (Module.finBasis ℝ Mcx)).isClosedEmbedding.polishSpace

theorem polishSpace_Gcx : PolishSpace Gcx := by
  haveI : PolishSpace Mcx := polishSpace_Mcx
  haveI : PolishSpace Mcxᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.polishSpace
  exact Units.isClosedEmbedding_embedProduct.polishSpace

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : Gcx → Mcx) := by
  haveI := polishSpace_Gcx
  exact Units.continuous_val.measurableEmbedding Units.val_injective

theorem measurable_val : Measurable (Units.val : Gcx → Mcx) := Units.continuous_val.measurable

theorem continuous_iotaE : Continuous iotaE := by
  have : (iotaE : ℝ → Ecx) = algebraMap ℝ Ecx := rfl
  rw [this]
  exact continuous_algebraMap ℝ Ecx

theorem continuous_toTensorGL : Continuous (toTensorGL ℝ ℂ ℝ : GL (Fin 2) ℝ → Gcx) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_iotaE)

theorem continuous_algebraNorm : Continuous (Algebra.norm ℝ : Ecx → ℝ) := by
  classical
  set b := Module.finBasis ℝ Ecx
  have h : (Algebra.norm ℝ : Ecx → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous fun x : Ecx => Algebra.leftMulMatrix b x :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  exact hc.matrix_det

end Instances

section FormDensity

def Bcx : Mcx →ₗ[ℝ] Mcx →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y : Mcx => Algebra.trace ℝ Ecx (Matrix.trace (X * Y)))
    (fun X₁ X₂ Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by
      show Algebra.trace ℝ Ecx (Matrix.trace (r • X * Y)) = r • Algebra.trace ℝ Ecx (Matrix.trace (X * Y))
      rw [smul_mul_M, trace_smul_M, map_smul])
    (fun X Y₁ Y₂ => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by
      show Algebra.trace ℝ Ecx (Matrix.trace (X * (r • Y))) = r • Algebra.trace ℝ Ecx (Matrix.trace (X * Y))
      rw [mul_smul_M, trace_smul_M, map_smul])

theorem Bcx_apply (X Y : Mcx) : Bcx X Y = Algebra.trace ℝ Ecx (Matrix.trace (X * Y)) := rfl

def conjL (x : Gcx) : Mcx →ₗ[ℝ] Mcx where
  toFun := conjM x
  map_add' X Y := by simp only [conjM, mul_add, add_mul]
  map_smul' r X := by
    simp only [conjM, RingHom.id_apply]
    rw [mul_smul_M, smul_mul_M]

theorem conjL_apply (x : Gcx) (X : Mcx) : conjL x X = (x : Mcx) * X * ((x⁻¹ : Gcx) : Mcx) := rfl

theorem continuous_conjL (x : Gcx) : Continuous (conjL x) :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem ker_conjL (x : Gcx) : LinearMap.ker (conjL x) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (conjM_injective x)

theorem Bcx_conjL (x : Gcx) (X Y : Mcx) : Bcx (conjL x X) (conjL x Y) = Bcx X Y := by
  rw [Bcx_apply, Bcx_apply, conjL_apply, conjL_apply]
  have : (x : Mcx) * X * ((x⁻¹ : Gcx) : Mcx) * ((x : Mcx) * Y * ((x⁻¹ : Gcx) : Mcx)) =
      (x : Mcx) * (X * Y) * ((x⁻¹ : Gcx) : Mcx) := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def rho (X : Mcx) : ℝ≥0∞ := (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹

theorem measurable_rho : Measurable rho := by
  have hc : Continuous fun X : Mcx => |Algebra.norm ℝ (Matrix.det X)| :=
    continuous_abs.comp (continuous_algebraNorm.comp (continuous_id.matrix_det))
  exact (ENNReal.continuous_ofReal.comp hc).measurable.inv

theorem rho_conjL (x : Gcx) (X : Mcx) : rho (conjL x X) = rho X := by
  rw [rho, rho, conjL_apply, Matrix.coe_units_inv, Matrix.det_conj x.isUnit]

theorem rho_comp_conjL (x : Gcx) : rho ∘ (conjL x) = rho := funext (rho_conjL x)

end FormDensity

theorem normString_two (δ : Gcx) :
    normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  simp [normString, Complex.finrank_real_complex, List.range_succ]

theorem toTensorGL_scalar (c : ℝˣ) :
    toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = Zof c := rfl

theorem main
    (c : ℝˣ) (hc : 0 < (c : ℝ))
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
               Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
             ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
               (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
             ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' := by

  have hN : δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ = Zof c := by
    have h1 : normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := normString_two δ
    have h2 : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        y⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * y := hδ
    rw [toTensorGL_scalar, h1] at h2
    have h3 : δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ = y * Zof c * y⁻¹ := by
      rw [h2]; group
    rw [h3, ← Zof_comm, mul_assoc, mul_inv_cancel, mul_one]

  obtain ⟨r, x, hr, hrr, hx⟩ := hilbert90 c hc δ hN
  refine ⟨x⁻¹, ?_, ?_⟩
  ·
    show toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      (x⁻¹)⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * x⁻¹
    rw [toTensorGL_scalar, normString_two, hN, inv_inv, ← Zof_comm, mul_assoc, mul_inv_cancel, mul_one]
  ·
    show Measure.map (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => (x⁻¹)⁻¹ * (t : Gcx) * x⁻¹) τ' =
      Measure.map (fun t : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
        toTensorGL ℝ ℂ ℝ (t : GL (Fin 2) ℝ)) τ
    rw [inv_inv]
    obtain ⟨n₁, n₂, e₁, e₂, s, hs0, hstop, hli₁, hsp₁, hli₂, hsp₂, hτe, hτ'e⟩ := hgram

    have hF₁ : Measurable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => x * (t : Gcx) * x⁻¹) :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF₂ : Measurable (fun t : Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
        toTensorGL ℝ ℂ ℝ (t : GL (Fin 2) ℝ)) :=
      (continuous_toTensorGL.comp continuous_subtype_val).measurable
    apply map_injective_of_measurableEmbedding measurableEmbedding_val
    rw [Measure.map_map measurable_val hF₁, Measure.map_map measurable_val hF₂]
    have eL : (Units.val ∘ fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => x * (t : Gcx) * x⁻¹) =
        (conjL x) ∘ (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => ((t : Gcx) : Mcx)) := by
      funext t; rfl
    have eR : (Units.val ∘ fun t : Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
        toTensorGL ℝ ℂ ℝ (t : GL (Fin 2) ℝ)) =
        fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
          ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
            (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ)) := by
      funext t; rfl
    have hval' : Measurable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => ((t : Gcx) : Mcx)) :=
      measurable_val.comp continuous_subtype_val.measurable
    rw [eL, eR, ← Measure.map_map (continuous_conjL x).measurable hval', hτ'e, hτe]

    change Measure.map (conjL x) (s • (gramMeasure Bcx e₂).withDensity rho) =
      s • (gramMeasure Bcx e₁).withDensity rho
    rw [Measure.map_smul]
    congr 1
    conv_lhs => rw [← rho_comp_conjL x]
    rw [map_withDensity_comp (continuous_conjL x).measurable _ measurable_rho,
      map_gramMeasure Bcx (conjL x) (continuous_conjL x) (Bcx_conjL x) e₂]
    congr 1

    have hspan : Submodule.span ℝ (Set.range ((conjL x) ∘ e₂)) = Submodule.span ℝ (Set.range e₁) := by
      apply SetLike.coe_injective
      rw [Set.range_comp, Submodule.span_image, Submodule.map_coe, hsp₂, hsp₁]
      exact image_conjM_twAlg r x δ hx
    have hli₂' : LinearIndependent ℝ ((conjL x) ∘ e₂) := hli₂.map' (conjL x) (ker_conjL x)
    have hn := card_eq_of_span_eq e₁ ((conjL x) ∘ e₂) hli₁ hli₂' hspan
    subst hn
    obtain ⟨P, hP, hdet⟩ := exists_matrix_of_span_eq e₁ ((conjL x) ∘ e₂) hli₁ hli₂' hspan.le
    exact gramMeasure_eq_of_comp Bcx e₁ _ P hP hdet

end P2mGramCoupled
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos.P2mGramCoupled"

open P2mGramCoupled in
theorem solution
    (c : ℝˣ) (hc : 0 < (c : ℝ))
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
               Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
             ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
               (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
             ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' :=
  main c hc δ y hδ τ τ' hτ hτ' hgram

end
end S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos (solution)
