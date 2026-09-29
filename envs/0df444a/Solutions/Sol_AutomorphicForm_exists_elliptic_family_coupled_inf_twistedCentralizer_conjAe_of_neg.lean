-- Prove2me | solution 1 for AutomorphicForm.exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fa009033-efc1-5094-aea5-7dc4d350f99c

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory AutomorphicForm Filter Topology
open scoped TensorProduct TensorProduct.RightActions

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory AutomorphicForm Topology Filter
open scoped TensorProduct TensorProduct.RightActions ComplexConjugate

noncomputable section

namespace HAModel

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

theorem normString_two (δ : Gcx) :
    normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  simp [normString, Complex.finrank_real_complex, List.range_succ]

theorem toTensorGL_scalar (c : ℝˣ) :
    toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = Zof c := rfl

scoped instance instIsTopologicalRingEcx : IsTopologicalRing Ecx := isTopologicalRing_tensor ℝ ℂ ℝ

theorem RM_injective : Function.Injective (RM : Mcx → Matrix (Fin 2) (Fin 2) ℂ) := fun X Y h => by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact ridE.injective this

theorem RM_sigM (X : Mcx) : RM (sigM X) = (RM X).map conj := by
  ext i j; simp [ridE_sigE]

theorem RM_iotaM (Y : Matrix (Fin 2) (Fin 2) ℝ) : RM (iotaM Y) = Y.map (fun x : ℝ => (x : ℂ)) := by
  ext i j; simp [iotaM_apply, ridE_iotaE]

theorem RM_scM_iotaE (a : ℝ) : RM (scM (iotaE a)) = (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [scM, ridE_iotaE]
  · simp [scM, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem continuous_lamE : Continuous lamE := by

  have h : lamE = fun l : ℂ => ridE.symm l := by
    funext l; apply ridE.injective; rw [ridE_lamE, RingEquiv.apply_symm_apply]
  rw [h]
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := ℂ)
  have h2 : (ridE.symm.toRingHom.comp (algebraMap ℝ ℂ)) = algebraMap ℝ Ecx := by
    ext a
    show ridE.symm (a : ℂ) = algebraMap ℝ Ecx a
    rw [ridE_symm_ofReal]; rfl
  exact IsModuleTopology.continuous_of_ringHom (R := ℝ) ridE.symm.toRingHom (by rw [h2]; exact continuous_algebraMap ℝ Ecx)

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  have := rot_mul_rot_neg (-θ); rwa [neg_neg] at this

def gam (c : ℝˣ) (θ : ℝ) : GL (Fin 2) ℝ :=
  ⟨(c : ℝ) • rot θ, (c : ℝ)⁻¹ • rot (-θ),
    by rw [smul_mul_smul_comm, rot_mul_rot_neg, mul_inv_cancel₀ c.ne_zero, one_smul],
    by rw [smul_mul_smul_comm, rot_neg_mul_rot, inv_mul_cancel₀ c.ne_zero, one_smul]⟩

theorem coe_gam (c : ℝˣ) (θ : ℝ) : ((gam c θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (c : ℝ) • rot θ := rfl

def dU (φ : ℝ) : Gcx :=
  ⟨Matrix.diagonal ![lamE (Complex.exp (Complex.I * φ)), lamE (Complex.exp (-(Complex.I * φ)))],
   Matrix.diagonal ![lamE (Complex.exp (-(Complex.I * φ))), lamE (Complex.exp (Complex.I * φ))],
   by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;>
      simp [lamE, Algebra.TensorProduct.tmul_mul_tmul, ← Complex.exp_add, Algebra.TensorProduct.one_def],
   by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;>
      simp [lamE, Algebra.TensorProduct.tmul_mul_tmul, ← Complex.exp_add, Algebra.TensorProduct.one_def]⟩

theorem coe_dU (φ : ℝ) : ((dU φ : Gcx) : Mcx) =
    Matrix.diagonal ![lamE (Complex.exp (Complex.I * φ)), lamE (Complex.exp (-(Complex.I * φ)))] := rfl

theorem RM_coe_dU (φ : ℝ) : RM ((dU φ : Gcx) : Mcx) =
    Matrix.diagonal ![Complex.exp (Complex.I * φ), Complex.exp (-(Complex.I * φ))] := by
  rw [coe_dU]; ext i j
  by_cases h : i = j
  · subst h; fin_cases i <;> simp [ridE_lamE]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem dU_zero : dU 0 = 1 := by
  apply Units.ext; rw [coe_dU, Units.val_one, ← Matrix.diagonal_one]; congr 1
  ext i; fin_cases i <;> simp [lamE, Algebra.TensorProduct.one_def]

theorem dU_add (φ ψ : ℝ) : dU (φ + ψ) = dU φ * dU ψ := by
  apply Units.ext; rw [Units.val_mul, coe_dU, coe_dU, coe_dU, Matrix.diagonal_mul_diagonal]; congr 1
  ext i; fin_cases i <;>
    simp [lamE, Algebra.TensorProduct.tmul_mul_tmul, ← Complex.exp_add] <;> ring_nf

theorem dU_comm (φ ψ : ℝ) : dU φ * dU ψ = dU ψ * dU φ := by rw [← dU_add, ← dU_add, add_comm]

theorem sigmaGL_dU (φ : ℝ) : sigmaGL ℝ ℂ ℝ Complex.conjAe (dU φ) = (dU φ)⁻¹ := by
  apply Units.ext
  rw [coe_sigmaGL, coe_dU]
  show _ = Matrix.diagonal ![lamE (Complex.exp (-(Complex.I * φ))), lamE (Complex.exp (Complex.I * φ))]
  ext i j
  by_cases h : i = j
  · subst h; fin_cases i <;> simp [sigE_lamE, ← Complex.exp_conj, Complex.conj_I]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem continuous_dU : Continuous dU := by
  have hc : ∀ s : ℂ, Continuous fun φ : ℝ => lamE (Complex.exp (s * φ)) := fun s =>
    continuous_lamE.comp (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hc' : ∀ s : ℂ, Continuous fun φ : ℝ => lamE (Complex.exp (-(s * φ))) := fun s =>
    continuous_lamE.comp (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_dU, Matrix.diagonal] <;> first | exact hc _ | exact hc' _ | exact continuous_const
  · have : (fun φ : ℝ => ((dU φ)⁻¹ : Gcx).val) = fun φ : ℝ =>
        Matrix.diagonal ![lamE (Complex.exp (-(Complex.I * (φ : ℂ)))), lamE (Complex.exp (Complex.I * (φ : ℂ)))] := rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> first | exact hc _ | exact hc' _ | exact continuous_const

def mkL (a b c d : ℂ) : Mcx := !![lamE a, lamE b; lamE c, lamE d]

theorem RM_mkL (a b c d : ℂ) : RM (mkL a b c d) = !![a, b; c, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mkL, ridE_lamE]

theorem RM_one : RM (1 : Mcx) = 1 := map_one _
theorem RM_mul (X Y : Mcx) : RM (X * Y) = RM X * RM Y := map_mul _ _ _

def Q0 : Gcx :=
  ⟨mkL 1 Complex.I 1 (-Complex.I), mkL (1/2) (1/2) (-Complex.I/2) (Complex.I/2),
   by
    apply RM_injective
    rw [RM_mul, RM_mkL, RM_mkL, RM_one]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring,
   by
    apply RM_injective
    rw [RM_mul, RM_mkL, RM_mkL, RM_one]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring⟩

def rotU (θ : ℝ) : GL (Fin 2) ℝ := ⟨rot θ, rot (-θ), rot_mul_rot_neg θ, rot_neg_mul_rot θ⟩

theorem gam_eq (c : ℝˣ) (θ : ℝ) : gam c θ = rotU θ * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  rw [coe_gam, Units.val_mul]
  show (c : ℝ) • rot θ = rot θ * Matrix.scalar (Fin 2) (c : ℝ)
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem exp_I_mul (θ : ℝ) : Complex.exp (Complex.I * θ) = Real.cos θ + Real.sin θ * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem exp_neg_I_mul (θ : ℝ) : Complex.exp (-(Complex.I * θ)) = Real.cos θ - Real.sin θ * Complex.I := by
  rw [show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

theorem Q0_mul_rot (θ : ℝ) : Q0 * toTensorGL ℝ ℂ ℝ (rotU θ) = dU θ * Q0 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply RM_injective
  rw [RM_mul, RM_mul, RM_coe_dU, coe_toTensorGL, RM_iotaM]
  show RM (mkL 1 Complex.I 1 (-Complex.I)) * _ = _ * RM (mkL 1 Complex.I 1 (-Complex.I))
  rw [RM_mkL, exp_I_mul, exp_neg_I_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotU, rot] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def m0 (c : ℝˣ) : GL (Fin 2) ℝ :=
  ⟨!![0, (c : ℝ); 1, 0], !![0, 1; (c : ℝ)⁻¹, 0],
   by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
   by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem RM_coe_M (c : ℝˣ) : RM ((toTensorGL ℝ ℂ ℝ (m0 c) : Gcx) : Mcx) = !![0, (c : ℂ); 1, 0] := by
  rw [coe_toTensorGL, RM_iotaM]
  ext i j; fin_cases i <;> fin_cases j <;> simp [m0]

theorem dU_M_dU (c : ℝˣ) (φ : ℝ) : dU φ * toTensorGL ℝ ℂ ℝ (m0 c) * dU φ = toTensorGL ℝ ℂ ℝ (m0 c) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply RM_injective
  rw [RM_mul, RM_mul, RM_coe_dU, RM_coe_M]
  have h1 : Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * φ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (-(Complex.I * φ)) * Complex.exp (Complex.I * φ) = 1 := by rw [mul_comm, h1]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  · rw [mul_comm, ← mul_assoc, mul_comm (Complex.exp _), h1, one_mul]
  · rw [h2]

theorem hilbert90_neg (c : ℝˣ) (hc : (c : ℝ) < 0) (δ : Gcx)
    (hN : δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ = Zof c) :
    ∃ X : Gcx, δ * sigmaGL ℝ ℂ ℝ Complex.conjAe X = X * toTensorGL ℝ ℂ ℝ (m0 c) := by
  set D : Matrix (Fin 2) (Fin 2) ℂ := RM (δ : Mcx) with hD
  have hDD : D * D.map conj = (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h := congrArg (fun g : Gcx => RM (g : Mcx)) hN
    simp only [coe_mul_sigma, RM_mul, RM_sigM, coe_Zof, RM_scM_iotaE] at h
    exact h
  have h00 : D 0 0 * conj (D 0 0) + D 0 1 * conj (D 1 0) = c := by
    have := congrFun (congrFun hDD 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : D 1 0 * conj (D 0 0) + D 1 1 * conj (D 1 0) = 0 := by
    have := congrFun (congrFun hDD 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] using this
  have hd10 : D 1 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero, add_zero, Complex.mul_conj] at h00
    have : (Complex.normSq (D 0 0) : ℝ) = c := by exact_mod_cast h00
    linarith [Complex.normSq_nonneg (D 0 0)]

  set P : Mcx := !![1, (δ : Mcx) 0 0; 0, (δ : Mcx) 1 0] with hP
  have hRP : RM P = !![1, D 0 0; 0, D 1 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP, hD]
  have hPu : IsUnit P := by
    rw [isUnit_iff_det_RM_ne_zero, hRP, Matrix.det_fin_two]
    simpa using hd10
  refine ⟨hPu.unit, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_sigmaGL, IsUnit.unit_spec]
  apply RM_injective
  rw [RM_mul, RM_mul, RM_sigM, hRP, RM_coe_M, ← hD]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact h00
  · exact h10

local notation "σ'" => sigmaGL ℝ ℂ ℝ Complex.conjAe

set_option maxHeartbeats 3200000 in

theorem model (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (y₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
      Continuous u ∧ u 0 = 1 ∧ (∀ θ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) ∧
      (∀ θ θ', u θ * u θ' = u θ' * u θ) ∧
      ∀ θ, IsNormConjugator ℝ ℂ ℝ Complex.conjAe (gam c θ) (u θ * δ) y₁ := by

  have hN : δ * σ' δ = Zof c := by
    have h : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = y⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * y := hδ
    rw [toTensorGL_scalar, normString_two] at h
    have : y * Zof c * y⁻¹ = δ * σ' δ := by rw [h]; group
    rw [← this, ← Zof_comm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨X, hX⟩ := hilbert90_neg c hc δ hN
  have hδX : δ = X * toTensorGL ℝ ℂ ℝ (m0 c) * (σ' X)⁻¹ := by rw [← hX]; group

  have hmem : ∀ θ : ℝ, X * dU (θ / 2) * X⁻¹ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ := by
    intro θ
    rw [mem_sigmaCentralizer_iff]
    show X * dU (θ / 2) * X⁻¹ * δ * (σ' (X * dU (θ / 2) * X⁻¹))⁻¹ = δ
    rw [map_mul, map_mul, map_inv, sigmaGL_dU, hδX]
    have key := dU_M_dU c (θ / 2)
    calc X * dU (θ / 2) * X⁻¹ * (X * toTensorGL ℝ ℂ ℝ (m0 c) * (σ' X)⁻¹) * (σ' X * (dU (θ / 2))⁻¹ * (σ' X)⁻¹)⁻¹
        = X * (dU (θ / 2) * toTensorGL ℝ ℂ ℝ (m0 c) * dU (θ / 2)) * (σ' X)⁻¹ := by group
      _ = X * toTensorGL ℝ ℂ ℝ (m0 c) * (σ' X)⁻¹ := by rw [key, mul_assoc]

  have hnorm : ∀ θ : ℝ, normString ℝ ℂ ℝ Complex.conjAe (X * dU (θ / 2) * X⁻¹ * δ) = X * dU θ * X⁻¹ * Zof c := by
    intro θ
    have hu : X * dU (θ / 2) * X⁻¹ * δ = δ * σ' (X * dU (θ / 2) * X⁻¹) :=
      mul_inv_eq_iff_eq_mul.mp (mem_sigmaCentralizer_iff.mp (hmem θ))
    have hadd : dU (θ / 2) * dU (θ / 2) = dU θ := by rw [← dU_add, add_halves]
    rw [normString_two, map_mul]
    calc X * dU (θ / 2) * X⁻¹ * δ * (σ' (X * dU (θ / 2) * X⁻¹) * σ' δ)
        = X * dU (θ / 2) * X⁻¹ * (δ * σ' (X * dU (θ / 2) * X⁻¹)) * σ' δ := by simp only [mul_assoc]
      _ = X * dU (θ / 2) * X⁻¹ * (X * dU (θ / 2) * X⁻¹ * δ) * σ' δ := by rw [← hu]
      _ = X * (dU (θ / 2) * dU (θ / 2)) * X⁻¹ * (δ * σ' δ) := by group
      _ = X * dU θ * X⁻¹ * Zof c := by rw [hadd, hN]
  have hrot : ∀ θ : ℝ, toTensorGL ℝ ℂ ℝ (rotU θ) = Q0⁻¹ * dU θ * Q0 := fun θ => by
    rw [mul_assoc, eq_inv_mul_iff_mul_eq, Q0_mul_rot]
  refine ⟨fun θ => X * dU (θ / 2) * X⁻¹, X * Q0, ?_, ?_, hmem, ?_, ?_⟩
  · exact ((continuous_const.mul (continuous_dU.comp (continuous_id.div_const _))).mul continuous_const)
  · show X * dU (0 / 2) * X⁻¹ = 1
    rw [zero_div, dU_zero, mul_one, mul_inv_cancel]
  · intro θ θ'
    show X * dU (θ / 2) * X⁻¹ * (X * dU (θ' / 2) * X⁻¹) = X * dU (θ' / 2) * X⁻¹ * (X * dU (θ / 2) * X⁻¹)
    calc X * dU (θ / 2) * X⁻¹ * (X * dU (θ' / 2) * X⁻¹) = X * (dU (θ / 2) * dU (θ' / 2)) * X⁻¹ := by group
      _ = X * (dU (θ' / 2) * dU (θ / 2)) * X⁻¹ := by rw [dU_comm]
      _ = X * dU (θ' / 2) * X⁻¹ * (X * dU (θ / 2) * X⁻¹) := by group
  · intro θ
    show toTensorGL ℝ ℂ ℝ (gam c θ) =
      (X * Q0)⁻¹ * normString ℝ ℂ ℝ Complex.conjAe (X * dU (θ / 2) * X⁻¹ * δ) * (X * Q0)
    rw [hnorm, gam_eq, map_mul, toTensorGL_scalar, hrot]
    calc Q0⁻¹ * dU θ * Q0 * Zof c = Q0⁻¹ * dU θ * (Zof c * Q0) := by rw [Zof_comm, mul_assoc]
      _ = Q0⁻¹ * dU θ * (X⁻¹ * Zof c * X) * Q0 := by
          rw [← Zof_comm c X⁻¹, mul_assoc (Zof c), inv_mul_cancel, mul_one]; simp only [mul_assoc]
      _ = (X * Q0)⁻¹ * (X * dU θ * X⁻¹ * Zof c) * (X * Q0) := by group

end HAModel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg.HAModel"

open MeasureTheory AutomorphicForm Filter Topology

noncomputable section

namespace HA

local notation "Aℂ" => ℂ ⊗[ℝ] ℝ
local notation "σGL" => sigmaGL ℝ ℂ ℝ Complex.conjAe
local notation "T′" => twistedCentralizer ℝ ℂ ℝ Complex.conjAe
local notation "ι" => toTensorGL ℝ ℂ ℝ

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  have := rot_mul_rot_neg (-θ); rwa [neg_neg] at this

private def _root_.HA.gam (c : ℝˣ) (θ : ℝ) : GL (Fin 2) ℝ :=
  ⟨(c : ℝ) • rot θ, (c : ℝ)⁻¹ • rot (-θ),
    by rw [smul_mul_smul_comm, rot_mul_rot_neg, mul_inv_cancel₀ c.ne_zero, one_smul],
    by rw [smul_mul_smul_comm, rot_neg_mul_rot, inv_mul_cancel₀ c.ne_zero, one_smul]⟩

p2m_export "HA" "gam"
theorem coe_gam (c : ℝˣ) (θ : ℝ) : ((gam c θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (c : ℝ) • rot θ := rfl

theorem gam_regular (c : ℝˣ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) : IsRegularSemisimple (gam c θ) := by
  rw [isRegularSemisimple_iff_ne_zero, coe_gam]
  have : Matrix.trace ((c : ℝ) • rot θ) ^ 2 - 4 * Matrix.det ((c : ℝ) • rot θ) = -(4 * (c : ℝ) ^ 2 * Real.sin θ ^ 2) := by
    simp [rot, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.smul_apply]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [this, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero four_ne_zero (pow_ne_zero _ c.ne_zero)) (pow_ne_zero _ hθ)

theorem mem_centralizer_gam_iff (c : ℝˣ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) (x : GL (Fin 2) ℝ) :
    x ∈ Subgroup.centralizer ({gam c θ} : Set (GL (Fin 2) ℝ)) ↔
      (x : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (x : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
        (x : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(x : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm : ((gam c θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (x : Matrix (Fin 2) (Fin 2) ℝ) =
        (x : Matrix (Fin 2) (Fin 2) ℝ) * ((gam c θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    rw [coe_gam] at hm
    have h00 := congrFun (congrFun hm 0) 0
    have h01 := congrFun (congrFun hm 0) 1
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    have hc0 : (c : ℝ) ≠ 0 := c.ne_zero
    constructor
    · have : (c : ℝ) * Real.sin θ * ((x : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (x : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = 0 := by
        nlinarith [h00, h01]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero hc0 hθ)
      · linarith
    · have : (c : ℝ) * Real.sin θ * ((x : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (x : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = 0 := by
        nlinarith [h00, h01]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero hc0 hθ)
      · linarith
  · rintro ⟨h1, h2⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_gam]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot, Matrix.mul_apply, Fin.sum_univ_two, h1, h2] <;> ring

theorem centralizer_gam_eq (c : ℝˣ) {θ θ' : ℝ} (hθ : Real.sin θ ≠ 0) (hθ' : Real.sin θ' ≠ 0) :
    Subgroup.centralizer ({gam c θ} : Set (GL (Fin 2) ℝ)) = Subgroup.centralizer ({gam c θ'} : Set (GL (Fin 2) ℝ)) := by
  ext x; rw [mem_centralizer_gam_iff c hθ, mem_centralizer_gam_iff c hθ']

theorem centralizer_gam_comm (c : ℝˣ) {θ : ℝ} (hθ : Real.sin θ ≠ 0)
    (a b : Subgroup.centralizer ({gam c θ} : Set (GL (Fin 2) ℝ))) : a * b = b * a := by
  obtain ⟨ha1, ha2⟩ := (mem_centralizer_gam_iff c hθ a.1).1 a.2
  obtain ⟨hb1, hb2⟩ := (mem_centralizer_gam_iff c hθ b.1).1 b.2
  apply Subtype.ext; apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, hb1, hb2] <;> ring

theorem continuous_rot : Continuous rot := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rot] <;> fun_prop

theorem continuous_gam (c : ℝˣ) : Continuous (gam c) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_const.fun_smul continuous_rot).congr fun θ => rfl
  · have : Continuous fun θ => (c : ℝ)⁻¹ • rot (-θ) := continuous_const.fun_smul (continuous_rot.comp continuous_neg)
    exact this.congr fun θ => rfl

theorem tendsto_gam (c : ℝˣ) :
    Tendsto (gam c) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := by
  have h0 : gam c 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    apply Units.ext; rw [coe_gam]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal]
  rw [← h0]
  exact ((continuous_gam c).tendsto 0).mono_left nhdsWithin_le_nhds

theorem gam_eq_model : gam = HAModel.gam := rfl

private theorem _root_.HA.model (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) Aℂ)
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ (u : ℝ → GL (Fin 2) Aℂ) (y₁ : GL (Fin 2) Aℂ),
      Continuous u ∧ u 0 = 1 ∧ (∀ θ, u θ ∈ T′ δ) ∧ (∀ θ θ', u θ * u θ' = u θ' * u θ) ∧
      ∀ θ, IsNormConjugator ℝ ℂ ℝ Complex.conjAe (gam c θ) (u θ * δ) y₁ := by
  rw [gam_eq_model]
  exact HAModel.model c hc δ y hδ

p2m_export "HA" "model"

theorem mem_twistedCentralizer_mul {δ u t : GL (Fin 2) Aℂ} (hu : u ∈ T′ δ) (ht : t ∈ T′ δ)
    (hc : t * u = u * t) : t ∈ T′ (u * δ) := by
  rw [mem_sigmaCentralizer_iff] at hu ht ⊢
  calc t * (u * δ) * (σGL t)⁻¹ = u * (t * δ * (σGL t)⁻¹) := by rw [← mul_assoc, hc]; group
    _ = u * δ := by rw [ht]

theorem mem_twistedCentralizer_of_mul {δ u t : GL (Fin 2) Aℂ} (hu : u ∈ T′ δ) (ht : t ∈ T′ (u * δ))
    (hc : t * u = u * t) : t ∈ T′ δ := by
  rw [mem_sigmaCentralizer_iff] at hu ht ⊢
  have : u * (t * δ * (σGL t)⁻¹) = u * δ := by
    calc u * (t * δ * (σGL t)⁻¹) = (u * t) * δ * (σGL t)⁻¹ := by group
      _ = t * (u * δ) * (σGL t)⁻¹ := by rw [← hc]; group
      _ = u * δ := ht
  exact mul_left_cancel this

theorem self_mem_twistedCentralizer_mul {δ u : GL (Fin 2) Aℂ} (hu : u ∈ T′ δ) : u ∈ T′ (u * δ) :=
  mem_twistedCentralizer_mul hu hu rfl

section Transport
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def congrCME {H K : Subgroup G} (h : H = K) : H ≃ₜ* K := by subst h; exact ContinuousMulEquiv.refl _

omit [IsTopologicalGroup G] in
theorem congrCME_coe {H K : Subgroup G} (h : H = K) (x : H) : ((congrCME h x : K) : G) = (x : G) := by
  subst h; rfl

omit [IsTopologicalGroup G] in
theorem map_map_congrCME {H K : Subgroup G} (h : H = K) {β : Type*} [MeasurableSpace β] (F : K → β)
    (μ : @Measure H (borel H)) :
    @Measure.map K β (borel K) _ F (@Measure.map H K (borel H) (borel K) (congrCME h) μ) =
      @Measure.map H β (borel H) _ (F ∘ congrCME h) μ := by
  subst h
  have : (⇑(congrCME (rfl : H = H)) : H → H) = id := rfl
  rw [this, @Measure.map_id]
  rfl

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg.HAModel"

def incl : ℝ →+* Aℂ where
  toFun r := (1 : ℂ) ⊗ₜ[ℝ] r
  map_one' := rfl
  map_mul' a b := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := TensorProduct.tmul_zero _ _
  map_add' a b := TensorProduct.tmul_add _ _ _

theorem toTensorGL_apply (g : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((ι g : GL (Fin 2) Aℂ) : Matrix (Fin 2) (Fin 2) Aℂ) i j = incl ((g : Matrix (Fin 2) (Fin 2) ℝ) i j) := rfl

theorem isRegularSemisimple_toTensorGL {g : GL (Fin 2) ℝ} (hg : IsRegularSemisimple g) : IsRegularSemisimple (ι g) := by
  unfold IsRegularSemisimple at hg ⊢
  have h2 : Matrix.trace ((ι g : GL (Fin 2) Aℂ) : Matrix (Fin 2) (Fin 2) Aℂ) ^ 2 -
      4 * Matrix.det ((ι g : GL (Fin 2) Aℂ) : Matrix (Fin 2) (Fin 2) Aℂ) =
      incl (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
    simp only [Matrix.trace_fin_two, Matrix.det_fin_two, toTensorGL_apply, map_sub, map_mul, map_pow, map_add, map_ofNat]
  rw [h2]
  exact hg.map incl

theorem isGalois_real_complex : IsGalois ℝ ℂ := by
  haveI : Algebra.IsQuadraticExtension ℝ ℂ := { finrank_eq_two' := Complex.finrank_real_complex }
  exact Algebra.IsQuadraticExtension.isGalois ℝ ℂ

theorem conjAe_generates : ∀ θ : ℂ ≃ₐ[ℝ] ℂ, θ ∈ Subgroup.zpowers Complex.conjAe := by
  intro θ
  rcases Complex.real_algHom_eq_id_or_conj (θ : ℂ →ₐ[ℝ] ℂ) with h | h
  · have hθ : θ = 1 := AlgEquiv.ext fun x => by
      have := AlgHom.congr_fun h x
      simpa using this
    rw [hθ]
    exact one_mem _
  · have hθ : θ = Complex.conjAe := AlgEquiv.ext fun x => by
      have := AlgHom.congr_fun h x
      simpa using this
    rw [hθ]
    exact Subgroup.mem_zpowers _

theorem coe_twistedCentralizer_eq_image {t : GL (Fin 2) ℝ} {δ' y₁ : GL (Fin 2) Aℂ}
    (e : Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ≃ₜ* T′ δ')
    (he : ∀ s : Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)), ((e s : T′ δ') : GL (Fin 2) Aℂ) = y₁ * ι (s : GL (Fin 2) ℝ) * y₁⁻¹) :
    ((T′ δ' : Subgroup (GL (Fin 2) Aℂ)) : Set (GL (Fin 2) Aℂ)) =
      (fun s : GL (Fin 2) ℝ => y₁ * ι s * y₁⁻¹) '' (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  ext x
  constructor
  · intro hx
    refine ⟨(e.symm ⟨x, hx⟩ : GL (Fin 2) ℝ), (e.symm ⟨x, hx⟩).2, ?_⟩
    show y₁ * ι ((e.symm ⟨x, hx⟩ : Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ) * y₁⁻¹ = x
    rw [← he, ContinuousMulEquiv.apply_symm_apply]
  · rintro ⟨s, hs, rfl⟩
    show y₁ * ι s * y₁⁻¹ ∈ _
    rw [← he ⟨s, hs⟩]
    exact (e ⟨s, hs⟩).2

theorem main
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ (γ : ℝ → GL (Fin 2) ℝ) (θ₀ θ₁ : ℝ) (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (y₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
      (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (τ : ∀ θ : ℝ, @Measure (Subgroup.centralizer ({γ θ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ (γ θ)))
      (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ))
        (borel _))
      (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
        (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
      (∀ θ : ℝ, ((γ θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (c : ℝ) • !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]) ∧
      0 < θ₀ ∧ θ₁ ∈ Set.Ioo 0 θ₀ ∧
      (∀ θ : ℝ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ)) ∧
      (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
       Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) ∧
      (letI := glBorelOf ℝ
       Filter.Tendsto γ (nhdsWithin 0 (Set.Ioi 0)) (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c))) ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τS ∧
      ∀ θ ∈ Set.Ioo 0 θ₀,
        IsRegularSemisimple (γ θ) ∧
        IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ)) ∧
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (γ θ) (u θ * δ) y₁ ∧
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (γ θ)) (τ θ) ∧
        @Measure.map _ _ (centralizerBorel ℝ (γ θ)) (glBorelOf ℝ) Subtype.val (τ θ) = νT ∧
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ) ∧
        (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
         letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
             twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ)) := borel _
         Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS) ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (γ θ) (u θ * δ) y₁ (τ θ) (τu θ) := by
  classical
  haveI : IsGalois ℝ ℂ := isGalois_real_complex
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  letI mA : MeasurableSpace (GL (Fin 2) Aℂ) := glBorelOf Aℂ
  haveI : BorelSpace (GL (Fin 2) Aℂ) := borelSpace_glBorelOf Aℂ
  letI mR : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  obtain ⟨u, y₁, hucont, hu0, huT, hucomm, hnc⟩ := model c hc δ y hδ

  have hsin : ∀ θ ∈ Set.Ioo 0 Real.pi, Real.sin θ ≠ 0 := fun θ hθ => (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hθ₁ : Real.pi / 2 ∈ Set.Ioo 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hsin₁ : Real.sin (Real.pi / 2) ≠ 0 := hsin _ hθ₁

  set Tell : Subgroup (GL (Fin 2) ℝ) := Subgroup.centralizer ({gam c (Real.pi / 2)} : Set (GL (Fin 2) ℝ)) with hTell
  letI mT : MeasurableSpace Tell := centralizerBorel ℝ (gam c (Real.pi / 2))
  haveI : BorelSpace Tell := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := by
    haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
    infer_instance
  have hTcl : IsClosed (Tell : Set (GL (Fin 2) ℝ)) := by
    have : (Tell : Set (GL (Fin 2) ℝ)) = {x | x * gam c (Real.pi / 2) = gam c (Real.pi / 2) * x} := by
      ext x; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Tell := hTcl.locallyCompactSpace
  set μT : Measure Tell := Measure.haar with hμT

  obtain ⟨e₁, he₁⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator ℝ ℂ
      Complex.conjAe conjAe_generates ℝ (gam c (Real.pi / 2)) (gam_regular c hsin₁) (u (Real.pi / 2) * δ) y₁ (hnc _)

  have hTθ : ∀ θ ∈ Set.Ioo 0 Real.pi, T′ (u θ * δ) = T′ (u (Real.pi / 2) * δ) := by
    intro θ hθ
    obtain ⟨e, he⟩ :=
      AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator ℝ ℂ
        Complex.conjAe conjAe_generates ℝ (gam c θ) (gam_regular c (hsin θ hθ)) (u θ * δ) y₁ (hnc θ)
    ext x
    rw [← Subgroup.mem_carrier, ← Subgroup.mem_carrier]
    show x ∈ ((T′ (u θ * δ) : Subgroup (GL (Fin 2) Aℂ)) : Set (GL (Fin 2) Aℂ)) ↔
      x ∈ ((T′ (u (Real.pi / 2) * δ) : Subgroup (GL (Fin 2) Aℂ)) : Set (GL (Fin 2) Aℂ))
    rw [coe_twistedCentralizer_eq_image e he, coe_twistedCentralizer_eq_image e₁ he₁, centralizer_gam_eq c (hsin θ hθ) hsin₁]
  have hab : ∀ a b : T′ (u (Real.pi / 2) * δ), a * b = b * a := by
    intro a b
    have h := congrArg e₁ (centralizer_gam_comm c hsin₁ (e₁.symm a) (e₁.symm b))
    rwa [map_mul, map_mul, e₁.apply_symm_apply, e₁.apply_symm_apply] at h
  have hS : T′ δ ⊓ T′ (u (Real.pi / 2) * δ) = T′ (u (Real.pi / 2) * δ) := by
    refine inf_eq_right.2 fun t ht => ?_
    have hu₁ : u (Real.pi / 2) ∈ T′ (u (Real.pi / 2) * δ) := self_mem_twistedCentralizer_mul (huT _)
    have hc' : t * u (Real.pi / 2) = u (Real.pi / 2) * t := by
      have := hab ⟨t, ht⟩ ⟨u (Real.pi / 2), hu₁⟩
      exact congrArg Subtype.val this
    exact mem_twistedCentralizer_of_mul (huT _) ht hc'

  letI mS : MeasurableSpace ↥(T′ δ ⊓ T′ (u (Real.pi / 2) * δ)) := borel _
  haveI : BorelSpace ↥(T′ δ ⊓ T′ (u (Real.pi / 2) * δ)) := ⟨rfl⟩
  letI m₁ : MeasurableSpace (T′ (u (Real.pi / 2) * δ)) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u (Real.pi / 2) * δ)
  haveI hB₁ : BorelSpace (T′ (u (Real.pi / 2) * δ)) := ⟨rfl⟩

  set νT : Measure (GL (Fin 2) ℝ) := Measure.map Subtype.val μT with hνT
  set τ : ∀ θ : ℝ, @Measure (Subgroup.centralizer ({gam c θ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ (gam c θ)) := fun θ =>
    if h : Real.sin θ ≠ 0 then @Measure.map _ _ mT (centralizerBorel ℝ (gam c θ)) (congrCME (centralizer_gam_eq c hsin₁ h)) μT
    else (0 : @Measure _ (centralizerBorel ℝ (gam c θ))) with hτ
  set τ₁ : Measure (T′ (u (Real.pi / 2) * δ)) := Measure.map e₁ μT with hτ₁
  set τS : Measure ↥(T′ δ ⊓ T′ (u (Real.pi / 2) * δ)) := Measure.map (congrCME hS.symm) τ₁ with hτS
  set τu : ∀ θ : ℝ, @Measure (T′ (u θ * δ)) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) := fun θ =>
    if h : θ ∈ Set.Ioo 0 Real.pi then
      @Measure.map _ _ m₁ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (congrCME (hTθ θ h).symm) τ₁
    else (0 : @Measure _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))) with hτu
  haveI hτ₁H : τ₁.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μT e₁
  have hτSH : @Measure.IsHaarMeasure _ _ _ mS τS := ContinuousMulEquiv.isHaarMeasure_map τ₁ (congrCME hS.symm)
  have hcoe : ∀ θ : ℝ, ((gam c θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (c : ℝ) • !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] :=
    fun θ => coe_gam c θ
  refine ⟨gam c, Real.pi, Real.pi / 2, u, y₁, νT, τ, τS, τu, hcoe, Real.pi_pos, hθ₁, ?_, ?_, tendsto_gam c, hτSH, ?_⟩
  · intro θ
    exact ⟨huT θ, mem_twistedCentralizer_mul (huT _) (huT θ) (hucomm _ _)⟩
  · rw [← hu0]; exact (hucont.tendsto 0).mono_left nhdsWithin_le_nhds
  intro θ hθ
  letI mθ : MeasurableSpace (T′ (u θ * δ)) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
  haveI : BorelSpace (T′ (u θ * δ)) := ⟨rfl⟩
  letI mθ' : MeasurableSpace (Subgroup.centralizer ({gam c θ} : Set (GL (Fin 2) ℝ))) := centralizerBorel ℝ (gam c θ)
  haveI : BorelSpace (Subgroup.centralizer ({gam c θ} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  have hsθ := hsin θ hθ
  have hτθ : τ θ = Measure.map (congrCME (centralizer_gam_eq c hsin₁ hsθ)) μT := by simp only [hτ]; rw [dif_pos hsθ]
  have hτuθ : τu θ = Measure.map (congrCME (hTθ θ hθ).symm) τ₁ := by simp only [hτu]; rw [dif_pos hθ]
  have hN : normString ℝ ℂ ℝ Complex.conjAe (u θ * δ) = (y₁⁻¹)⁻¹ * ι (gam c θ) * y₁⁻¹ := by
    have := hnc θ; unfold IsNormConjugator at this; rw [this]; group
  have hreg : IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ)) := by
    rw [hN]; exact (isRegularSemisimple_toTensorGL (gam_regular c hsθ)).conj _
  have hvc : ∀ {H K : Subgroup (GL (Fin 2) ℝ)} (h : H = K), (Subtype.val ∘ ⇑(congrCME h)) = (Subtype.val : H → GL (Fin 2) ℝ) :=
    fun h => funext fun x => congrCME_coe h x
  have hvc' : ∀ {H K : Subgroup (GL (Fin 2) Aℂ)} (h : H = K), (Subtype.val ∘ ⇑(congrCME h)) = (Subtype.val : H → GL (Fin 2) Aℂ) :=
    fun h => funext fun x => congrCME_coe h x
  refine ⟨gam_regular c hsθ, hreg, hnc θ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hτθ]; exact ContinuousMulEquiv.isHaarMeasure_map μT _
  · rw [hτθ, map_map_congrCME, hvc]
  · rw [hτuθ]; exact ContinuousMulEquiv.isHaarMeasure_map τ₁ _
  · rw [hτuθ, map_map_congrCME, hvc', hτS, map_map_congrCME, hvc']
  · unfold Coupled
    rw [hτuθ, hτθ, map_map_congrCME, map_map_congrCME, hτ₁]
    have hc1 : Continuous (fun t : T′ (u θ * δ) => y₁⁻¹ * (t : GL (Fin 2) Aℂ) * y₁) := by
      have h1 : Continuous (fun t : T′ (u θ * δ) => (t : GL (Fin 2) Aℂ)) := continuous_subtype_val
      exact (h1.const_mul y₁⁻¹).mul_const y₁
    have hc2 : Continuous (⇑(congrCME (hTθ θ hθ).symm) : T′ (u (Real.pi / 2) * δ) → T′ (u θ * δ)) := map_continuous _
    have hm1 : Measurable ((fun t : T′ (u θ * δ) => y₁⁻¹ * (t : GL (Fin 2) Aℂ) * y₁) ∘ ⇑(congrCME (hTθ θ hθ).symm)) :=
      (hc1.comp hc2).measurable
    rw [Measure.map_map hm1 (map_continuous e₁).measurable]
    congr 1
    funext s
    simp only [Function.comp_apply]
    rw [congrCME_coe, congrCME_coe, he₁]; group

end HA
p2m_reactivate "P2MW.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg.HAModel"

open MeasureTheory AutomorphicForm in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ (γ : ℝ → GL (Fin 2) ℝ) (θ₀ θ₁ : ℝ) (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (y₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
      (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (τ : ∀ θ : ℝ, @Measure (Subgroup.centralizer ({γ θ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ (γ θ)))
      (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ))
        (borel _))
      (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
        (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
      (∀ θ : ℝ, ((γ θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (c : ℝ) • !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]) ∧
      0 < θ₀ ∧ θ₁ ∈ Set.Ioo 0 θ₀ ∧
      (∀ θ : ℝ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ)) ∧
      (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
       Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) ∧
      (letI := glBorelOf ℝ
       Filter.Tendsto γ (nhdsWithin 0 (Set.Ioi 0)) (nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c))) ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τS ∧
      ∀ θ ∈ Set.Ioo 0 θ₀,
        IsRegularSemisimple (γ θ) ∧
        IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ)) ∧
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (γ θ) (u θ * δ) y₁ ∧
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (γ θ)) (τ θ) ∧
        @Measure.map _ _ (centralizerBorel ℝ (γ θ)) (glBorelOf ℝ) Subtype.val (τ θ) = νT ∧
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ) ∧
        (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
         letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
             twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ₁ * δ)) := borel _
         Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS) ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (γ θ) (u θ * δ) y₁ (τ θ) (τu θ) := HA.main c hc δ y hδ

end
end
end S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg
end P2MW
export P2MW.S_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg (solution)
