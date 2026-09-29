-- Prove2me | solution 1 for AutomorphicForm.map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f8692c82-da43-53aa-b7e9-3466b95eecf4

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarMeasure_HaarChar_AddEquiv
import Theorems.Thm_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField Matrix
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace P2mTwCommMod

section General

open AutomorphicForm

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))

abbrev MA : Type := Matrix (Fin 2) (Fin 2) (L ⊗[K] A)

abbrev sT : L ⊗[K] A →+* L ⊗[K] A := sigmaTensor K L A σ

def theta (X : MA K L A) : MA K L A :=
  (δ : MA K L A) * X.map (sT K L A σ) * ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A)

variable {K L A σ δ}

theorem coe_mul_coe_inv :
    (δ : MA K L A) * ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; rfl

theorem coe_inv_mul_coe :
    ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) * (δ : MA K L A) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; rfl

theorem map_mul_sT (X Y : MA K L A) :
    (X * Y).map (sT K L A σ) = X.map (sT K L A σ) * Y.map (sT K L A σ) :=
  Matrix.map_mul

theorem map_add_sT (X Y : MA K L A) :
    (X + Y).map (sT K L A σ) = X.map (sT K L A σ) + Y.map (sT K L A σ) :=
  Matrix.map_add _ (map_add (sT K L A σ)) X Y

theorem map_smul_sT (r : L ⊗[K] A) (X : MA K L A) :
    (r • X).map (sT K L A σ) = sT K L A σ r • X.map (sT K L A σ) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem map_one_sT : (1 : MA K L A).map (sT K L A σ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_iff_theta_eq (X : MA K L A) :
    X ∈ twistedCommutant K L A σ δ ↔ theta K L A σ δ X = X := by
  rw [mem_twistedCommutant_iff, theta]
  constructor
  · intro h
    rw [← h, mul_assoc, coe_mul_coe_inv, mul_one]
  · intro h
    have := congrArg (fun Y : MA K L A => Y * (δ : MA K L A)) h
    beta_reduce at this
    rw [← this, mul_assoc, coe_inv_mul_coe, mul_one]

theorem theta_add (X Y : MA K L A) :
    theta K L A σ δ (X + Y) = theta K L A σ δ X + theta K L A σ δ Y := by
  simp only [theta, map_add_sT, mul_add, add_mul]

theorem theta_zero : theta K L A σ δ 0 = 0 := by
  simp [theta, Matrix.map_zero _ (map_zero _)]

theorem theta_neg (X : MA K L A) : theta K L A σ δ (-X) = -theta K L A σ δ X := by
  have h : theta K L A σ δ (-X) + theta K L A σ δ X = 0 := by
    rw [← theta_add, neg_add_cancel, theta_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem theta_sub (X Y : MA K L A) :
    theta K L A σ δ (X - Y) = theta K L A σ δ X - theta K L A σ δ Y := by
  rw [sub_eq_add_neg, theta_add, theta_neg, ← sub_eq_add_neg]

theorem theta_mul (X Y : MA K L A) :
    theta K L A σ δ (X * Y) = theta K L A σ δ X * theta K L A σ δ Y := by
  simp only [theta, map_mul_sT, mul_assoc]
  rw [← mul_assoc ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) (δ : MA K L A), coe_inv_mul_coe, one_mul]

theorem theta_one : theta K L A σ δ 1 = 1 := by
  rw [theta, map_one_sT, mul_one, coe_mul_coe_inv]

theorem theta_smul (r : L ⊗[K] A) (X : MA K L A) :
    theta K L A σ δ (r • X) = sT K L A σ r • theta K L A σ δ X := by
  simp only [theta, map_smul_sT, Matrix.mul_smul, Matrix.smul_mul]

theorem theta_smul_one (r : L ⊗[K] A) :
    theta K L A σ δ (r • (1 : MA K L A)) = sT K L A σ r • (1 : MA K L A) := by
  rw [theta_smul, theta_one]

theorem smul_one_mem {r : L ⊗[K] A} (hr : sT K L A σ r = r) :
    r • (1 : MA K L A) ∈ twistedCommutant K L A σ δ := by
  rw [mem_iff_theta_eq, theta_smul_one, hr]

theorem sT_trace_of_mem {X : MA K L A} (hX : X ∈ twistedCommutant K L A σ δ) :
    sT K L A σ X.trace = X.trace := by
  rw [mem_iff_theta_eq] at hX
  have htr : (theta K L A σ δ X).trace = (X.map (sT K L A σ)).trace := by
    rw [theta, Matrix.trace_mul_cycle, coe_inv_mul_coe, one_mul]
  rw [hX] at htr
  have hmt : (X.map (sT K L A σ)).trace = sT K L A σ X.trace := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]; simp [Matrix.map_apply]
  rw [← hmt, ← htr]

def iota (X : MA K L A) : MA K L A := X.trace • (1 : MA K L A) - X

theorem iota_eq_adjugate (X : MA K L A) : iota X = X.adjugate := by
  rw [Matrix.adjugate_fin_two, iota, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem iota_add (X Y : MA K L A) : iota (X + Y) = iota X + iota Y := by
  simp only [iota, Matrix.trace_add, add_smul]; abel

theorem iota_iota (X : MA K L A) : iota (iota X) = X := by
  rw [iota_eq_adjugate, iota_eq_adjugate, Matrix.adjugate_adjugate _ (by simp), Fintype.card_fin]
  simp

theorem iota_mul (X Y : MA K L A) : iota (X * Y) = iota Y * iota X := by
  rw [iota_eq_adjugate, iota_eq_adjugate, iota_eq_adjugate, Matrix.adjugate_mul_distrib]

theorem iota_one : iota (1 : MA K L A) = 1 := by
  rw [iota_eq_adjugate, Matrix.adjugate_one]

theorem det_iota (X : MA K L A) : (iota X).det = X.det := by
  rw [iota_eq_adjugate, Matrix.det_adjugate, Fintype.card_fin]
  norm_num

theorem iota_mem {X : MA K L A} (hX : X ∈ twistedCommutant K L A σ δ) :
    iota X ∈ twistedCommutant K L A σ δ :=
  Subalgebra.sub_mem _ (smul_one_mem (sT_trace_of_mem hX)) hX

theorem theta_theta (hs2 : ∀ x : L ⊗[K] A, sT K L A σ (sT K L A σ x) = x)
    {n : L ⊗[K] A} (hN : ((δ * sigmaGL K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) = n • 1)
    (X : MA K L A) : theta K L A σ δ (theta K L A σ δ X) = X := by

  have hmap2 : (X.map (sT K L A σ)).map (sT K L A σ) = X := by
    ext i j; simp [Matrix.map_apply, hs2]
  have hσδ : ((sigmaGL K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) = (δ : MA K L A).map (sT K L A σ) :=
    coe_sigmaGL δ
  have hσδinv : ((sigmaGL K L A σ δ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) =
      sigmaGL K L A σ δ⁻¹ := (map_inv _ _).symm
  have hσδinv' : (((sigmaGL K L A σ δ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) =
      ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A).map (sT K L A σ) := by
    rw [hσδinv]; exact coe_sigmaGL δ⁻¹

  set N : GL (Fin 2) (L ⊗[K] A) := δ * sigmaGL K L A σ δ with hNdef
  have hNinv : ((N⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) =
      (((sigmaGL K L A σ δ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) *
        ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) := by
    rw [hNdef, _root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul]
  have key : theta K L A σ δ (theta K L A σ δ X) =
      (N : MA K L A) * X * ((N⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) := by
    rw [hNinv, hNdef, Matrix.GeneralLinearGroup.coe_mul, hσδ, hσδinv']
    simp only [theta, map_mul_sT, hmap2]
    simp only [mul_assoc]
  rw [key, hN]
  calc n • (1 : MA K L A) * X * ((N⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A)
        = X * (n • (1 : MA K L A)) * ((N⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) := by
          rw [Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one]
    _ = X * ((N : MA K L A) * ((N⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A)) := by rw [← hN, mul_assoc]
    _ = X := by rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; exact mul_one X

end General

section Descent

open AutomorphicForm

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))

abbrev RR : Type := ↥(twistedCommutant K L A σ δ)

scoped instance isTopologicalRing_MA : IsTopologicalRing (MA K L A) := by
  haveI := isTopologicalRing_tensor K L A
  infer_instance

scoped instance isTopologicalRing_RR : IsTopologicalRing (RR K L A σ δ) := by
  haveI := isTopologicalRing_tensor K L A
  exact inferInstanceAs (IsTopologicalRing (twistedCommutant K L A σ δ).toSubring)

scoped instance isTopologicalAddGroup_RR : IsTopologicalAddGroup (RR K L A σ δ) :=
  haveI := isTopologicalRing_RR K L A σ δ
  IsTopologicalRing.to_topologicalAddGroup

scoped instance isTopologicalAddGroup_RR_prod : IsTopologicalAddGroup (RR K L A σ δ × RR K L A σ δ) :=
  Prod.instIsTopologicalAddGroup

scoped instance continuousConstSMul_MA : ContinuousConstSMul (L ⊗[K] A) (MA K L A) := by
  haveI := isTopologicalRing_tensor K L A
  infer_instance

theorem continuous_iota : Continuous (iota : MA K L A → MA K L A) := by
  haveI := isTopologicalRing_tensor K L A
  have : (iota : MA K L A → MA K L A) = fun X => X.adjugate := funext iota_eq_adjugate
  rw [this]
  exact continuous_id.matrix_adjugate

theorem continuous_theta : Continuous (theta K L A σ δ) := by
  haveI := isTopologicalRing_tensor K L A
  exact (continuous_const.mul (continuous_id.matrix_map (continuous_sigmaTensor K L A σ))).mul
    continuous_const

structure DescentData where
  hs2 : ∀ x : L ⊗[K] A, sT K L A σ (sT K L A σ x) = x
  n : L ⊗[K] A
  hN : ((δ * sigmaGL K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : MA K L A) = n • 1
  lam : (L ⊗[K] A)ˣ
  hlam : sT K L A σ lam = -lam
  half : L ⊗[K] A
  hhalf : half * 2 = 1
  hshalf : sT K L A σ half = half

variable {K L A σ δ} (d : DescentData K L A σ δ)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem sT_lam_inv : sT K L A σ ((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = -((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) := by
  have h1 : sT K L A σ ((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (d.lam : L ⊗[K] A) = -1 := by
    have := congrArg (sT K L A σ) (d.lam.inv_mul)
    rw [map_mul, map_one, d.hlam, mul_neg] at this
    rw [← this, neg_neg]
  calc sT K L A σ ((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A)
        = sT K L A σ ((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (d.lam : L ⊗[K] A) *
            ((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [h1, neg_one_mul]

def proj1 (X : MA K L A) : RR K L A σ δ :=
  ⟨d.half • (X + theta K L A σ δ X), by
    rw [mem_iff_theta_eq, theta_smul, d.hshalf, theta_add, theta_theta d.hs2 d.hN, add_comm]⟩

def proj2 (X : MA K L A) : RR K L A σ δ :=
  ⟨(((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * d.half) • (X - theta K L A σ δ X), by
    rw [mem_iff_theta_eq, theta_smul, map_mul, d.hshalf, sT_lam_inv, theta_sub,
      theta_theta d.hs2 d.hN, neg_mul, neg_smul, ← smul_neg, neg_sub]⟩

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
@[scoped simp] theorem coe_proj1 (X : MA K L A) :
    ((proj1 d X : RR K L A σ δ) : MA K L A) = d.half • (X + theta K L A σ δ X) := rfl

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
@[scoped simp] theorem coe_proj2 (X : MA K L A) :
    ((proj2 d X : RR K L A σ δ) : MA K L A) =
      (((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * d.half) • (X - theta K L A σ δ X) := rfl

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem two_smul_eq_add (X : MA K L A) : (2 : L ⊗[K] A) • X = X + X := two_smul _ _

def phi : (RR K L A σ δ × RR K L A σ δ) ≃ₜ+ MA K L A where
  toFun p := (p.1 : MA K L A) + (d.lam : L ⊗[K] A) • (p.2 : MA K L A)
  invFun X := (proj1 d X, proj2 d X)
  left_inv p := by
    obtain ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := p
    have hY' := (mem_iff_theta_eq Y).1 hY
    have hZ' := (mem_iff_theta_eq Z).1 hZ
    have hθ : theta K L A σ δ (Y + (d.lam : L ⊗[K] A) • Z) = Y - (d.lam : L ⊗[K] A) • Z := by
      rw [theta_add, theta_smul, d.hlam, hY', hZ', neg_smul, sub_eq_add_neg]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [coe_proj1, hθ]
      rw [show Y + (d.lam : L ⊗[K] A) • Z + (Y - (d.lam : L ⊗[K] A) • Z) = (2 : L ⊗[K] A) • Y by
        rw [two_smul_eq_add]; abel, smul_smul, d.hhalf, one_smul]
    · simp only [coe_proj2, hθ]
      rw [show Y + (d.lam : L ⊗[K] A) • Z - (Y - (d.lam : L ⊗[K] A) • Z) =
          ((2 : L ⊗[K] A) * d.lam) • Z by rw [← smul_smul, two_smul_eq_add]; abel, smul_smul,
        show ((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * d.half * (2 * (d.lam : L ⊗[K] A)) =
          d.half * 2 * (((d.lam⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * d.lam) by ring,
        d.hhalf, Units.inv_mul, one_mul, one_smul]
  right_inv X := by
    simp only [coe_proj1, coe_proj2, smul_smul]
    rw [← mul_assoc, Units.mul_inv, one_mul, ← smul_add,
      show X + theta K L A σ δ X + (X - theta K L A σ δ X) = (2 : L ⊗[K] A) • X by
        rw [two_smul_eq_add]; abel, smul_smul, d.hhalf, one_smul]
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, smul_add]
    abel
  continuous_toFun := by
    exact ((continuous_subtype_val.comp continuous_fst).fun_add
      ((continuous_subtype_val.comp continuous_snd).fun_const_smul _))
  continuous_invFun := by
    have hθ := continuous_theta K L A σ δ
    refine Continuous.prodMk ?_ ?_
    · exact ((continuous_id.fun_add hθ).fun_const_smul _).subtype_mk _
    · exact ((continuous_id.fun_sub hθ).fun_const_smul _).subtype_mk _

theorem phi_apply (p : RR K L A σ δ × RR K L A σ δ) :
    phi d p = (p.1 : MA K L A) + (d.lam : L ⊗[K] A) • (p.2 : MA K L A) := rfl

variable (K L A σ δ)

def rhoM (g : GL (Fin 2) (L ⊗[K] A)) : MA K L A ≃ₜ+ MA K L A where
  toFun X := X * (g : MA K L A)
  invFun X := X * ((g⁻¹ : GL (Fin 2) (L ⊗[K] A)) : MA K L A)
  left_inv X := by
    simp only
    rw [mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; exact mul_one X
  right_inv X := by
    simp only
    rw [mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; exact mul_one X
  map_add' X Y := add_mul _ _ _
  continuous_toFun := continuous_id.mul continuous_const
  continuous_invFun := continuous_id.mul continuous_const

def rhoR (u : (RR K L A σ δ)ˣ) : RR K L A σ δ ≃ₜ+ RR K L A σ δ where
  toFun x := x * u
  invFun x := x * ((u⁻¹ : (RR K L A σ δ)ˣ) : RR K L A σ δ)
  left_inv x := by simp only; rw [mul_assoc, Units.mul_inv, mul_one]
  right_inv x := by simp only; rw [mul_assoc, Units.inv_mul, mul_one]
  map_add' x y := add_mul _ _ _
  continuous_toFun := continuous_id.mul continuous_const
  continuous_invFun := continuous_id.mul continuous_const

def lamR (u : (RR K L A σ δ)ˣ) : RR K L A σ δ ≃ₜ+ RR K L A σ δ where
  toFun x := u * x
  invFun x := ((u⁻¹ : (RR K L A σ δ)ˣ) : RR K L A σ δ) * x
  left_inv x := by simp only; rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by simp only; rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def unitM : (RR K L A σ δ)ˣ →* GL (Fin 2) (L ⊗[K] A) :=
  Units.map ((twistedCommutant K L A σ δ).val : RR K L A σ δ →* MA K L A)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
@[scoped simp] theorem coe_unitM (u : (RR K L A σ δ)ˣ) :
    ((unitM K L A σ δ u : GL (Fin 2) (L ⊗[K] A)) : MA K L A) = ((u : RR K L A σ δ) : MA K L A) := rfl

variable {K L A σ δ}

theorem phi_sumCongr_rhoR (u : (RR K L A σ δ)ˣ) (p : RR K L A σ δ × RR K L A σ δ) :
    phi d ((rhoR K L A σ δ u).sumCongr (rhoR K L A σ δ u) p) = rhoM K L A (unitM K L A σ δ u) (phi d p) := by
  show ((p.1 * u : RR K L A σ δ) : MA K L A) + (d.lam : L ⊗[K] A) • ((p.2 * u : RR K L A σ δ) : MA K L A) =
    ((p.1 : MA K L A) + (d.lam : L ⊗[K] A) • (p.2 : MA K L A)) * ((u : RR K L A σ δ) : MA K L A)
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, add_mul, Matrix.smul_mul]

def iotaR : RR K L A σ δ ≃ₜ+ RR K L A σ δ where
  toFun x := ⟨iota (x : MA K L A), iota_mem x.2⟩
  invFun x := ⟨iota (x : MA K L A), iota_mem x.2⟩
  left_inv x := Subtype.ext (iota_iota _)
  right_inv x := Subtype.ext (iota_iota _)
  map_add' x y := Subtype.ext (by simp only [Subalgebra.coe_add]; exact iota_add _ _)
  continuous_toFun := ((continuous_iota K L A).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_iota K L A).comp continuous_subtype_val).subtype_mk _

@[scoped simp] theorem coe_iotaR (x : RR K L A σ δ) : ((iotaR x : RR K L A σ δ) : MA K L A) = iota (x : MA K L A) := rfl

def iotaUnit (u : (RR K L A σ δ)ˣ) : (RR K L A σ δ)ˣ where
  val := iotaR (u : RR K L A σ δ)
  inv := iotaR ((u⁻¹ : (RR K L A σ δ)ˣ) : RR K L A σ δ)
  val_inv := Subtype.ext (by
    simp only [Subalgebra.coe_mul, coe_iotaR, Subalgebra.coe_one]
    rw [← iota_mul, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one, iota_one])
  inv_val := Subtype.ext (by
    simp only [Subalgebra.coe_mul, coe_iotaR, Subalgebra.coe_one]
    rw [← iota_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, iota_one])

theorem iotaR_lamR (u : (RR K L A σ δ)ˣ) (x : RR K L A σ δ) :
    iotaR (lamR K L A σ δ u x) = rhoR K L A σ δ (iotaUnit u) (iotaR x) := by
  refine Subtype.ext ?_
  show iota (((u : RR K L A σ δ) * x : RR K L A σ δ) : MA K L A) =
    ((iotaR x * iotaR (u : RR K L A σ δ) : RR K L A σ δ) : MA K L A)
  rw [Subalgebra.coe_mul, iota_mul, Subalgebra.coe_mul, coe_iotaR, coe_iotaR]

theorem det_unitM_iotaUnit (u : (RR K L A σ δ)ˣ) :
    Matrix.GeneralLinearGroup.det (unitM K L A σ δ (iotaUnit u)) =
      Matrix.GeneralLinearGroup.det (unitM K L A σ δ u) := by
  refine Units.ext ?_
  show (iota ((u : RR K L A σ δ) : MA K L A)).det = ((u : RR K L A σ δ) : MA K L A).det
  exact det_iota _

end Descent

section HaarChar

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem map_eq_inv_addEquivAddHaarChar_smul (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (φ : G ≃ₜ+ G) : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
  have h := addEquivAddHaarChar_smul_map μ φ
  have hpos : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
  calc μ.map φ = (addEquivAddHaarChar φ)⁻¹ • (addEquivAddHaarChar φ • μ.map φ) := by
        rw [smul_smul, inv_mul_cancel₀ hpos, one_smul]
    _ = _ := by rw [h]

theorem addEquivAddHaarChar_eq_of_map_eq_inv_smul (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (φ : G ≃ₜ+ G) {r : ℝ≥0} (hr : r ≠ 0) (h : μ.map φ = r⁻¹ • μ) :
    addEquivAddHaarChar φ = r := by
  have h1 := addEquivAddHaarChar_smul_map μ φ
  rw [h, smul_smul] at h1

  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : 0 < μ C := Measure.measure_pos_of_mem_nhds μ hC0
  have hlt : μ C < ⊤ := hC.measure_lt_top
  have h2 := congrArg (fun ν : Measure G => ν C) h1
  simp only [Measure.smul_apply] at h2
  rw [ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((addEquivAddHaarChar φ * r⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_left_inj hpos.ne' hlt.ne).1 (h2.trans (one_mul _).symm)
    exact this
  have h4 : addEquivAddHaarChar φ * r⁻¹ = 1 := by exact_mod_cast h3
  calc addEquivAddHaarChar φ = addEquivAddHaarChar φ * r⁻¹ * r := by
        rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
    _ = r := by rw [h4, one_mul]

end HaarChar

section Adelic

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

scoped instance secondCountableTopology_adeleRing (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology F

def rowMul (g : GL (Fin 2) AL) : (Fin 2 → AL) ≃ₜ+ (Fin 2 → AL) where
  toFun x := Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) AL)
  invFun x := Matrix.vecMul x ((g⁻¹ : GL (Fin 2) AL) : Matrix (Fin 2) (Fin 2) AL)
  left_inv x := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
    exact Matrix.vecMul_one x
  right_inv x := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]
    exact Matrix.vecMul_one x
  map_add' x y := Matrix.add_vecMul _ _ _
  continuous_toFun := by
    refine continuous_pi fun j => ?_
    simp only [Matrix.vecMul, dotProduct]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  continuous_invFun := by
    refine continuous_pi fun j => ?_
    simp only [Matrix.vecMul, dotProduct]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

theorem rowMul_apply (g : GL (Fin 2) AL) (x : Fin 2 → AL) :
    rowMul L g x = Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) AL) := rfl

theorem addEquivAddHaarChar_rowMul [MeasurableSpace AL] [BorelSpace AL] (g : GL (Fin 2) AL) :
    addEquivAddHaarChar (rowMul L g) =
      distribHaarChar AL (Matrix.GeneralLinearGroup.det g) := by
  set μ : Measure (Fin 2 → AL) := Measure.addHaar with hμ
  have h1 := (NumberField.AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
    L g).1 μ
  exact addEquivAddHaarChar_eq_of_map_eq_inv_smul μ (rowMul L g) (distribHaarChar_pos).ne' h1

abbrev MK : Type := MA K L (AdeleRing (𝓞 K) K)

scoped instance secondCountableTopology_tensor : SecondCountableTopology (L ⊗[K] AK) := by
  haveI := isTopologicalRing_tensor K L AK
  exact Module.Finite.secondCountabletopology AK (L ⊗[K] AK)

scoped instance secondCountableTopology_MK : SecondCountableTopology (MK K L) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → L ⊗[K] AK))

scoped instance locallyCompactSpace_MK : LocallyCompactSpace (MK K L) := by
  haveI := locallyCompactSpace_tensor K L AK
  exact inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → L ⊗[K] AK))

scoped instance t2Space_MK : T2Space (MK K L) := by
  haveI := t2Space_tensor K L AK
  exact inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] AK))

def psi : MK K L ≃ₜ+ (Fin 2 → Fin 2 → AL) where
  toFun X := fun i j => baseChangeEquiv K L (X i j)
  invFun Y := Matrix.of fun i j => (baseChangeEquiv K L).symm (Y i j)
  left_inv X := by ext i j; simp
  right_inv Y := by ext i j; simp
  map_add' X Y := by ext i j; simp
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_baseChangeEquiv K L).comp (continuous_id.matrix_elem i j)
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_baseChangeEquiv_symm K L).comp ((continuous_apply j).comp (continuous_apply i))

theorem psi_rhoM (g : GL (Fin 2) (L ⊗[K] AK)) (X : MK K L) :
    psi K L (rhoM K L AK g X) =
      ContinuousAddEquiv.piCongrRight (fun _ : Fin 2 => rowMul L (baseChangeGL K L g)) (psi K L X) := by
  funext i j
  show baseChangeEquiv K L ((X * (g : MK K L)) i j) =
    Matrix.vecMul (fun k => baseChangeEquiv K L (X i k))
      ((baseChangeGL K L g : GL (Fin 2) AL) : Matrix (Fin 2) (Fin 2) AL) j
  simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.vecMul, dotProduct]
  rfl

theorem addEquivAddHaarChar_rhoM [MeasurableSpace (MK K L)] [BorelSpace (MK K L)]
    (g : GL (Fin 2) (L ⊗[K] AK)) :
    addEquivAddHaarChar (rhoM K L AK g) =
      distribHaarChar AL (Matrix.GeneralLinearGroup.det (baseChangeGL K L g)) ^ 2 := by
  letI : MeasurableSpace AL := borel AL
  haveI : BorelSpace AL := ⟨rfl⟩
  rw [addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv (psi K L) (rhoM K L AK g)
    (ContinuousAddEquiv.piCongrRight (fun _ : Fin 2 => rowMul L (baseChangeGL K L g))) (psi_rhoM K L g),
    addEquivAddHaarChar_piCongrRight, Fin.prod_univ_two, addEquivAddHaarChar_rowMul, pow_two]

variable (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))

abbrev RK : Type := RR K L (AdeleRing (𝓞 K) K) σ δ

scoped instance secondCountableTopology_RK : SecondCountableTopology (RK K L σ δ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance locallyCompactSpace_RK : LocallyCompactSpace (RK K L σ δ) :=
  locallyCompactSpace_twistedCommutant K L AK σ δ

scoped instance t2Space_RK : T2Space (RK K L σ δ) := inferInstanceAs (T2Space {x // x ∈ twistedCommutant K L AK σ δ})

def modR (u : (RK K L σ δ)ˣ) : ℝ≥0 :=
  distribHaarChar AL (Matrix.GeneralLinearGroup.det (baseChangeGL K L (unitM K L AK σ δ u)))

variable {K L σ δ}

theorem addEquivAddHaarChar_rhoR [MeasurableSpace (RK K L σ δ)] [BorelSpace (RK K L σ δ)]
    (d : DescentData K L AK σ δ) (u : (RK K L σ δ)ˣ) :
    addEquivAddHaarChar (G := RK K L σ δ) (rhoR K L AK σ δ u) = modR K L σ δ u := by
  letI : MeasurableSpace (MK K L) := borel _
  haveI : BorelSpace (MK K L) := ⟨rfl⟩
  have hM := addEquivAddHaarChar_rhoM K L (unitM K L AK σ δ u)
  rw [← addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv (phi d)
    ((rhoR K L AK σ δ u).sumCongr (rhoR K L AK σ δ u)) (rhoM K L AK (unitM K L AK σ δ u))
    (phi_sumCongr_rhoR d u), addEquivAddHaarChar_prodCongr, ← pow_two] at hM
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 hM

theorem addEquivAddHaarChar_lamR [MeasurableSpace (RK K L σ δ)] [BorelSpace (RK K L σ δ)]
    (d : DescentData K L AK σ δ) (u : (RK K L σ δ)ˣ) :
    addEquivAddHaarChar (G := RK K L σ δ) (lamR K L AK σ δ u) = modR K L σ δ u := by
  rw [addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv iotaR (lamR K L AK σ δ u)
    (rhoR K L AK σ δ (iotaUnit u)) (iotaR_lamR u), addEquivAddHaarChar_rhoR d]
  simp only [modR, baseChangeGL, Matrix.GeneralLinearGroup.map_det, det_unitM_iotaUnit]

theorem map_mul_right_eq (mR : MeasurableSpace (RK K L σ δ)) [BorelSpace (RK K L σ δ)]
    (d : DescentData K L AK σ δ) (α : Measure (RK K L σ δ)) [α.IsAddHaarMeasure] (u : (RK K L σ δ)ˣ) :
    Measure.map (fun x : RK K L σ δ => x * u) α = (modR K L σ δ u)⁻¹ • α := by
  rw [← addEquivAddHaarChar_rhoR d u]
  exact map_eq_inv_addEquivAddHaarChar_smul α (rhoR K L AK σ δ u)

theorem map_mul_left_eq (mR : MeasurableSpace (RK K L σ δ)) [BorelSpace (RK K L σ δ)]
    (d : DescentData K L AK σ δ) (α : Measure (RK K L σ δ)) [α.IsAddHaarMeasure] (u : (RK K L σ δ)ˣ) :
    Measure.map (fun x : RK K L σ δ => (u : RK K L σ δ) * x) α = (modR K L σ δ u)⁻¹ • α := by
  rw [← addEquivAddHaarChar_lamR d u]
  exact map_eq_inv_addEquivAddHaarChar_smul α (lamR K L AK σ δ u)

end Adelic

section Main

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "AK" => AdeleRing (𝓞 K) K
local notation "AL" => AdeleRing (𝓞 L) L

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : GL (Fin 2) (L ⊗[K] AK) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AK) δ₀ *
    Matrix.GeneralLinearGroup.scalar (Fin 2) c

variable {K L}

omit [NumberField K] [NumberField L] in

theorem sigma_sigma (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (l : L) : σ (σ l) = l := by
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  have hσ : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have := congrArg (fun τ : L ≃ₐ[K] L => τ l) hσ
  simpa [pow_two, AlgEquiv.mul_apply] using this

omit [NumberField L] in
theorem sT_sT (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (x : L ⊗[K] AK) :
    sT K L AK σ (sT K L AK σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp [sT, sigmaTensor, Algebra.TensorProduct.map_tmul, sigma_sigma h2 σ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [NumberField K] [NumberField L] in

theorem exists_sigma_ne (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : ∃ l : L, σ l ≠ l := by
  by_contra h
  push Not at h
  have hσ1 : σ = 1 := AlgEquiv.ext h
  have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen τ)
    rw [← hk, hσ1, _root_.one_zpow]
  have hcard : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_eq_one_iff_exists.2 ⟨1, hall⟩
  have h2' : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  omega

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem sT_tmul (σ : L ≃ₐ[K] L) (l : L) (a : AK) : sT K L AK σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [sT, sigmaTensor, Algebra.TensorProduct.map_tmul]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in

theorem normString_two (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AK)) :
    normString K L AK σ δ = δ * sigmaGL K L AK σ δ := by
  rw [normString, h2]
  simp [List.range_succ]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem coe_toTensorGL_centralScalar (u : AKˣ) :
    ((toTensorGL K L AK (centralScalar (𝓞 K) K u) : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      ((1 : L) ⊗ₜ[K] (u : AK)) • (1 : MK K L) := by
  ext i j
  change (Algebra.TensorProduct.includeRight : AK →ₐ[K] L ⊗[K] AK)
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) AK) : Matrix (Fin 2) (Fin 2) AK) i j) = _
  rw [Matrix.smul_apply, Matrix.one_apply]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [Algebra.TensorProduct.includeRight_apply]

variable (K L) in

def descentData (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) (u : AKˣ)
    (hN : normString K L AK σ (δA K L δ₀ c) = toTensorGL K L AK (centralScalar (𝓞 K) K u)) :
    DescentData K L AK σ (δA K L δ₀ c) := by
  classical

  let l : L := Classical.choose (exists_sigma_ne h2 σ hgen)
  have hl : σ l ≠ l := Classical.choose_spec (exists_sigma_ne h2 σ hgen)
  let lam0 : L := l - σ l
  have hlam0 : lam0 ≠ 0 := fun h => hl (sub_eq_zero.1 h).symm
  have hσlam0 : σ lam0 = -lam0 := by
    simp only [lam0, map_sub, sigma_sigma h2 σ, neg_sub]
  refine
    { hs2 := sT_sT h2 σ
      n := (1 : L) ⊗ₜ[K] (u : AK)
      hN := ?_
      lam := Units.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AK).toMonoidHom
        (Units.mk0 lam0 hlam0)
      hlam := ?_
      half := algebraMap K (L ⊗[K] AK) 2⁻¹
      hhalf := ?_
      hshalf := sigmaTensor_algebraMap K L AK σ _ }
  · rw [← normString_two h2, hN, coe_toTensorGL_centralScalar]
  · show sT K L AK σ (lam0 ⊗ₜ[K] (1 : AK)) = -(lam0 ⊗ₜ[K] (1 : AK))
    rw [sT_tmul, hσlam0, TensorProduct.neg_tmul]
  · rw [show (2 : L ⊗[K] AK) = algebraMap K (L ⊗[K] AK) 2 from (map_ofNat _ 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero' K), map_one]

variable (K L) in

theorem main (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) (u : AKˣ)
    (hN : normString K L AK σ (δA K L δ₀ c) = toTensorGL K L AK (centralScalar (𝓞 K) K u))
    (mR : MeasurableSpace (RK K L σ (δA K L δ₀ c))) [BorelSpace (RK K L σ (δA K L δ₀ c))]
    (α : Measure (RK K L σ (δA K L δ₀ c))) [α.IsAddHaarMeasure]
    (t : twistedCentralizer K L AK σ (δA K L δ₀ c)) :
    Measure.map (fun x : RK K L σ (δA K L δ₀ c) =>
        ((twistedCentralizerEquivUnits (δA K L δ₀ c) t : (RK K L σ (δA K L δ₀ c))ˣ) :
          RK K L σ (δA K L δ₀ c)) * x) α =
      (distribHaarChar AL (Matrix.GeneralLinearGroup.det
        (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))))⁻¹ • α ∧
    Measure.map (fun x : RK K L σ (δA K L δ₀ c) =>
        x * ((twistedCentralizerEquivUnits (δA K L δ₀ c) t : (RK K L σ (δA K L δ₀ c))ˣ) :
          RK K L σ (δA K L δ₀ c))) α =
      (distribHaarChar AL (Matrix.GeneralLinearGroup.det
        (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))))⁻¹ • α := by
  set d := descentData K L h2 σ hgen δ₀ c u hN
  set uR : (RK K L σ (δA K L δ₀ c))ˣ := twistedCentralizerEquivUnits (δA K L δ₀ c) t with huR
  have hunit : unitM K L AK σ (δA K L δ₀ c) uR = (t : GL (Fin 2) (L ⊗[K] AK)) := Units.ext rfl
  have hmod : modR K L σ (δA K L δ₀ c) uR =
      distribHaarChar AL (Matrix.GeneralLinearGroup.det (baseChangeGL K L (t : GL (Fin 2) (L ⊗[K] AK)))) := by
    rw [modR, hunit]
  exact ⟨hmod ▸ map_mul_left_eq mR d α uR, hmod ▸ map_mul_right_eq mR d α uR⟩

end Main

end P2mTwCommMod
p2m_reactivate "P2MW.S_AutomorphicForm_map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.P2mTwCommMod"

end
p2m_reactivate "P2MW.S_AutomorphicForm_map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.P2mTwCommMod"

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    [MeasurableSpace (AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c))]
    [BorelSpace (AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c))]
    (α : Measure (AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    [α.IsAddHaarMeasure]
    (t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    Measure.map (fun x => ((AutomorphicForm.twistedCentralizerEquivUnits
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) t :
          (AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c))ˣ) :
          AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)) * x) α =
        (distribHaarChar (AdeleRing (𝓞 L) L)
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))))⁻¹ • α ∧
      Measure.map (fun x => x * ((AutomorphicForm.twistedCentralizerEquivUnits
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) t :
          (AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c))ˣ) :
          AutomorphicForm.twistedCommutant K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c))) α =
        (distribHaarChar (AdeleRing (𝓞 L) L)
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))))⁻¹ • α :=
  P2mTwCommMod.main K L h2 σ hgen δ₀ c u hN _ α t

end S_AutomorphicForm_map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_map_mul_addHaar_twistedCommutant_eq_inv_distribHaarChar_det_smul_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two (solution)
