-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:57.252484+00:00
-- url     : https://prove2.me/theorems/3e4117ea-663e-5148-a42f-c010cffedbdd
-- title:
--   Hua Inv Of Tau Deriv
-- statement:
--   Definitions and structural lemmas for Hua Inv Of Tau Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcInf
open HcS.BasicNotions Matrix
section MatDet
variable {n : Type} [Fintype n] [DecidableEq n]
end MatDet
section Real
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
def sigJ (W : Mat) : Mat := HcS.UG.Jpq P Q * Wᴴ * HcS.UG.Jpq P Q
theorem Jpq_mul_mul (X : Mat) : HcS.UG.Jpq P Q * (HcS.UG.Jpq P Q * X) = X := by
  rw [← Matrix.mul_assoc]
  simp [HcS.UG.Jpq, Matrix.fromBlocks_multiply]
theorem sigJ_add (V W : Mat) : sigJ (V + W) = sigJ V + sigJ W := by
  simp only [sigJ, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
theorem sigJ_smul (c : ℂ) (W : Mat) : sigJ (c • W) = star c • sigJ W := by
  simp only [sigJ, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
theorem sigJ_sigJ (W : Mat) : sigJ (sigJ W) = W := by
  have hJ : (HcS.UG.Jpq P Q)ᴴ = HcS.UG.Jpq P Q := by
    simp [HcS.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have hJJ : HcS.UG.Jpq P Q * HcS.UG.Jpq P Q = 1 := by
    simpa using Jpq_mul_mul (P := P) (Q := Q) 1
  simp only [sigJ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
    Matrix.mul_assoc, Jpq_mul_mul, hJJ, Matrix.mul_one]
theorem mem_lieU_iff_sigJ (X : Mat) : X ∈ lieU P Q ↔ sigJ X = -X := by
  show Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0 ↔ HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q = -X
  constructor
  · intro h
    have h' : Xᴴ * HcS.UG.Jpq P Q = -(HcS.UG.Jpq P Q * X) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.mul_assoc, h', Matrix.mul_neg, Jpq_mul_mul]
  · intro h
    have e1 : HcS.UG.Jpq P Q * (Xᴴ * HcS.UG.Jpq P Q) = -X := by
      rw [← Matrix.mul_assoc]
      exact h
    calc Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X
        = HcS.UG.Jpq P Q * (HcS.UG.Jpq P Q * (Xᴴ * HcS.UG.Jpq P Q)) + HcS.UG.Jpq P Q * X := by
          rw [Jpq_mul_mul]
      _ = 0 := by rw [e1, Matrix.mul_neg, neg_add_cancel]
def cplx : (lieU P Q × lieU P Q) →ₗ[ℝ] Mat where
  toFun p := ((p.1 : lieU P Q) : Mat) + Complex.I • ((p.2 : lieU P Q) : Mat)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm c Complex.I]
theorem cplx_apply (p : lieU P Q × lieU P Q) :
    cplx p = ((p.1 : lieU P Q) : Mat) + Complex.I • ((p.2 : lieU P Q) : Mat) := rfl
theorem cplx_injective : Function.Injective (cplx (P := P) (Q := Q)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ h
  have h1 : Y + Complex.I • Z = 0 := h
  have hY' : sigJ Y = -Y := (mem_lieU_iff_sigJ Y).1 hY
  have hZ' : sigJ Z = -Z := (mem_lieU_iff_sigJ Z).1 hZ
  have hs : star Complex.I = -Complex.I := by simp [Complex.star_def]
  have h2 : -Y + Complex.I • Z = 0 := by
    have h3 : sigJ (Y + Complex.I • Z) = 0 := by
      rw [h1]; simp [sigJ]
    rw [sigJ_add, sigJ_smul, hY', hZ', hs, neg_smul_neg] at h3
    exact h3
  have hY0 : Y = 0 := by
    have h4 : (2 : ℂ) • Y = 0 := by
      rw [two_smul]
      calc Y + Y = (Y + Complex.I • Z) - (-Y + Complex.I • Z) := by abel
        _ = 0 := by rw [h1, h2, sub_zero]
    exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
  have hZ0 : Z = 0 := by
    rw [hY0, zero_add] at h1
    exact (smul_eq_zero.1 h1).resolve_left Complex.I_ne_zero
  subst hY0
  subst hZ0
  rfl
theorem cplx_surjective : Function.Surjective (cplx (P := P) (Q := Q)) := by
  intro W
  have hsub : ∀ V U : Mat, sigJ (V - U) = sigJ V - sigJ U := by
    intro V U
    simp only [sigJ, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hh : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  have hi : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.star_def]
  have hI2 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  have hY : ((1 : ℂ) / 2) • (W - sigJ W) ∈ lieU P Q := by
    rw [mem_lieU_iff_sigJ, sigJ_smul, hsub, sigJ_sigJ, hh, ← smul_neg, neg_sub]
  have hZ : (-Complex.I / 2) • (W + sigJ W) ∈ lieU P Q := by
    rw [mem_lieU_iff_sigJ, sigJ_smul, sigJ_add, sigJ_sigJ, hi, ← neg_smul, add_comm (sigJ W)]
    congr 1
    ring
  refine ⟨(⟨_, hY⟩, ⟨_, hZ⟩), ?_⟩
  rw [cplx_apply]
  show ((1 : ℂ) / 2) • (W - sigJ W) + Complex.I • ((-Complex.I / 2) • (W + sigJ W)) = W
  rw [smul_smul, hI2, ← smul_add,
    show W - sigJ W + (W + sigJ W) = (2 : ℂ) • W by rw [two_smul]; abel, smul_smul]
  norm_num
def cplxE : (lieU P Q × lieU P Q) ≃ₗ[ℝ] Mat :=
  LinearEquiv.ofBijective cplx ⟨cplx_injective, cplx_surjective⟩
end Real
end HcInf


