-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_JRMapTheta
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_JRMapTheta
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:52.862584+00:00
-- url     : https://prove2.me/theorems/cee9bfe1-51fc-4441-b1cf-5dccefc5ce84
-- title:
--   JRMap Theta
-- statement:
--   Definitions and structural lemmas for JRMap Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/JRMapTheta.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_MapThetaEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_BridgeHomFormula
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_SG_AdBridge_tauF_inclR
import Theorems.Thm_Formalism_L2_SG_AdBridge_tauF_tmul
import Theorems.Thm_Formalism_L2_SG_AdBridge_thetaV_inclR
import Theorems.Thm_Formalism_L2_SG_AdBridge_thetaV_sigR
import Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeInvAlg_matEq_of_inj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
def pre (hs : ThetaSurj) (I : AutInst) (z : (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E := (hs I z).choose
theorem theta_pre (hs : ThetaSurj) (I : AutInst)
    (z : (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Theta I (pre hs I z) = z :=
  (hs I z).choose_spec
def coZ (I : AutInst) (y : I.GA) (i j : Fin I.n) :
    (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  (fun v => (I.P v * uMat (y.1 v) * (I.P v)⁻¹) i j, I.fmat y.2 i j)
def coM (hs : ThetaSurj) (I : AutInst) (y : I.GA) :
    Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  Matrix.of fun i j => pre hs I (coZ I y i j)
theorem coM_theta (hs : ThetaSurj) (I : AutInst) (y : I.GA) (v : InfinitePlace I.F) :
    (coM hs I y).map (thetaV I v) = I.P v * uMat (y.1 v) * (I.P v)⁻¹ := by
  ext i j
  exact congrArg (fun z => z.1 v) (theta_pre hs I (coZ I y i j))
theorem coM_tau (hs : ThetaSurj) (I : AutInst) (y : I.GA) :
    (coM hs I y).map (tauF I) = I.fmat y.2 := by
  ext i j
  exact congrArg (fun z => z.2) (theta_pre hs I (coZ I y i j))
theorem coM_mul (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) (y z : I.GA) :
    coM hs I (y * z) = coM hs I y * coM hs I z := by
  apply matEq_of_inj hi I
  · intro v
    rw [Matrix.map_mul, coM_theta, coM_theta, coM_theta]
    have : uMat ((y * z).1 v) = uMat (y.1 v) * uMat (z.1 v) := rfl
    rw [this]
    calc I.P v * (uMat (y.1 v) * uMat (z.1 v)) * (I.P v)⁻¹
        = I.P v * uMat (y.1 v) * 1 * uMat (z.1 v) * (I.P v)⁻¹ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = I.P v * uMat (y.1 v) * (I.P v)⁻¹ * (I.P v * uMat (z.1 v) * (I.P v)⁻¹) := by
          rw [← P_inv_mul I v]; simp only [Matrix.mul_assoc]
  · rw [Matrix.map_mul, coM_tau, coM_tau, coM_tau]
    rfl
theorem coM_one (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) : coM hs I 1 = 1 := by
  apply matEq_of_inj hi I
  · intro v
    rw [coM_theta, Matrix.map_one _ (map_zero _) (map_one _)]
    have : uMat ((1 : I.GA).1 v) = 1 := rfl
    rw [this, Matrix.mul_one, P_mul_inv]
  · rw [coM_tau, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
theorem cT_map_theta (I : AutInst) (v : InfinitePlace I.F)
    (M : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (thetaV I v) =
      (M.map (thetaV I v))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, thetaV_sigR]
theorem JR_map_theta (I : AutInst) (v : InfinitePlace I.F) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (thetaV I v) = I.J.map (I.φ v) := by
  ext i j
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, thetaV_inclR]
theorem tauF_sigR (I : AutInst) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (tauF I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, tauF_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
theorem cT_map_tau (I : AutInst)
    (M : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (tauF I) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (M.map (tauF I)) := by
  ext i j
  simp [Formalism.UG.cT, tauF_sigR]
theorem JR_map_tau (I : AutInst) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (tauF I) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, tauF_inclR]
theorem conj_unitary (I : AutInst) (v : InfinitePlace I.F) (X : Matrix (Fin I.n) (Fin I.n) ℂ)
    (hX : Xᴴ * Formalism.REAL.Jm (I.ε v) * X = Formalism.REAL.Jm (I.ε v)) :
    (I.P v * X * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * X * (I.P v)⁻¹) = I.J.map (I.φ v) := by
  set P := I.P v
  set Q := (I.P v)⁻¹
  set Jv := I.J.map (I.φ v)
  have hS : Pᴴ * Jv * P = Formalism.REAL.Jm (I.ε v) := I.P_spec v
  have hPQ : P * Q = 1 := P_mul_inv I v
  have hJ : Jv = Qᴴ * Formalism.REAL.Jm (I.ε v) * Q := by
    rw [← hS]
    calc Jv = (P * Q)ᴴ * Jv * (P * Q) := by
          rw [hPQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * (Pᴴ * Jv * P) * Q := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  calc (P * X * Q)ᴴ * Jv * (P * X * Q)
      = Qᴴ * (Xᴴ * (Pᴴ * Jv * P) * X) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jv := by rw [hS, hX, ← hJ]
theorem coM_mem (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) (y : I.GA) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) (coM hs I y) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * coM hs I y =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J := by
  apply matEq_of_inj hi I
  · intro v
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_theta, JR_map_theta, coM_theta]
    exact conj_unitary I v _ (y.1 v).2
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_tau, JR_map_tau, coM_tau]
    exact y.2.2
def preHA (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) (y : I.GA) : HAd I :=
  let u : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
    ⟨coM hs I y, coM hs I y⁻¹,
      by rw [← coM_mul hi, mul_inv_cancel, coM_one hi],
      by rw [← coM_mul hi, inv_mul_cancel, coM_one hi]⟩
  let h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := ⟨u, coM_mem hi hs I y⟩
  h'
end PI.UnitaryGroupMassFormula.BridgeInvAlg


