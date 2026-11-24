-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:54:15.525797+00:00
-- url     : https://prove2.me/theorems/6a66ebad-c906-49bd-8080-202599213bfa
-- title:
--   Rt Unitary Of
-- statement:
--   Definitions and structural lemmas for Rt Unitary Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct
namespace PI.UnitaryGroupMassFormula.InHHClassFin
abbrev rtA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F
abbrev rtι (I : Formalism.MainNotions.S.AutInst) : I.E →+* rtA I := inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)
theorem rt_conj_mul {k : Type} [Fintype k] [DecidableEq k] (P Pi A B : Matrix k k ℂ) (h1 : P * Pi = 1) :
    (Pi * A * P) * (Pi * B * P) = Pi * (A * B) * P := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Pi, h1, Matrix.one_mul]
def rtReal (I : Formalism.MainNotions.S.AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ UJ (starRingEnd I.E) I.J)
    (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    by
      have e1 : (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [rt_conj_mul _ _ _ _ (Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v), e1, Matrix.mul_one,
        Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul],
    by
      have e1 : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [rt_conj_mul _ _ _ _ (Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v), e1, Matrix.mul_one,
        Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul]⟩,
  by
    have hγ' : cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : (cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp only [cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply]
      exact I.cm.cmUnram.2.1 (I.φ v) _
    have hu : ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      rw [← hc, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.conjTranspose_one]
    show ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ *
        Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) =
        Formalism.REAL.Jm (I.ε v)
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)⁻¹)ᴴ (I.P v)ᴴ, hPP, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hu]⟩
end PI.UnitaryGroupMassFormula.InHHClassFin


