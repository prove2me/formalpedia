-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
-- name    : CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:19.212177+00:00
-- url     : https://prove2.me/theorems/8cc404b2-2b30-4bc5-b11f-0703a8cff63e
-- title:
--   Schur H
-- statement:
--   Definitions and structural lemmas for Schur H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply


set_option autoImplicit false
noncomputable section
namespace CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
theorem inv_mul_P (hP : IsCayley k r ε P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1)
theorem P_mul_inv (hP : IsCayley k r ε P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1)
theorem back_forth (hP : IsCayley k r ε P) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P⁻¹ * (P * x * P⁻¹) * P = x := by
  calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [inv_mul_P hP, Matrix.one_mul, Matrix.mul_one]
theorem forth_back (hP : IsCayley k r ε P) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P * (P⁻¹ * x * P) * P⁻¹ = x := by
  calc P * (P⁻¹ * x * P) * P⁻¹ = (P * P⁻¹) * x * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [P_mul_inv hP, Matrix.one_mul, Matrix.mul_one]
theorem back_mul (hP : IsCayley k r ε P) (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [P_mul_inv hP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem back_mem (hP : IsCayley k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, P_mul_inv hP, Matrix.conjTranspose_one]
  show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
  rw [← hP.2]
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * g) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [h1, P_mul_inv hP, Matrix.mul_one, Matrix.mul_one, hg']
def iota (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (g : UJ ε) : Formalism.QuantumDeterminants.Mt k r :=
  P⁻¹ * umat g * P
theorem umat_mem (g : UJ ε) : umat g ∈ UJset ε := g.2
theorem iota_mem (hP : IsCayley k r ε P) (g : UJ ε) : Matrix.of (iota P g) ∈ UH (Hpk k r) :=
  back_mem hP (umat_mem g)
theorem iota_mul (hP : IsCayley k r ε P) (g h : UJ ε) :
    Matrix.of (iota P (g * h)) = Matrix.of (iota P g) * Matrix.of (iota P h) :=
  back_mul hP (umat g) (umat h)
theorem iota_one (hP : IsCayley k r ε P) : Matrix.of (iota P (1 : UJ ε)) = 1 := by
  show P⁻¹ * 1 * P = 1
  rw [Matrix.mul_one, inv_mul_P hP]
theorem iota_closedEmb (hP : IsCayley k r ε P) : IsClosedEmbedding (iota (ε := ε) P) := by
  let φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ≃ₜ
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    { toFun := fun x => P⁻¹ * x * P
      invFun := fun x => P * x * P⁻¹
      left_inv := forth_back hP
      right_inv := back_forth hP
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact φ.isClosedEmbedding.comp (isClosedEmbeddingMatrix _ ε).1
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def toURep (hP : IsCayley k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UH (Hpk k r)) σ) : UnitaryRep (UJ ε) H :=
  have hmul : ∀ g h : UJ ε, σ (Matrix.of (iota P (g * h))) =
      (σ (Matrix.of (iota P g))).comp (σ (Matrix.of (iota P h))) := fun g h => by
    rw [iota_mul hP, hσ.1.2 _ (iota_mem hP g) _ (iota_mem hP h)]
  have hone : σ (Matrix.of (iota P (1 : UJ ε))) = 1 := by rw [iota_one hP, hσ.1.1]
  UnitaryRep.ofLinearIsometryEquiv
    { toFun := fun g => LinearIsometryEquiv.ofSurjective
        ⟨(σ (Matrix.of (iota P g)) : H →ₗ[ℂ] H), hσ.2.1 _ (iota_mem hP g)⟩
        (fun v => ⟨σ (Matrix.of (iota P g⁻¹)) v, by
          have := congrArg (fun T : H →L[ℂ] H => T v) (hmul g g⁻¹)
          simp only [mul_inv_cancel, hone] at this
          exact this.symm⟩)
      map_one' := by
        ext v
        exact congrArg (fun T : H →L[ℂ] H => T v) hone
      map_mul' := fun g h => by
        ext v
        exact congrArg (fun T : H →L[ℂ] H => T v) (hmul g h) }
    (fun v => (hσ.2.2 v).comp_continuous (f := fun g : UJ ε => Matrix.of (iota P g))
      (iota_closedEmb hP).continuous (iota_mem hP))
end Rep
end CompanionTheory.LimBd.SchurHpk


