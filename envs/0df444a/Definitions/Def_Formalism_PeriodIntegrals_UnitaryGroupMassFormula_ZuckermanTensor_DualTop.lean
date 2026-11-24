-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualTop
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T23:15:27.486136+00:00
-- url     : https://prove2.me/theorems/29162b7a-905e-4b50-8423-8410a56dbadc
-- title:
--   Dual Top
-- statement:
--   Definitions and structural lemmas for Dual Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualTop.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
def RevUJ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), g ∈ UJset (revE ε) → revM g ∈ UJset ε
def DualVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), g ∈ UJset ε → ∀ x y : Fin n → ℂ,
    (starRingEnd ℂ) (star y ⬝ᵥ (revM g *ᵥ x)) =
      star (Jm ε *ᵥ (x ∘ Fin.rev)) ⬝ᵥ (g⁻¹ *ᵥ (Jm ε *ᵥ (y ∘ Fin.rev)))
def JJ : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (x : Fin n → ℂ), Jm ε *ᵥ (Jm ε *ᵥ x) = x
def RevSingle : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (s : Fin n), revP (lam + Pi.single s 1) = revP lam - Pi.single (Fin.rev s) 1
section Eq
variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
def cjEquivInv (U : Cj A ≃ₗᵢ[ℂ] Cj B) : A ≃ₗᵢ[ℂ] B where
  toFun x := Cj.un (U (Cj.mk x))
  invFun y := Cj.un (U.symm (Cj.mk y))
  left_inv x := by
    show Cj.un (U.symm (U (Cj.mk x))) = x
    rw [U.symm_apply_apply]; rfl
  right_inv y := by
    show Cj.un (U (U.symm (Cj.mk y))) = y
    rw [U.apply_symm_apply]; rfl
  map_add' x y := by
    show Cj.un (U (Cj.mk x + Cj.mk y)) = _
    rw [map_add]; rfl
  map_smul' c x := by
    have e : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
      show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
      rw [Complex.conj_conj]
    show Cj.un (U (Cj.mk (c • x))) = c • Cj.un (U (Cj.mk x))
    rw [e, map_smul, Cj.un_smul, Complex.conj_conj]
  norm_map' x := U.norm_map (Cj.mk x)
end Eq
end PI.ZuckTensorWork
end


