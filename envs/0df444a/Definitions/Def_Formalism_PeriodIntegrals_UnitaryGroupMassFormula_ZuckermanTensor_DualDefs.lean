-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:51.632815+00:00
-- url     : https://prove2.me/theorems/01b4c461-84bc-4010-a6f1-4187c2704a01
-- title:
--   Dual Defs
-- statement:
--   Definitions and structural lemmas for Dual Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
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
def Cj (H : Type) : Type := H
namespace Cj
variable {H : Type}
def mk (x : H) : Cj H := x
def un (x : Cj H) : H := x
instance [NormedAddCommGroup H] : NormedAddCommGroup (Cj H) := inferInstanceAs (NormedAddCommGroup H)
instance [NormedAddCommGroup H] [CompleteSpace H] : CompleteSpace (Cj H) := inferInstanceAs (CompleteSpace H)
instance [NormedAddCommGroup H] [Nontrivial H] : Nontrivial (Cj H) := inferInstanceAs (Nontrivial H)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
instance : Module ℂ (Cj H) := Module.compHom H (starRingEnd ℂ)
instance : NormedSpace ℂ (Cj H) where
  norm_smul_le c x := by
    show ‖(starRingEnd ℂ) c • un x‖ ≤ ‖c‖ * ‖un x‖
    rw [norm_smul, RCLike.norm_conj]
instance : InnerProductSpace ℂ (Cj H) where
  inner x y := ⟪un y, un x⟫_ℂ
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) (un x)
  conj_inner_symm x y := inner_conj_symm (un y) (un x)
  add_left x y z := inner_add_right (un z) (un x) (un y)
  smul_left x y r := by
    show ⟪un y, (starRingEnd ℂ) r • un x⟫_ℂ = (starRingEnd ℂ) r * ⟪un y, un x⟫_ℂ
    rw [inner_smul_right]
end Cj
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def cjOp (T : H →L[ℂ] H) : Cj H →L[ℂ] Cj H :=
  LinearMap.mkContinuous
    { toFun := fun x => Cj.mk (T (Cj.un x))
      map_add' := fun x y => by
        show T (Cj.un x + Cj.un y) = T (Cj.un x) + T (Cj.un y)
        exact map_add T _ _
      map_smul' := fun c x => by
        show T ((starRingEnd ℂ) c • Cj.un x) = (starRingEnd ℂ) c • T (Cj.un x)
        exact map_smul T _ _ }
    ‖T‖ (fun x => T.le_opNorm (Cj.un x))
variable {n : ℕ}
def revM (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := g.submatrix Fin.rev Fin.rev
def revE (ε : Fin n → Bool) : Fin n → Bool := fun a => ε (Fin.rev a)
def revP (lam : Fin n → ℝ) : Fin n → ℝ := fun a => - lam (Fin.rev a)
def sigC (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Matrix (Fin n) (Fin n) ℂ → (Cj H →L[ℂ] Cj H) :=
  fun g => cjOp (σ (revM g))
end PI.ZuckTensorWork
end


