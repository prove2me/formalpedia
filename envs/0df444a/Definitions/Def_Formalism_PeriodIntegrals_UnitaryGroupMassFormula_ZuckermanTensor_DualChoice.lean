-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:21.07423+00:00
-- url     : https://prove2.me/theorems/793a85d9-dafe-47a0-83a6-76915b47867d
-- title:
--   Dual Choice
-- statement:
--   Definitions and structural lemmas for Dual Choice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualChoice.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
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
section Sub
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def cjSub (S : Submodule ℂ H) : Submodule ℂ (Cj H) where
  carrier := {x | Cj.un x ∈ S}
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun c _ hx => S.smul_mem ((starRingEnd ℂ) c) hx
def cjSubInv (S : Submodule ℂ (Cj H)) : Submodule ℂ H where
  carrier := {x | Cj.mk x ∈ S}
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun c x hx => by
    have h : (starRingEnd ℂ) c • Cj.mk x ∈ S := S.smul_mem ((starRingEnd ℂ) c) hx
    have e : (starRingEnd ℂ) c • Cj.mk x = Cj.mk (c • x) := by
      show (starRingEnd ℂ) ((starRingEnd ℂ) c) • x = c • x
      rw [Complex.conj_conj]
    show Cj.mk (c • x) ∈ S
    rw [← e]
    exact h
end Sub
def HCRev : Prop := ∀ (n : ℕ) (lam : Fin n → ℝ), IsHCParam lam → IsHCParam (revP lam)
def GapRev : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), GapAtLeast ε lam h → GapAtLeast (revE ε) (revP lam) h
def LowKRev : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), lowK (revE ε) (revP lam) = revP (lowK ε lam)
def VNormRev : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Fin n → ℝ), vNormSq (revE ε) (revP ν) = vNormSq ε ν
def CDomRev : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ), CDom ε μ Λ → CDom (revE ε) (revP μ) (revP Λ)
def URepConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsURepOn (UJset (revE ε)) (sigC σ)
def IrredConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrredOn (UJset ε) σ → IsIrredOn (UJset (revE ε)) (sigC σ)
def SqIntConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntOn ε σ → IsSqIntOn (revE ε) (sigC σ)
def KTypeConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H),
    IsKTypeOf ε σ Λ S → IsKTypeOf (revE ε) (sigC σ) (revP Λ) (cjSub S)
def KTypeConjInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ (Cj H)),
    IsKTypeOf (revE ε) (sigC σ) Λ S → IsKTypeOf ε σ (revP Λ) (cjSubInv S)
def KFinConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), IsKFin ε σ v ↔ IsKFin (revE ε) (sigC σ) (Cj.mk v)
def DSConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsDS ε lam σ → IsDS (revE ε) (revP lam) (sigC σ)
end PI.ZuckTensorWork
end


