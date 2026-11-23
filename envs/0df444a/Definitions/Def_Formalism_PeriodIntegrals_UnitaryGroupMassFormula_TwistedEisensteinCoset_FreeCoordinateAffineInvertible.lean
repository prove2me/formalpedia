-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:43.758471+00:00
-- url     : https://prove2.me/theorems/4241550c-0d71-423e-9424-7d1972186744
-- title:
--   Free Coordinate Affine Invertible
-- statement:
--   Definitions and structural lemmas for Free Coordinate Affine Invertible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section XX
variable {E : Type} [Field E]
def xxwLin {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : (FC n' c' n c → E) →ₗ[E] (FC n' c' n c → E) where
  toFun t f := ρ (fun l => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) f.1.1
  map_add' t t' := by
    funext f
    have hv : (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then (t + t') ⟨(l, f.1.2), hf⟩ else 0) =
        (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) +
        (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t' ⟨(l, f.1.2), hf⟩ else 0) := by
      funext l
      simp only [Pi.add_apply]
      split_ifs <;> simp
    show ρ _ f.1.1 = ρ _ f.1.1 + ρ _ f.1.1
    rw [hv, map_add]
    rfl
  map_smul' a t := by
    funext f
    have hv : (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then (a • t) ⟨(l, f.1.2), hf⟩ else 0) =
        a • (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) := by
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    show ρ _ f.1.1 = a * ρ _ f.1.1
    rw [hv, map_smul]
    rfl
end XX
end PI.TwistedEisensteinNonvanishing.W


