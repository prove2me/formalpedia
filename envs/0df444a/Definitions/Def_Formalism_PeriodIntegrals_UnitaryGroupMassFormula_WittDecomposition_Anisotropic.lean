-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:54.542975+00:00
-- url     : https://prove2.me/theorems/fe5c96f7-8237-4591-babc-0c774d3ca8db
-- title:
--   Anisotropic
-- statement:
--   Definitions and structural lemmas for Anisotropic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/Anisotropic.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Witt
def OneVector : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ x y : V, B x x = B y y → B x x ≠ 0 →
      ∃ g : V ≃ₗ[K] V, (∀ z w, B (g z) (g w) = B z w) ∧ g x = y ∧
        ∀ z, B x z = 0 → B y z = 0 → g z = z
def Anisotropic : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ U : Submodule K V, (∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0) → ∃ x ∈ U, B x x ≠ 0
end PI.Witt


