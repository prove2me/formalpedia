-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:42.644826+00:00
-- url     : https://prove2.me/theorems/a71790e6-8d50-43d2-be9a-17a9a40b9f9b
-- title:
--   FFInert2 Holds
-- statement:
--   Definitions and structural lemmas for FFInert2 Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/FFInert2Holds.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
section basic
variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
end basic
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
def FFInert2 : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))
end PI.OmLocU.CntFF


