-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:25.194342+00:00
-- url     : https://prove2.me/theorems/4de3d1c5-9179-4509-8249-ff5f99501097
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DefPosDefWork
open Matrix ComplexOrder
def Step1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)
def Step2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)) →
    ∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef
end PI.DefPosDefWork


