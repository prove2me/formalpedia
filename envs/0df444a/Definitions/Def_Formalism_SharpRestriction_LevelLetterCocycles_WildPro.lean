-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_WildPro
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:34.113802+00:00
-- url     : https://prove2.me/theorems/5ce2f7d0-0938-4045-8b5f-5924658470ed
-- title:
--   Wild Pro
-- statement:
--   Definitions and structural lemmas for Wild Pro, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/WildPro.lean

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.N.KillingConditions
def WildProP (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Prop :=
  ∀ (A : ValuationSubring Ω) (p : ℕ), p.Prime → A.valuation ((p : ℕ) : Ω) < 1 →
    ∀ σ : Ω ≃ₐ[E] Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) →
    ∀ N : Subgroup (Ω ≃ₐ[E] Ω), IsOpen (N : Set (Ω ≃ₐ[E] Ω)) → ∃ k : ℕ, σ ^ (p ^ k) ∈ N
end Formalism.MainNotions.N.KillingConditions
namespace Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
def IsWild (σ : Ω ≃ₐ[E] Ω) : Prop := ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1
variable {A}
end Formalism.MainNotions.N.KillingConditions.WildPf
end


