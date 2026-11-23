-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
-- name    : Formalism_PeriodIntegrals_PinHostLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:11.779251+00:00
-- url     : https://prove2.me/theorems/e990e4f6-067d-4219-80df-55a935172848
-- title:
--   Pin Host Loc
-- statement:
--   Definitions and structural lemmas for Pin Host Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PinHostLoc.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open IsDedekindDomain NumberField ValuativeRel MeasureTheory
namespace PI.PinHostLoc
def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (g : Fin 2 → ℕ), (∀ i, (g i).Prime) → g 0 ≠ g 1 →
    ∀ i : Fin 2, ((g i : ℕ) : 𝓞 F) ∈ p.asIdeal → ((g i : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 →
      Irreducible ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : 𝒪[A.Fp]) ∧
        ∃ u : 𝒪[A.Fp], IsUnit u ∧
          (u : A.Fp) = A.ιF (((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F))
end PI.PinHostLoc


