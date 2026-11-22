-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_StrongApproxE
-- name    : Formalism_PeriodIntegrals_StrongApproxE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:31.319238+00:00
-- url     : https://prove2.me/theorems/e22db7da-73d7-44d6-9d42-77f79b9c48d4
-- title:
--   Strong Approx E
-- statement:
--   Definitions and structural lemmas for Strong Approx E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/StrongApproxE.lean

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
open IsDedekindDomain NumberField
namespace PI.StrongApproxE
def StrongApproxE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (U : ∀ p, AddSubgroup (L p).Ep), (∀ p, IsOpen (U p : Set (L p).Ep)) →
    {p | (U p : Set (L p).Ep) ≠ ((L p).O : Set (L p).Ep)}.Finite →
    ∀ x : ∀ p, (L p).Ep, {p | x p ∉ (L p).O}.Finite →
      ∃ t : E, ∀ p, (L p).ιE t - x p ∈ U p
end PI.StrongApproxE


