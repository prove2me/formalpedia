-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.046018+00:00
-- url     : https://prove2.me/theorems/4d34e2c7-fea1-4d2a-a1b2-e03889b3baca
-- title:
--   Local Length Fraction
-- statement:
--   Definitions and structural lemmas for Local Length Fraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalLengthFraction.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
variable {K₁ : Type} [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁))
instance isFractionRing_Rv : IsFractionRing (Rv K₁ w) K₁ :=
  (inferInstance : IsFractionRing (w.valuationSubringAtPrime K₁) K₁)
variable {U : Type} [AddCommGroup U] [Module K₁ U] [FiniteDimensional K₁ U]
  [Module (Rv K₁ w) U] [IsScalarTower (Rv K₁ w) K₁ U]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction


