-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:39.988269+00:00
-- url     : https://prove2.me/theorems/5ca8db6a-1cf2-441d-a7be-3f2fc4407182
-- title:
--   Local Quotient Rank
-- statement:
--   Definitions and structural lemmas for Local Quotient Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalQuotientRank.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
open NumberField Module
open scoped TensorProduct
section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
end
section
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]
end
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank


