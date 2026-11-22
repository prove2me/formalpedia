-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:20.602787+00:00
-- url     : https://prove2.me/theorems/a83f8740-82db-465c-a2cb-469b26988d4b
-- title:
--   Orth Sum
-- statement:
--   Definitions and structural lemmas for Orth Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
namespace Formalism.BranchingDeterminantCap
namespace OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end OrthogonalSumAlt
namespace OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end OrthogonalSumAlt
end Formalism.BranchingDeterminantCap


