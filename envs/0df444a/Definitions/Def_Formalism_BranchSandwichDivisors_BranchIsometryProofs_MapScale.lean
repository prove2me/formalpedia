-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:31.028445+00:00
-- url     : https://prove2.me/theorems/b2dd4e1d-ed8b-4c53-9e2a-454f98cad74f
-- title:
--   Map Scale
-- statement:
--   Definitions and structural lemmas for Map Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/MapScale.lean

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.BranchingDeterminantCap
open Formalism.HN
section SlopeTestRemainingChoices
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
end SlopeTestRemainingChoices
end Formalism.BranchingDeterminantCap


