-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
-- name    : Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:17:42.70613+00:00
-- url     : https://prove2.me/theorems/f3ba7a7c-d9b0-439f-9f0c-7a4cd25a4162
-- title:
--   Reduction Quotient
-- statement:
--   Definitions and structural lemmas for Reduction Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ReductionQuotient.lean

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module
namespace BasisReduction
open Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
abbrev q (A B : Submodule O X) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)
end BasisReduction
open BasisReduction
end Formalism.LatticeBaseChangeAlt


