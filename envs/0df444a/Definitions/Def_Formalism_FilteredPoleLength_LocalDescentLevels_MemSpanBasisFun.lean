-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
-- name    : Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:35.007465+00:00
-- url     : https://prove2.me/theorems/c7058b29-83ef-4c55-8b81-489eb9bc4162
-- title:
--   Mem Span Basis Fun
-- statement:
--   Definitions and structural lemmas for Mem Span Basis Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
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
namespace BQuot
section General
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
abbrev ql (A B : Submodule O V) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)
end General
section DVR
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
end DVR
end BQuot
end Formalism.LatticeBaseChangeAlt


