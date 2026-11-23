-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExtNRowsGen
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_ExtNRowsGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:39.506647+00:00
-- url     : https://prove2.me/theorems/1725be54-a22b-4dc0-a7db-b9acfba0790f
-- title:
--   Ext NRows Gen
-- statement:
--   Definitions and structural lemmas for Ext NRows Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
namespace Formalism.L2.N.ExtNRows
section Generic
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
end Generic
end Formalism.L2.N.ExtNRows
end


