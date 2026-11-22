-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsGal
-- name    : Formalism_LocalToGlobal_GaloisLevelStructure_DefsGal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:12.555253+00:00
-- url     : https://prove2.me/theorems/477d8436-2f11-4917-a132-8136baba479d
-- title:
--   Defs Gal
-- statement:
--   Definitions and structural lemmas for Defs Gal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsGal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.NG
instance isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
end Formalism.L2.NG


