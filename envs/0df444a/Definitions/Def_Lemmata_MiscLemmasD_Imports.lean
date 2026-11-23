-- Prove2me | Definitions.Def_Lemmata_MiscLemmasD_Imports
-- name    : Lemmata_MiscLemmasD_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:10.330892+00:00
-- url     : https://prove2.me/theorems/f9ca042c-0aa6-47ea-80ca-0af8e42ffea1
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasD/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace Bl.SecondBlockLemmaE
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end Bl.SecondBlockLemmaE


