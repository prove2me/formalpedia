-- Prove2me | Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
-- name    : Lemmata_RankOneOrbitForms_RankOneForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:07.118981+00:00
-- url     : https://prove2.me/theorems/8d17f897-5ed6-4302-a6e4-67150e6e30c6
-- title:
--   Rank One Form
-- statement:
--   Definitions and structural lemmas for Rank One Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/RankOneOrbitForms/RankOneForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
namespace Bl.RankOneOrbitForms
variable {K : Type} [Field K] {G : Type} [Group G] {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
end Bl.RankOneOrbitForms


