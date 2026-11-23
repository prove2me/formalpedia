-- Prove2me | Definitions.Def_SimpleRbrFri
-- name    : SimpleRbrFri
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T09:44:48.401986+00:00
-- url     : https://prove2.me/theorems/45b24ef0-9f32-476d-8b8a-9b96be5b303f
-- title:
--   Simple Rbr Fri
-- statement:
--   Definitions and structural lemmas for Simple Rbr Fri, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri.lean

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
set_option linter.mathlibStandardSet false


