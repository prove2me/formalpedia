-- Prove2me | Definitions.Def_Csg_SkirmishProperties
-- name    : Csg_SkirmishProperties
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:54:31.672455+00:00
-- url     : https://prove2.me/theorems/b79de4b8-a4c5-4980-9998-982aab57c05e
-- title:
--   Skirmish Properties
-- statement:
--   Definitions and structural lemmas for Skirmish Properties, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
set_option autoImplicit true
namespace Csg
abbrev skirmishSafe : Set SkirmishPos := {s | s ≠ .wet}
end Csg


