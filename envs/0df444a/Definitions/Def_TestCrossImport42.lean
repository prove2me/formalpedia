-- Prove2me | Definitions.Def_TestCrossImport42
-- name    : TestCrossImport42
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T18:11:26.085716+00:00
-- url     : https://prove2.me/theorems/99fe7487-3f38-44b5-a62d-d1d2c96843b5
-- title:
--   Cross-import test
-- statement:
--   Test: a definition importing an already-published Definition module.
-- source:
--   test

import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent

/-- Test: cross-import of a published Definition module. -/
noncomputable def TestCrossImport42 : ℕ := 42


