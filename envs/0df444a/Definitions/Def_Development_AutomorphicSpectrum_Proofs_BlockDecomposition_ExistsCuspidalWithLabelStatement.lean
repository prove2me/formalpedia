-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabelStatement
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabelStatement
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:13:58.103234+00:00
-- url     : https://prove2.me/theorems/84992c39-4ec8-459b-81fd-7ddb029ac0e8
-- title:
--   Exists Cuspidal With Label Statement
-- statement:
--   Definitions and structural lemmas for Exists Cuspidal With Label Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabelStatement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory


