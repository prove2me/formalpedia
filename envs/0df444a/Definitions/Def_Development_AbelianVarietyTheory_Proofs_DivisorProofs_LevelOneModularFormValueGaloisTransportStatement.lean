-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LevelOneModularFormValueGaloisTransportStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LevelOneModularFormValueGaloisTransportStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:10.924613+00:00
-- url     : https://prove2.me/theorems/b3a0bdc2-8426-4937-a80a-36ec954bb132
-- title:
--   Level One Modular Form Value Galois Transport Statement
-- statement:
--   Definitions and structural lemmas for Level One Modular Form Value Galois Transport Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LevelOneModularFormValueGaloisTransportStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LevelOneModularFormValueGaloisTransport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)


