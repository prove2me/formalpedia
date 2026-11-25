-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochainStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochainStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:39:45.2289+00:00
-- url     : https://prove2.me/theorems/be6260ad-204c-4d83-b740-74d60c98c0c3
-- title:
--   Is Cech One Cocycle Poset One Cochain To Cech Cochain Statement
-- statement:
--   Definitions and structural lemmas for Is Cech One Cocycle Poset One Cochain To Cech Cochain Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCechOneCocyclePosetOneCochainToCechCochainStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp


