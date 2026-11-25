-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetOneCochainToCechCochainCoboundaryStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetOneCochainToCechCochainCoboundaryStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:43.080434+00:00
-- url     : https://prove2.me/theorems/55bffb79-fdc3-51be-b640-782b3cfcfe7c
-- title:
--   Poset One Cochain To Cech Cochain Coboundary Statement
-- statement:
--   Definitions and structural lemmas for Poset One Cochain To Cech Cochain Coboundary Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosetOneCochainToCechCochainCoboundaryStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetOneCochainToCechCochainCoboundary
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


