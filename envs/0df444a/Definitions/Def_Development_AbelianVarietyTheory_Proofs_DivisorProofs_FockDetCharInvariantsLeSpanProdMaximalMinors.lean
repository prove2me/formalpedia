-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:26:54.123564+00:00
-- url     : https://prove2.me/theorems/49e7624e-0139-47c9-bee5-c2293ea821b6
-- title:
--   Fock Det Char Invariants Le Span Prod Maximal Minors
-- statement:
--   Definitions and structural lemmas for Fock Det Char Invariants Le Span Prod Maximal Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDenseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
namespace GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
end GlobalTheory.MinorFrame


