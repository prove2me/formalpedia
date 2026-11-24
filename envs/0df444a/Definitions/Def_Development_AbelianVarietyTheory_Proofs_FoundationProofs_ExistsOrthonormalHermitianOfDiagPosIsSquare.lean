-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsOrthonormalHermitianOfDiagPosIsSquare
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsOrthonormalHermitianOfDiagPosIsSquare
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T19:39:09.8558+00:00
-- url     : https://prove2.me/theorems/bb005802-ba3b-47ae-957b-735b4f3276ad
-- title:
--   Exists Orthonormal Hermitian Of Diag Pos Is Square
-- statement:
--   Definitions and structural lemmas for Exists Orthonormal Hermitian Of Diag Pos Is Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsOrthonormalHermitianOfDiagPosIsSquare.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandherrAndLandherrSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory.SqDet
section
variable {K : Type} [Field K] [NumberField K] {d : ℕ} {θ : K}
end
end GlobalTheory.SqDet


