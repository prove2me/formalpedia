-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:32.463848+00:00
-- url     : https://prove2.me/theorems/e3ef8b12-b5ba-4ea7-a1e3-1872d1dbc9a9
-- title:
--   Phi Eq Zero Iff
-- statement:
--   Definitions and structural lemmas for Phi Eq Zero Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
def blk (X : Matrix n n B) : Matrix (n ⊕ n) (n ⊕ n) B := fromBlocks (1 + X) (-X) X (1 - X)
def phi (c : B →+* B) (J X : Matrix n n B) : Matrix n n B := Xᵀ * J + J * X.map c
def tau (c : B →+* B) (J K X : Matrix n n B) : Matrix n n B := -(J * X.map c * K)ᵀ
def proj (c : B →+* B) (J K : Matrix n n B) (h : B) (X : Matrix n n B) : Matrix n n B := h • (X + tau c J K X)
end GlobalTheory.EisBL.NilAlg


