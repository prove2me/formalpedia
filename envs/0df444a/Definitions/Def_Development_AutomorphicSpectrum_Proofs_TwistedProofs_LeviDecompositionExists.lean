-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:54.921547+00:00
-- url     : https://prove2.me/theorems/dd6648a5-1bca-4b0c-a76c-1a07f2537836
-- title:
--   Levi Decomposition Exists
-- statement:
--   Definitions and structural lemmas for Levi Decomposition Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LeviDecompositionExists.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertLevi
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
def edge (c d : L) (f : Fin N → L) : Fin (N + 2) → L := Fin.cons c (Fin.snoc f d : Fin (N + 1) → L)
def blkMat (x y : L) (A : Matrix (Fin N) (Fin N) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  fun i j => edge (edge x 0 (fun _ => 0) j) (edge 0 y (fun _ => 0) j) (fun p => edge 0 0 (A p) j) i
end GlobalTheory.CompanionTheory.InertLevi
end


