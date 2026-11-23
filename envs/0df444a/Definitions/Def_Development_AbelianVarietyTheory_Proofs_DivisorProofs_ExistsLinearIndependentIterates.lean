-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:15.201388+00:00
-- url     : https://prove2.me/theorems/d91f6293-6462-4376-9ae7-cbb7161cae21
-- title:
--   Exists Linear Independent Iterates
-- statement:
--   Definitions and structural lemmas for Exists Linear Independent Iterates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
namespace GlobalTheory.ConjLocal
variable {R : Type} [CommRing R] {n : ℕ}
def iterMat (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (Y ^ (j : ℕ) *ᵥ v) i
def compMat (Q : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -Q.coeff i
end GlobalTheory.ConjLocal
namespace GlobalTheory.ConjLocal
variable {R : Type} [CommRing R] {n : ℕ}
end GlobalTheory.ConjLocal


