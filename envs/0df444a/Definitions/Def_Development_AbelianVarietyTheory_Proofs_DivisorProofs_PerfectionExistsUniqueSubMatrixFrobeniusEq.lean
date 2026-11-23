-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:58.772717+00:00
-- url     : https://prove2.me/theorems/340e8199-e740-4d78-9190-9b68f3cfcfbe
-- title:
--   Perfection Exists Unique Sub Matrix Frobenius Eq
-- statement:
--   Definitions and structural lemmas for Perfection Exists Unique Sub Matrix Frobenius Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PerfectionExistsUniqueSubMatrixFrobeniusEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Matrix
noncomputable def perfLevelOp (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) : (ι → S) →+ (ι → S) where
  toFun w := (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k)
  map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
  map_add' a b := by ext i; simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
end GlobalTheory


