-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:42.004808+00:00
-- url     : https://prove2.me/theorems/bf380656-03b6-47fd-aa35-5eafb2fd3f67
-- title:
--   Kos Block Mul Kos D
-- statement:
--   Definitions and structural lemmas for Kos Block Mul Kos D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
def kosBlock {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
    (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R) :
    Matrix (KIx g d N) (KIx g d N) R :=
  Matrix.fromBlocks (Matrix.blockDiagonal' fun I : Finset (Fin g) => C I.card) 0 0 P
section
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
end
end GlobalTheory.KeyKa


