-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:44.072173+00:00
-- url     : https://prove2.me/theorems/41c6d3a8-5427-4934-a053-eb822da34a36
-- title:
--   Adjoin Gelfand Invariants Dual Pair Eq
-- statement:
--   Definitions and structural lemmas for Adjoin Gelfand Invariants Dual Pair Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
namespace GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
def trAlg (M : Matrix (Fin n) (Fin n) A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range fun k : ℕ => (M ^ (k + 1)).trace)
section CCR
variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)
end CCR
end GlobalTheory.Mem.Capelli


