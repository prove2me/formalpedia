-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLift
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:07.202807+00:00
-- url     : https://prove2.me/theorems/2f869d9f-cc03-4c2d-b5a3-5fbc4c67e005
-- title:
--   Finrank Eigenspace Monomial Matrix Lift
-- statement:
--   Definitions and structural lemmas for Finrank Eigenspace Monomial Matrix Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.MonoEigen
def orbProd {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (m : ℕ) (j : Fin n) : K :=
  ∏ i ∈ Finset.range m, a ((σ ^ i) j)
def GoodRep {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (j : Fin n) : Prop :=
  (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1
section
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
end
end GlobalTheory.MonoEigen


