-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:49:29.839797+00:00
-- url     : https://prove2.me/theorems/b057f9a9-02e0-4af9-984c-e7d79c75a323
-- title:
--   Exists Basis Tensor
-- statement:
--   Definitions and structural lemmas for Exists Basis Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsBasisTensor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
namespace GlobalTheory.SemilinearExt
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
section
variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end
def extOfBasis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V']
    (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') : V →ₛₗ[σ] V' where
  toFun x := ∑ k, σ (B.repr x k) • w k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]
end GlobalTheory.SemilinearExt


