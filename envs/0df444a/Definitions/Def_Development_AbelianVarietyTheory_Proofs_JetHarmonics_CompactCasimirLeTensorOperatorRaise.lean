-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaise
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaise
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:29:00.16535+00:00
-- url     : https://prove2.me/theorems/9f991e37-a148-4c42-87e4-316f14bc13b7
-- title:
--   Compact Casimir Le Tensor Operator Raise
-- statement:
--   Definitions and structural lemmas for Compact Casimir Le Tensor Operator Raise, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeTensorOperatorRaise.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.TensOp
def tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) : Module.End ℂ (PiLp 2 (fun _ : ι => V)) where
  toFun x := WithLp.toLp 2 (fun i => E (x i) + ∑ j, A i j • x j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
    abel
  map_smul' r x := by
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]
def sumMap {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) :
    PiLp 2 (fun _ : ι => V) →ₗ[ℂ] N where
  toFun x := ∑ j, φ j (x j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]
end GlobalTheory.TensOp


