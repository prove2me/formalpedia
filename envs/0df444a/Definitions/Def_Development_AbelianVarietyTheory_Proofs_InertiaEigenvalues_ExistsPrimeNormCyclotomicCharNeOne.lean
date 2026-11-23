-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:10.221678+00:00
-- url     : https://prove2.me/theorems/30f9cbb3-a61c-4cb3-bb87-cfa834e04aa0
-- title:
--   Exists Prime Norm Cyclotomic Char Ne One
-- statement:
--   Definitions and structural lemmas for Exists Prime Norm Cyclotomic Char Ne One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeNormCyclotomicCharNeOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotForallExistsTwoLiesOverAbsNormEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
namespace GlobalTheory.NormChar
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in

theorem _root_.GlobalTheory.NormChar.smulComm (K L : Type) [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := by
  refine ⟨fun σ a x => ?_⟩
  apply RingOfIntegers.ext
  have h1 : ((a • x : 𝓞 L) : L) = algebraMap K L a * x := by
    rw [Algebra.smul_def]; rfl
  have h3 : ((σ • (a • x) : 𝓞 L) : L) = σ ((a • x : 𝓞 L) : L) := rfl
  rw [h3, h1, Algebra.smul_def]
  push_cast
  rw [map_mul, AlgEquiv.commutes]
  rfl
attribute [local instance] smulComm
end GlobalTheory.NormChar


