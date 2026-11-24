-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:15.858528+00:00
-- url     : https://prove2.me/theorems/060828f8-3aa0-4b45-b1ba-ef0e7fc3f5ab
-- title:
--   Statements Complex Minimal Primes Contract
-- statement:
--   Definitions and structural lemmas for Statements Complex Minimal Primes Contract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComplexMinimalPrimesContract.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
noncomputable section
def ComplexMinimalPrimesContract.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    ∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


