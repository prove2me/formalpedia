-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:32.744827+00:00
-- url     : https://prove2.me/theorems/aca9d461-93f3-4639-876a-1214dce3bffd
-- title:
--   Statements Fibre Comp Dim Z
-- statement:
--   Definitions and structural lemmas for Statements Fibre Comp Dim Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/StatementsFibreCompDimZ.lean

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
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
def FibreCompDimZ.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥ → ∀ (d p : ℕ), p.Prime →
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) →
        ∀ W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
          ringKrullDim (MvPolynomial σ ℤ ⧸ W) = ((d : ℕ) : WithBot ℕ∞)
end GroundTheory.Heights₂.Heights


