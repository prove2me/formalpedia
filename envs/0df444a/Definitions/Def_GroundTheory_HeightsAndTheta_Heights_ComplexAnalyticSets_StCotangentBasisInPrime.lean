-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCotangentBasisInPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCotangentBasisInPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:37.882433+00:00
-- url     : https://prove2.me/theorems/495e2df0-3af7-4caf-9e12-446971cfd642
-- title:
--   St Cotangent Basis In Prime
-- statement:
--   Definitions and structural lemmas for St Cotangent Basis In Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCotangentBasisInPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
def CotangentBasisInPrime.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime],
    ∃ (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) ∧
      maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 ∧
      ∀ a : Fin h → Localization.AtPrime P,
        ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
          ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


