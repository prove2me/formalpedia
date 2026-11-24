-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:10.521158+00:00
-- url     : https://prove2.me/theorems/b2597594-e0ff-4d64-a064-1d39200b8ca1
-- title:
--   St Derivation Cotangent Independent
-- statement:
--   Definitions and structural lemmas for St Derivation Cotangent Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDerivationCotangentIndependent.lean

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
def DerivationCotangentIndependent.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (D : Fin h → Derivation ℤ T T)
    (f : Fin h → T), (∀ i, f i ∈ P) → (Matrix.of fun i j => D j (f i)).det ∉ P →
      ∀ a : Fin h → Localization.AtPrime P,
        ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈
            maximalIdeal (Localization.AtPrime P) ^ 2 →
          ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


