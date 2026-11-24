-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGeneratorsClearDenominators
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGeneratorsClearDenominators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:12.830021+00:00
-- url     : https://prove2.me/theorems/c42b0df9-dc88-498f-b55c-fe3aabf037f1
-- title:
--   St Local Generators Clear Denominators
-- statement:
--   Definitions and structural lemmas for St Local Generators Clear Denominators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalGeneratorsClearDenominators.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyOriginIdeal_isMaximal_f9e3f262b184

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
theorem LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime
attribute [local instance] LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime
def LocalGeneratorsClearDenominators.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T),
    (∀ i, f i ∈ P) →
    maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 →
      ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


