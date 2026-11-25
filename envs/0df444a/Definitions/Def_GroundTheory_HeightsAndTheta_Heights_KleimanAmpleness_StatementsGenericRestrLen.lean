-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:53.267728+00:00
-- url     : https://prove2.me/theorems/ec9e74ff-5ee4-4d37-9e71-b7c484e2b152
-- title:
--   Statements Generic Restr Len
-- statement:
--   Definitions and structural lemmas for Statements Generic Restr Len, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsGenericRestrLen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
def GenericRestrLen.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (Q : SubSystem S x Ω) (qq : Ideal (Poly S N)),
    (∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) →
    restrLen (qq.map (MvPolynomial.map (algebraMap S F))) (Q.extend F) =
      (Module.finrank S (Q.secs ⧸ ((Q.twist (idealSys x qq)).secs).comap Q.secs.subtype) : ℤ)
end
end GroundTheory.Heights₂.Heights.Kleiman


