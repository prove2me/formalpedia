-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:17:14.825006+00:00
-- url     : https://prove2.me/theorems/10557032-1374-4f58-886e-48c9daa79d85
-- title:
--   Quotient H0 Finite Hypotheses Line
-- statement:
--   Definitions and structural lemmas for Quotient H0 Finite Hypotheses Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotientH0FiniteHypothesesLine.lean

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
universe u v w
def QuotientH0Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F G : SubSystem S x E), (∀ I, G.sub I ≤ F.sub I) →
    Module.Finite S (F.H 0) → Module.Finite S (G.H 1) → Module.Finite S (SubSystem.quotH F G 0)
end
end GroundTheory.Heights₂.Heights.Kleiman


