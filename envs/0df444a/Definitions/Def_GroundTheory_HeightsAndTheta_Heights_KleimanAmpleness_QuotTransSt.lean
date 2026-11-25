-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:00.897251+00:00
-- url     : https://prove2.me/theorems/c41ae755-ca14-5a4d-b2c3-09e40ebd1c36
-- title:
--   Quot Trans St
-- statement:
--   Definitions and structural lemmas for Quot Trans St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/QuotTransSt.lean

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
def QuotTrans.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F₁ F₂ F₃ : SubSystem S x E), (∀ I, F₃.sub I ≤ F₂.sub I) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    Subsingleton (SubSystem.quotH F₂ F₃ 1) → Subsingleton (SubSystem.quotH F₁ F₂ 1) →
    Subsingleton (SubSystem.quotH F₁ F₃ 1)
end
end GroundTheory.Heights₂.Heights.Kleiman


