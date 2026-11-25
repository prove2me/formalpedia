-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:27:17.767282+00:00
-- url     : https://prove2.me/theorems/e4c80383-c4fd-52bd-80b0-d6280b5c0876
-- title:
--   Mul Quot Eq St
-- statement:
--   Definitions and structural lemmas for Mul Quot Eq St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulQuotEqSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
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
def MulQuotEq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (s : Ω),
    (∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) →
    (∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I) →
    (∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) →
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂
end
end GroundTheory.Heights₂.Heights.Kleiman


