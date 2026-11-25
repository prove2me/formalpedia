-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:41.898849+00:00
-- url     : https://prove2.me/theorems/ef05b911-7437-40fc-a06f-d231d9169c41
-- title:
--   Snapper Subquot Finite St
-- statement:
--   Definitions and structural lemmas for Snapper Subquot Finite St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperSubquotFiniteSt.lean

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
def SnapperSubquotFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F F₁ F₂ : SubFamily k x E), (∀ I, (F.sub I).FG) → (∀ I, F₁.sub I ≤ F.sub I) →
    (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ i : ℕ, FiniteDimensional k (SubSystem.quotH F₁.toSubSystem F₂.toSubSystem i)
end
end GroundTheory.Heights₂.Heights.Kleiman


