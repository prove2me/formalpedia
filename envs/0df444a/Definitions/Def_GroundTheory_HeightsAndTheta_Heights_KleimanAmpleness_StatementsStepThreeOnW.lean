-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:01.188928+00:00
-- url     : https://prove2.me/theorems/fe1623bd-99d4-4f83-929f-ef9921e5333b
-- title:
--   Statements Step Three On W
-- statement:
--   Definitions and structural lemmas for Statements Step Three On W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsStepThreeOnW.lean

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
def StepThree.OnW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ I : Chart x,
      ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) (((T.L.pow b).twist (twistSys k x c)).secs : Set Ω) ⊔
          (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I
end
end GroundTheory.Heights₂.Heights.Kleiman


