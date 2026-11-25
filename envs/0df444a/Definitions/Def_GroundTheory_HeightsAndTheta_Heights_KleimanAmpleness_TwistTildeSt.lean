-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:57:06.001941+00:00
-- url     : https://prove2.me/theorems/8e106cc0-7c5f-40d5-bddd-d3e2319c7617
-- title:
--   Twist Tilde St
-- statement:
--   Definitions and structural lemmas for Twist Tilde St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistTildeSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
def TwistTilde.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω),
    ∃ P : FinGradedSub (S := S) (x := x) E,
      (∀ c : ℤ, P.piece c = Submodule.span S {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧
        m ∈ M.piece b ∧ a + b = c ∧ z = q • m}) ∧
      ∀ I, ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = P.tilde 0 I
end
end GroundTheory.Heights₂.Heights.Kleiman


