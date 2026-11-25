-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeShiftSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeShiftSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:32.184111+00:00
-- url     : https://prove2.me/theorems/de91f828-f1b0-41f9-88da-132b74e63a25
-- title:
--   Tilde Shift St
-- statement:
--   Definitions and structural lemmas for Tilde Shift St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TildeShiftSt.lean

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
def TildeShift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (c : ℤ),
    M.tildeSys c = (M.tildeSys 0).twist (twistSys S x c)
end
end GroundTheory.Heights₂.Heights.Kleiman


