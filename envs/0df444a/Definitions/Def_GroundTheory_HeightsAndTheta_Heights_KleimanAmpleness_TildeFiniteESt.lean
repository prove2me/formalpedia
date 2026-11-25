-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:37.453619+00:00
-- url     : https://prove2.me/theorems/c6cd17ff-1901-4667-baf2-fdae19fd39b1
-- title:
--   Tilde Finite ESt
-- statement:
--   Definitions and structural lemmas for Tilde Finite ESt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TildeFiniteESt.lean

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
def TildeFiniteE.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (i : ℕ) (c : ℤ),
    Module.Finite S ((M.tildeSys c).H i)
end
end GroundTheory.Heights₂.Heights.Kleiman


