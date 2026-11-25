-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:46.186128+00:00
-- url     : https://prove2.me/theorems/92d4716e-5561-5220-995c-2fcb0e9e06b7
-- title:
--   PRestr Len Euler
-- statement:
--   Definitions and structural lemmas for PRestr Len Euler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrLenEuler.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
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
open MvPolynomial Filter
noncomputable section
universe u w
namespace RestrLenEuler
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
def incl (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    F₂.sub I →ₗ[k] F₁.sub I where
  toFun y := ⟨y, h21 I y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end RestrLenEuler
end
end GroundTheory.Heights₂.Heights.Kleiman


