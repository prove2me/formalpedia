-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecRankSpecialize
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecRankSpecialize
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:17:32.657153+00:00
-- url     : https://prove2.me/theorems/b42cb9f8-b09f-42ba-b428-e5085362fad5
-- title:
--   PSec Rank Specialize
-- statement:
--   Definitions and structural lemmas for PSec Rank Specialize, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecRankSpecialize.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace SecRankSpecialize
open Vertical
def secMap {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    SecAlg Q y →ₐ[R] SecAlg (Q.map (MvPolynomial.map (algebraMap R S))) (algebraMap R S ∘ y) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId R S))
    (by rw [SecAlgFieldChange.secIdeal_map]; exact Ideal.le_comap_map)
end SecRankSpecialize
end
end GroundTheory.Heights₂.Heights


