-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomIdeal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:10.900605+00:00
-- url     : https://prove2.me/theorems/f1b610cd-deb1-5d81-982d-80a57f98e337
-- title:
--   St Chart Dehom Ideal
-- statement:
--   Definitions and structural lemmas for St Chart Dehom Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartDehomIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal)
def ChartDehomIdeal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P →
      segreChartIdeal P σ i =
        (((P.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).radical).comap (segreDehom σ i)
end GroundTheory.Heights₂.Heights.Targets


