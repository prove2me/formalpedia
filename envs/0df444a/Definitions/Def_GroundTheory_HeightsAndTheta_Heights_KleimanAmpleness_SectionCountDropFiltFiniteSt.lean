-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltFiniteSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltFiniteSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:36.666214+00:00
-- url     : https://prove2.me/theorems/6398ac0a-beac-45af-9dac-bbbeb07f73ce
-- title:
--   Section Count Drop Filt Finite St
-- statement:
--   Definitions and structural lemmas for Section Count Drop Filt Finite St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionCountDropFiltFiniteSt.lean

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
def SectionCount.Drop.Filt.Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (pp : Ideal (Poly S N)) (c : ℤ), pp.IsPrime →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → primeOf (S := S) x ≤ pp →
    Module.Finite S (SubSystem.quotH (Q.twist (twistSys S x c))
      ((Q.twist (twistSys S x c)).twist (idealSys x pp)) 0)
end
end GroundTheory.Heights₂.Heights.Kleiman


