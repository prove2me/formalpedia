-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltStepSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltStepSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:18:19.26647+00:00
-- url     : https://prove2.me/theorems/dc3e8c92-2a0c-47a8-bd1a-ff3239e1b9e9
-- title:
--   Section Count Drop Filt Step St
-- statement:
--   Definitions and structural lemmas for Section Count Drop Filt Step St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionCountDropFiltStepSt.lean

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
def SectionCount.Drop.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle S x) (J₁ pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ J₁, ∀ d : ℕ, homogeneousComponent d f ∈ J₁) → primeOf (S := S) x ≤ J₁ →
    g.IsHomogeneous e → (∀ f, f ∈ pp ↔ f * g ∈ J₁) →
    ∃ φ : (Q.twist (idealSys x (J₁ ⊔ Ideal.span {g}))).secs →ₗ[S]
        SubSystem.quotH (Q.twist (twistSys S x (-(e : ℤ))))
          ((Q.twist (twistSys S x (-(e : ℤ)))).twist (idealSys x pp)) 0,
      ∀ s, φ s = 0 → (s : Ω) ∈ (Q.twist (idealSys x J₁)).secs
end
end GroundTheory.Heights₂.Heights.Kleiman


