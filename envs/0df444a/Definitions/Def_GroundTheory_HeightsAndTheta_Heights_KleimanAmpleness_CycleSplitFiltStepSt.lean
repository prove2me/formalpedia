-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CycleSplitFiltStepSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CycleSplitFiltStepSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:54.737061+00:00
-- url     : https://prove2.me/theorems/f18ef930-327c-4125-903d-ec64cfb95c06
-- title:
--   Cycle Split Filt Step St
-- statement:
--   Definitions and structural lemmas for Cycle Split Filt Step St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CycleSplitFiltStepSt.lean

import Mathlib
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
open MvPolynomial Filter
noncomputable section
universe u w
def CycleSplit.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ (K pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ K, ∀ d : ℕ, homogeneousComponent d f ∈ K) → primeOf (S := S) x ≤ K →
    𝔪.map (C : S →+* Poly S N) ≤ K → g.IsHomogeneous e →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → (∀ f, f ∈ pp ↔ f * g ∈ K) →
    ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen K (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (K ⊔ Ideal.span {g}) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen pp (Q.twist (twistSys S x ((c : ℤ) - e)))
end
end GroundTheory.Heights₂.Heights.Kleiman


