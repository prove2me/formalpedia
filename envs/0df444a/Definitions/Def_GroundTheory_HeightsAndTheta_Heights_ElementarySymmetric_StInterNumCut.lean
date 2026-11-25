-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:38:34.095634+00:00
-- url     : https://prove2.me/theorems/0498117e-fd3e-4179-8759-2ece0b504a36
-- title:
--   St Inter Num Cut
-- statement:
--   Definitions and structural lemmas for St Inter Num Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StInterNumCut.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
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
open Classical in

def InterNumCut.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp (n + 1) → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      interNum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i => (L i).toSubSystem)
          Lc.toSubSystem) =
        ∑ᶠ qq : Ideal (Poly k N),
          if h : qq ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes ∧ IsSubvar x qq n then
            haveI : qq.IsPrime := h.1.1.1
            ((cutMult (pp ⊔ zeroIdeal Lc.toSubSystem s) qq).toNat : ℤ) *
              interNum qq (fun i => (L i).toSubSystem)
          else 0
end
end GroundTheory.Heights₂.Heights.Kleiman


