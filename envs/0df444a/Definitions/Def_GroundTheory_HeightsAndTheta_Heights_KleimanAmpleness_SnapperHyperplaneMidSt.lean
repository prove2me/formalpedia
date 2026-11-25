-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:54.068357+00:00
-- url     : https://prove2.me/theorems/e6aa3ac9-8929-5b63-903f-21dc011d7a78
-- title:
--   Snapper Hyperplane Mid St
-- statement:
--   Definitions and structural lemmas for Snapper Hyperplane Mid St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperHyperplaneMidSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
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
def SnapperHyperplaneMid.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp →
    ∀ (a : ℤ) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
      eulerCharQuot k
          ((((twistSys k x (a + 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)}))).twistPows t
            (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a + 1)).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)) =
        pieceChar k pp a L n c
end
end GroundTheory.Heights₂.Heights.Kleiman


