-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:12:45.226834+00:00
-- url     : https://prove2.me/theorems/f9b62b6f-05f4-48a4-9609-db471224d0bc
-- title:
--   Inter Num Restrict St
-- statement:
--   Definitions and structural lemmas for Inter Num Restrict St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/InterNumRestrictSt.lean

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
open MvPolynomial Filter
noncomputable section
universe u v w
def InterNumRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (n : ℕ), IsSubvar y pp n →
    ∀ (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y) (r : Fin n → Ω → K'),
      (∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (r i)) →
      interNum pp (fun i => (L' i).toSubSystem) = interNum pp (fun i => (L i).toSubSystem)
end
end GroundTheory.Heights₂.Heights.Kleiman


