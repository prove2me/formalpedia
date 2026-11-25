-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:17:28.022991+00:00
-- url     : https://prove2.me/theorems/bde448e3-1136-4a4c-ab10-d852abdd1df0
-- title:
--   St Inter Num Eventual
-- statement:
--   Definitions and structural lemmas for St Inter Num Eventual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StInterNumEventual.lean

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
universe u w
def InterNumEventual.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x), IsSubvar x pp n →
      ∃ m : ℤ, ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c = m
end
end GroundTheory.Heights₂.Heights.Kleiman


