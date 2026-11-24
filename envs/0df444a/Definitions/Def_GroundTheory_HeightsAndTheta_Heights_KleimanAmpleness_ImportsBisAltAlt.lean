-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:56.599642+00:00
-- url     : https://prove2.me/theorems/a79911a2-f2da-4bcf-ad68-2d023db7d3bb
-- title:
--   Imports Bis Alt Alt
-- statement:
--   Definitions and structural lemmas for Imports Bis Alt Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsBisAltAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
def LineBundle.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω),
    (∀ Q : Kleiman.LineBundle S x,
      ∃ Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x, ∀ i, Q'.mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i) ∧
    ∀ Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x,
      ∃ Q : Kleiman.LineBundle S x, ∀ i, x i ≠ 0 → Q'.mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


