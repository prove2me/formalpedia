-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsLastLast
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsLastLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:05.177769+00:00
-- url     : https://prove2.me/theorems/05875ada-d31e-41de-b56b-b13b8f458d70
-- title:
--   Imports Last Last
-- statement:
--   Definitions and structural lemmas for Imports Last Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsLastLast.lean

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
def Ample.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : Kleiman.LineBundle S x), Kleiman.AmpleData S x H →
    Nonempty (IndefiniteRowSideFullHecke.Kleiman.AmpleData S x (toIndefiniteRowSideFullHecke H.toSubSystem))
noncomputable def Ample.hyps (k : Type) [Field k] :
    Kleiman.AmpleData k (Kleiman.lineX k) (Kleiman.twistBundle k (Kleiman.lineX k) 1) :=
  Kleiman.twistAmple k (Kleiman.lineX k)
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


