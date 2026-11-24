-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:43.968272+00:00
-- url     : https://prove2.me/theorems/519178e5-de26-4cae-af6b-9e2baf366645
-- title:
--   St Poly Germ Point Pow
-- statement:
--   Definitions and structural lemmas for St Poly Germ Point Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPolyGermPointPow.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
def PolyGermPointPow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (q : MvPolynomial σ ℂ),
    polyGerm w q ∈ holGermPointIdeal w ^ k → q ∈ RingHom.ker (MvPolynomial.eval w) ^ k
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


