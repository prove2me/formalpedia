-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:36.45755+00:00
-- url     : https://prove2.me/theorems/8e6da663-30ca-4209-b743-61ad3157aad8
-- title:
--   PFinite Map Open
-- statement:
--   Definitions and structural lemmas for PFinite Map Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
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
open MvPolynomial Filter Topology
noncomputable section
namespace FiniteMapOpen
abbrev evalYT {d : ℕ} (F : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (t : ℂ) : ℂ :=
  (F.map (MvPolynomial.eval y)).eval t
variable {n d : ℕ}
def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    (MvPolynomial (Fin n) ℂ ⧸ J) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ J (aeval z) fun q hq => by rw [aeval_eq_eval]; exact hz q hq
end FiniteMapOpen
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


