-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:16.988835+00:00
-- url     : https://prove2.me/theorems/cd3d0177-4894-5286-b2ba-4c7979ba52c9
-- title:
--   St Imaginary Lattice Cocompact
-- statement:
--   Definitions and structural lemmas for St Imaginary Lattice Cocompact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StImaginaryLatticeCocompact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable (F E : Type*) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
def ImaginaryLatticeCocompact.Statement : Prop :=
  ∀ m : ℕ, 0 < m → ∃ R : ℝ, ∀ s : InfinitePlace E → ℝ, ∃ a : 𝓞 E,
    (m : E) * a + conj F E ((m : E) * a) = 0 ∧ ∀ w, |(w.embedding ((m : E) * a)).im - s w| ≤ R
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


