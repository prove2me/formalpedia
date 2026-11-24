-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:48.358435+00:00
-- url     : https://prove2.me/theorems/a1579a96-6bf0-4315-a3c2-bf40a7b64388
-- title:
--   Statements Cone Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Cone Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/StatementsConeTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
def ConeTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), Geo.Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Geo.IsHorizontal (Geo.mCoordIdeal y) →
        Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ Ω + Fintype.card K
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights


