-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerBis
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:26.721202+00:00
-- url     : https://prove2.me/theorems/6a824ad5-d1fb-4079-aecd-c1cc368169cf
-- title:
--   Imports Ter Bis
-- statement:
--   Definitions and structural lemmas for Imports Ter Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerBis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def regularityDehomogenization_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → IsMultiHomog t a → t ∉ W →
    y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    y ∈ locRing P W ∧
      multAt (P ⊔ Ideal.span {s}) W = (Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat
end
end GroundTheory.Heights₂.Heights.Inter


