-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:38.933842+00:00
-- url     : https://prove2.me/theorems/6b88fbed-6626-4516-a1ea-8761fdc3bb17
-- title:
--   Imports Ter Rest
-- statement:
--   Definitions and structural lemmas for Imports Ter Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerRest.lean

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
def regularityLocalResidue_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → ∀ [IsLocalRing (locRing P W)],
    Finite (IsLocalRing.ResidueField (locRing P W)) ∧
      Nat.card (IsLocalRing.ResidueField (locRing P W)) = charOf W ^ (geoNum 0 W b).toNat
end
end GroundTheory.Heights₂.Heights.Inter


