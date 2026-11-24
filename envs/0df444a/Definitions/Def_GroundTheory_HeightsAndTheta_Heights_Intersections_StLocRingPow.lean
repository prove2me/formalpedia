-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:15.655566+00:00
-- url     : https://prove2.me/theorems/85b62114-a84e-41df-8955-b49e91794f11
-- title:
--   St Loc Ring Pow
-- statement:
--   Definitions and structural lemmas for St Loc Ring Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StLocRingPow.lean

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
def LocRingPow.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ P))
    (u v : MRing ι) (b : K → ℕ) (y : FractionRing (MRing ι ⧸ P)),
    P.IsPrime → IsMultiHomogIdeal P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsMultiHomog t a → t ∉ W → x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    IsMultiHomog u b → IsMultiHomog v b → u ∈ W → v ∉ W → y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
    ∃ n : ℕ, ∃ z ∈ locRing P W, y ^ n = x * z
end
end GroundTheory.Heights₂.Heights.Inter


