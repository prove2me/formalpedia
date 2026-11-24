-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:53.614464+00:00
-- url     : https://prove2.me/theorems/768185eb-3d09-4f04-96f3-4a567199bdee
-- title:
--   Statements Orbit Comp Nonvanish
-- statement:
--   Definitions and structural lemmas for Statements Orbit Comp Nonvanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsOrbitCompNonvanish.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def OrbitCompNonvanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (E : MRing ι),
    IsMultiHomogIdeal P → E ∉ P →
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ P ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) E) ≠ 0
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


