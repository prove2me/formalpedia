-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:27.586264+00:00
-- url     : https://prove2.me/theorems/21adbf75-9230-4a16-823d-60941415df6e
-- title:
--   Same Orbit One Spec Z
-- statement:
--   Definitions and structural lemmas for Same Orbit One Spec Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/SameOrbitOneSpecZ.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
def VerticalClosedPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    vertR P (Fin.elim0 : Fin 0 → HermLine ι) f - vertR P (Fin.elim0 : Fin 0 → HermLine ι) g =
      ∑ t ∈ R, Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ / ‖eval t (map (Int.castRingHom ℂ) g)‖)
end
end GroundTheory.Heights₂.Heights.Inter


