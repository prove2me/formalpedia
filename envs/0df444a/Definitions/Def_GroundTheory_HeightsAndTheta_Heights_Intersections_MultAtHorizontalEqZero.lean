-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:06.958571+00:00
-- url     : https://prove2.me/theorems/afc4afb0-88c2-4c5c-8e89-5ec06927cfb0
-- title:
--   Mult At Horizontal Eq Zero
-- statement:
--   Definitions and structural lemmas for Mult At Horizontal Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
section Lemmas
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end Lemmas
def IndependenceOfSmoothMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s t : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s → IsSectionOn P A t →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P (Fin.elim0 : Fin 0 → HermLine ι) A t
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


