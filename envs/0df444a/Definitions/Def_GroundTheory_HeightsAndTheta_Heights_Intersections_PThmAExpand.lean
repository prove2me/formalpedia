-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:56.411675+00:00
-- url     : https://prove2.me/theorems/b5a2db1c-3d93-4082-bb28-db8c328b23cd
-- title:
--   PThm AExpand
-- statement:
--   Definitions and structural lemmas for PThm AExpand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def famExt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (e : Fin 2 → HermLine ι) : MultilinearMap ℝ (fun _ : Fin n => Fin 2 → ℝ) ℝ :=
  ∑ s : Fin n → Fin 2,
    I P n (e ∘ s) • (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap fun j => LinearMap.proj (s j)
section Family
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
end Family
end
end GroundTheory.Heights₂.Heights.Inter


