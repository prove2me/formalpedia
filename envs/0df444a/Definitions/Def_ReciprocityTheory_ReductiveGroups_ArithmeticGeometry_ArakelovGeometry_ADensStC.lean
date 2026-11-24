-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:13:02.621429+00:00
-- url     : https://prove2.me/theorems/6d4c001e-2af4-43b5-ad9b-17a68dd26d9d
-- title:
--   ADens St C
-- statement:
--   Definitions and structural lemmas for ADens St C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
section Poly
variable {J : Type} [Fintype J]
end Poly
variable {J : Type} [Fintype J] {D : ℕ}
def adensF (m : ConeMetric ℂ J) (γ : (Fin D → ℂ) → J → ℂ) (ν : (Fin D → ℂ) → ℝ)
    (y : Fin D → ℂ) : ℝ :=
  maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y / ((D.factorial : ℝ) * ν y)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


