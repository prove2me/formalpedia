-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:49.516138+00:00
-- url     : https://prove2.me/theorems/6e1903f4-baf5-441d-81d6-ccbbd1cf546e
-- title:
--   Projective Frame Coord Ne Zero
-- statement:
--   Definitions and structural lemmas for Projective Frame Coord Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
theorem fnField_comp_le' (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨i, j, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨e i, e j, rfl⟩
def homogz {σ : Type*} (j : σ → Fin (D + 1)) (l : Fin (D + 1)) (N : ℕ) (g : MvPolynomial σ ℤ) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ d ∈ Finset.range (N + 1), MvPolynomial.X l ^ (N - d) *
    MvPolynomial.rename j (MvPolynomial.homogeneousComponent d g)
def dehom (l : Fin (D + 1)) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial {k // k ≠ l} ℤ :=
  MvPolynomial.aeval fun k => if h : k = l then 1 else MvPolynomial.X ⟨k, h⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds


