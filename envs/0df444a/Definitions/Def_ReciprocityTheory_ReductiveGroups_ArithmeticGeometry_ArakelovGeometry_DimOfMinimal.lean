-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:23.784932+00:00
-- url     : https://prove2.me/theorems/755faa93-4737-4bc1-a651-5e5bddbb1720
-- title:
--   Dim Of Minimal
-- statement:
--   Definitions and structural lemmas for Dim Of Minimal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/DimOfMinimal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def appr (L : ℝ) (d : ℕ) (W : Ideal (MRing ι)) (a : K → ℕ) : ℝ :=
  L * (geoNum d W (fun _ k => (a k : ℤ)) : ℝ) / d.factorial
def HAsymp (L : ℝ) (d : ℕ) (W : Ideal (MRing ι)) : Prop :=
  ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
    |lg W a - appr L d W a| ≤ C * d * ((tdeg a : ℝ) + 1) ^ (d - 1)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


