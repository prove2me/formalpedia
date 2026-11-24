-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:12.200693+00:00
-- url     : https://prove2.me/theorems/531ee270-7d4e-4c0c-aa26-ec7d897cdafe
-- title:
--   Inter Red A
-- statement:
--   Definitions and structural lemmas for Inter Red A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def HermLine.inv (B : HermLine ι) : HermLine ι where
  a := -B.a
  h z := (B.h z)⁻¹
  pos z hz := inv_pos.mpr (B.pos z hz)
  smul c z hc := by
    rw [B.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, zpow_neg]
variable {P J : Ideal (MRing ι)} {e : ℕ}
def PotOfPotentialStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnLogRes P J e) (L : HermLine ι), IsSmoothHerm L → IsPotential R.A (potOf R L)
end ReciprocityTheory.ChartRestriction.G.Geo


