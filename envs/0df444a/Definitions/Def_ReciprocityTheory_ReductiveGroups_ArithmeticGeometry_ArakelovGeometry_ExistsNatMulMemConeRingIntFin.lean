-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:39.708037+00:00
-- url     : https://prove2.me/theorems/62bbbef2-84e6-4dcf-b93c-320ebc46cf7a
-- title:
--   Exists Nat Mul Mem Cone Ring Int Fin
-- statement:
--   Definitions and structural lemmas for Exists Nat Mul Mem Cone Ring Int Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
section Int
variable {ι : Type*}
theorem mem_coneRing_rat_of_int (y : ι → Ω) (v : (Polynomial Ω)) (hv : v ∈ coneRing ℤ y) : v ∈ coneRing ℚ y := by

  rw [coneRing, AlgHom.mem_range] at hv ⊢
  obtain ⟨p, rfl⟩ := hv
  refine ⟨MvPolynomial.map (algebraMap ℤ ℚ) p, ?_⟩
  simp only [coneMap]
  exact MvPolynomial.aeval_map_algebraMap ℚ _ p
def coneRingIntToRat (y : ι → Ω) : coneRing ℤ y →+* coneRing ℚ y where
  toFun s := ⟨s, mem_coneRing_rat_of_int y s s.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end Int
section SlopeTestRemainingChoices
variable {ι : Type*}
end SlopeTestRemainingChoices
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


