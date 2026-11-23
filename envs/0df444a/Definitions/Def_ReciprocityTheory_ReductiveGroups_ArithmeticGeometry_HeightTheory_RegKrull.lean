-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:50.071062+00:00
-- url     : https://prove2.me/theorems/123d84af-4539-426a-a8f4-0e7ecbfcea0c
-- title:
--   Reg Krull
-- statement:
--   Definitions and structural lemmas for Reg Krull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace KrullColonIdeal
variable {R : Type*} [CommRing R]
def colonI (s c : R) : Ideal R where
  carrier := {r | r * c ∈ Ideal.span {s}}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul]
    exact Ideal.add_mem _ hx hy
  zero_mem' := by simp
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ hx
end KrullColonIdeal
end ReciprocityTheory.ChartRestriction.G.T0


