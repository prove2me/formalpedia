-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:24.694503+00:00
-- url     : https://prove2.me/theorems/d32699b4-82f4-4620-ba7c-e0fac8d2e4b0
-- title:
--   ABridge St B
-- statement:
--   Definitions and structural lemmas for ABridge St B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct
section Poly
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]
def evalT (x : J → Ω) : MvPolynomial J ℂ →ₐ[ℂ] ℂ ⊗[ℚ] Ω :=
  aeval fun j => (1 : ℂ) ⊗ₜ[ℚ] x j
end Poly
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


