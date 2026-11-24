-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:04.2924+00:00
-- url     : https://prove2.me/theorems/2902baeb-203d-42c3-aeea-c3f8d5f95787
-- title:
--   Eq Zero Of Sec Trace Mul Eq Zero
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Sec Trace Mul Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqZeroOfSecTraceMulEqZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
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
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
theorem fnField_comp_le (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  exact TraceNormBounds.fnField_comp_le' x e
def fnTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (t : Ω) : Ω :=
  open Classical in
  if ht : t ∈ fnField x then
    ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le x e)) ⟨t, ht⟩ : fnField (x ∘ e)) : Ω)
  else 0
def secTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (n : ℕ) (s : Ω) : Ω :=
  x (e 0) ^ n * fnTrace x e (s / x (e 0) ^ n)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


