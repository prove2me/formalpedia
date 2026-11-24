-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:45.044623+00:00
-- url     : https://prove2.me/theorems/ab369b97-be8d-4fe9-8af0-e9c115e28fd5
-- title:
--   Fibre St D
-- statement:
--   Definitions and structural lemmas for Fibre St D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_mem_fnField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x := by
  exact IntermediateField.subset_adjoin ℚ {t | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩
theorem deh_mem_fnField {ι : Type*} (y : ι → Ω) (i₀ : ι) (m : MvPolynomial ι ℤ) :
    deh y i₀ m ∈ fnField y := by
  rw [deh_apply]
  induction m using MvPolynomial.induction_on
  · rw [MvPolynomial.eval₂_C]
    simpa using intCast_mem (fnField y) _
  · rw [MvPolynomial.eval₂_add]
    exact add_mem ‹_› ‹_›
  · rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem ‹_› (div_mem_fnField y _ i₀)
def dehK (y : Fin (D + 1) → Ω) : MvPolynomial (Fin (D + 1)) ℤ →+* fnField y :=
  (deh y 0).codRestrict (fnField y).toSubfield.toSubring fun m => deh_mem_fnField y 0 m
def chartGen (y : Fin (D + 1) → Ω) (k : {k : Fin (D + 1) // k ≠ 0}) : fnField y :=
  ⟨y k / y 0, div_mem_fnField y k 0⟩
def chartRing (y : Fin (D + 1) → Ω) : Subalgebra ℤ (fnField y) :=
  Algebra.adjoin ℤ (Set.range (chartGen y))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}
abbrev Lx (x : ι → Ω) (e : Fin (D + 1) → ι) : IntermediateField (fnField (x ∘ e)) Ω :=
  extendScalars (fnField_comp_le x e)
def gL (x : ι → Ω) (e : Fin (D + 1) → ι) (i : ι) : Lx x e :=
  ⟨x i / x (e 0), div_mem_fnField x i (e 0)⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib


