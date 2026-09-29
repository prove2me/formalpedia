-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.mul_left_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/82df6714-4aa9-5dbf-b385-75e9f2680021

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel

set_option autoImplicit false

universe u

namespace Ideal p2m_export "Ideal" "span mem_span_singleton_mul" end Ideal
p2m_open_scoped "Ideal" in

theorem Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {a : R} (ha : a ∈ nonZeroDivisors R) :
    Function.Injective fun K : Ideal R ↦ Ideal.span {a} * K := by

  suffices key : ∀ K K' : Ideal R, Ideal.span {a} * K = Ideal.span {a} * K' → K ≤ K' from
    fun K K' h ↦ le_antisymm (key K K' h) (key K' K h.symm)
  intro K K' h x hx
  have hax : a * x ∈ Ideal.span {a} * K' := h ▸ Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Ideal.mem_span_singleton_mul.mp hax
  rwa [← (mul_cancel_left_mem_nonZeroDivisors ha).mp hyx]

open AlgebraicGeometry

theorem solution {X : Scheme.{u}}
    {I J J' : X.IdealSheafData} (hI : I.IsInvertible) (h : I * J = I * J') : J = J' := by
  choose U f hxf g hg hIg using hI
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x : X ↦ X.affineBasicOpen (f x)) ?_ ?_
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxf x⟩
  · intro x
    have hx := congrArg (fun K : X.IdealSheafData ↦ K.ideal (X.affineBasicOpen (f x))) h
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIg] at hx
    exact Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors (hg x) hx

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel (solution)
