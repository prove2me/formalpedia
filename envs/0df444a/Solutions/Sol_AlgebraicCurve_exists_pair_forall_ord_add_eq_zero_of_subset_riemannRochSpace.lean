-- Prove2me | solution 1 for AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a047209a-07dd-5c61-aeab-259799641c2f

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace

set_option autoImplicit false

open Submodule AlgebraicCurve in

theorem solution
    {K F : Type*} [Field K] [Infinite K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (D : AlgebraicCurve.Divisor K F) (V : Submodule K F) [FiniteDimensional K ↥V]
    (hVD : V ≤ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, ∃ f ∈ V, f ≠ 0 ∧ w.ord f + D w = 0) :
    ∃ f₁ ∈ V, ∃ f₂ ∈ V, ∀ w : AlgebraicCurve.Place K F,
      (f₁ ≠ 0 ∧ w.ord f₁ + D w = 0) ∨ (f₂ ≠ 0 ∧ w.ord f₂ + D w = 0) := by
  classical
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨w₀⟩⟩
  · exact ⟨0, V.zero_mem, 0, V.zero_mem, fun w => (hE.false w).elim⟩
  obtain ⟨f₁, hf₁V, hf₁0, -⟩ := hbpf w₀

  obtain ⟨P, hP⟩ := HasPrincipalDivisors.exists_divisor (K := K) f₁ hf₁0
  let bad : Finset (Place K F) := (P.support ∪ D.support).filter fun w => w.ord f₁ + D w ≠ 0
  have hbad : ∀ w, w.ord f₁ + D w ≠ 0 → w ∈ bad := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨?_, hw⟩
    rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    by_contra h
    push Not at h
    apply hw
    rw [← hP.1 w, h.1, h.2, add_zero]

  let p : ↥bad → Submodule K ↥V := fun w =>
    (riemannRochSpace (D - Finsupp.single (w : Place K F) 1)).comap V.subtype
  have hp : ∀ w, p w ≠ ⊤ := by
    intro w htop
    obtain ⟨f, hfV, hf0, hford⟩ := hbpf w
    have hf : (⟨f, hfV⟩ : ↥V) ∈ p w := by rw [htop]; trivial
    have hf' := (mem_riemannRochSpace_iff.mp hf (w : Place K F)).resolve_left hf0
    rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hf'
    change -(D (w : Place K F) - 1) ≤ (w : Place K F).ord f at hf'
    linarith
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨f₁, hf₁V, (x : F), x.2, fun w => ?_⟩
  by_cases hw : w.ord f₁ + D w = 0
  · exact Or.inl ⟨hf₁0, hw⟩
  · right
    have hxw := hx ⟨w, hbad w hw⟩
    have hx0 : (x : F) ≠ 0 := by
      intro h0
      apply hxw
      show (V.subtype x) ∈ riemannRochSpace _
      rw [show V.subtype x = (x : F) from rfl, h0]
      exact Submodule.zero_mem _
    refine ⟨hx0, ?_⟩

    have hxD := (mem_riemannRochSpace_iff.mp (hVD x.2) w).resolve_left hx0
    by_contra hne
    apply hxw
    show (x : F) ∈ riemannRochSpace (D - Finsupp.single w 1)
    rw [mem_riemannRochSpace_iff]
    intro w'
    right
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with hww
    · subst hww; omega
    · rw [sub_zero]; exact (mem_riemannRochSpace_iff.mp (hVD x.2) w').resolve_left hx0

end S_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
end P2MW
export P2MW.S_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace (solution)
