-- Prove2me | solution 1 for Auto.sum_pair_by_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:21.335947+00:00
-- url     : https://prove2.me/submissions/08870f07-abf6-44dc-bae8-5542713a5d1a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
namespace Auto
theorem _root_.solution {κ : Type*} [LinearOrder κ] {M : Type*} [AddCommMonoid M] (g : κ → κ → M)
    (s : Finset κ) :
    ∑ i ∈ s, ∑ j ∈ s, g i j = ∑ μ ∈ s, (g μ μ + ∑ j ∈ s.filter (μ < ·), (g μ j + g j μ)) := by
  classical
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a t ha ih =>
    have hat : a ∉ t := fun h => lt_irrefl a (ha a h)
    have hfa : (insert a t).filter (a < ·) = t := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, ha x hx⟩
    have hfμ : ∀ μ ∈ t, (insert a t).filter (μ < ·) = t.filter (μ < ·) := by
      intro μ hμ
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd (ha μ hμ) (not_lt.2 h.le)
        · exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩; exact ⟨Or.inr hx, h⟩
    have hR : ∑ μ ∈ insert a t, (g μ μ + ∑ j ∈ (insert a t).filter (μ < ·), (g μ j + g j μ)) = (g a
        a + ∑ j ∈ t, (g a j + g j a)) +
        ∑ μ ∈ t, (g μ μ + ∑ j ∈ t.filter (μ < ·), (g μ j + g j μ)) := by
      rw [Finset.sum_insert hat, hfa]
      congr 1
      exact Finset.sum_congr rfl fun μ hμ => by rw [hfμ μ hμ]
    rw [hR, ← ih]
    simp only [Finset.sum_insert hat, Finset.sum_add_distrib]
    abel
end Auto
