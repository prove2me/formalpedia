-- Prove2me | solution 1 for Auto.sum_triple_by_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:10.418485+00:00
-- url     : https://prove2.me/submissions/0f7d20ff-4142-4e24-a24c-b5ce5c23b3fc

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
theorem _root_.solution {κ : Type*} [LinearOrder κ] {M : Type*} [AddCommMonoid M]
    (f : κ → κ → κ → M) (hf : ∀ i j k, f i j k = f j k i) (s : Finset κ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k = ∑ μ ∈ s, (3 • ∑ j ∈ s.filter (μ < ·), ∑ k ∈ s.filter (μ
      < ·), f μ j k + 3 • ∑ k ∈ s.filter (μ < ·), f μ μ k + f μ μ μ) := by
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
    have hR : ∑ μ ∈ insert a t, (3 • ∑ j ∈ (insert a t).filter (μ < ·),
        ∑ k ∈ (insert a t).filter (μ < ·), f μ j k +
        3 • ∑ k ∈ (insert a t).filter (μ < ·), f μ μ k + f μ μ μ) =
        (3 • ∑ j ∈ t, ∑ k ∈ t, f a j k + 3 • ∑ k ∈ t, f a a k + f a a a) +
        ∑ μ ∈ t, (3 • ∑ j ∈ t.filter (μ < ·), ∑ k ∈ t.filter (μ < ·), f μ j k +
          3 • ∑ k ∈ t.filter (μ < ·), f μ μ k + f μ μ μ) := by
      rw [Finset.sum_insert hat, hfa]
      congr 1
      exact Finset.sum_congr rfl fun μ hμ => by rw [hfμ μ hμ]
    rw [hR, ← ih]
    have c1 : ∀ k, f k a a = f a a k := fun k => by rw [hf, hf]
    have c2 : ∀ k, f a k a = f a a k := fun k => by rw [← hf]
    have c3 : ∀ j k, f j a k = f a k j := fun j k => hf j a k
    have c4 : ∀ j k, f j k a = f a j k := fun j k => by rw [hf, hf]
    have e1 : ∑ j ∈ t, f a j a = ∑ k ∈ t, f a a k := Finset.sum_congr rfl fun j _ => c2 j
    have e2 : ∑ i ∈ t, f i a a = ∑ k ∈ t, f a a k := Finset.sum_congr rfl fun i _ => c1 i
    have e3 : ∑ i ∈ t, ∑ k ∈ t, f i a k = ∑ j ∈ t, ∑ k ∈ t, f a j k := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => c3 i k
    have e4 : ∑ i ∈ t, ∑ j ∈ t, f i j a = ∑ j ∈ t, ∑ k ∈ t, f a j k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => c4 i j
    simp only [Finset.sum_insert hat, Finset.sum_add_distrib]
    rw [e1, e2, e3, e4]
    simp only [succ_nsmul, zero_nsmul, zero_add]
    abel
end Auto
