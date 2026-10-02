-- Prove2me | Definitions.Def_Yukon_a957bc9c4724c6765d4efdf5
-- name    : Yukon_a957bc9c4724c6765d4efdf5
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:03:10.257745+00:00
-- url     : https://prove2.me/theorems/bb6a25a7-760c-47ba-9a7c-0fb706d97b12
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WeightedSliceAssignment6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WeightedSliceAssignment6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WeightedSliceAssignment6807.lean
--
--   yukon-proof-operation:foundation-direct-214e2cfcfd22c1b66431834604e1aa4725ffb4c2872831c90387341bd541e204
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmVhMTY2NmNhZGU1NDg1MjNlMjU4Nzc1MTBlN2E5YjFlMDBkNjU2ZjMzYWU1NjBkMTE1OWFmY2M5MDYyMjE1MiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTIxNGUyY2ZjZmQyMmMxYjY2NDMxODM0NjA0ZTFhYTQ3MjVmZmI0YzI4NzI4MzFjOTAzODczNDFiZDU0MWUyMDQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hOTU3YmM5YzQ3MjRjNjc2NWQ0ZWZkZjUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_889970ac05654d96eb829360

/-
UNCOMPILED. Choose one actual factor/component for each embedded point.
This supplies a disjoint weighted partition, including points lying on more
than one component, rather than counting an overlapping cover as a partition.
-/













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.WeightedSliceAssignment6807
open scoped Classical BigOperators
open RCN002 RCN007 RCN072 RCN084 RCN095 RCN134 RCN264
noncomputable section
set_option autoImplicit false
local instance  _root_.ProximityPrize.SubmissionLower.WeightedSliceAssignment6807.instDecidableEq_proximityPrize {A : Type*} : DecidableEq A := Classical.decEq A
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {E I : Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" => MvPolynomial (Fin 3) E

abbrev SliceComponent (F N R : Poly) :=
  (g : ↥(activeFactors F N)) × RegularComponent E g.1 N R

theorem exists_point_assignment (F N R : Poly) (point : I → Fin 3 → E)
    (hcover : ∀ i, ∃ g : ↥(activeFactors F N), MvPolynomial.eval (point i) g.1 = 0)
    (hN : ∀ i, MvPolynomial.eval (point i) N = 0)
    (hR : ∀ i, MvPolynomial.eval (point i) R ≠ 0) :
    ∃ assign : I → SliceComponent F N R,
      ∀ i, (assign i).2.1 ≤ RingHom.ker
        (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom := by
  classical
  have he (i : I) : ∃ a : SliceComponent F N R,
      a.2.1 ≤ RingHom.ker (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom := by
    obtain ⟨g, hg⟩ := hcover i
    obtain ⟨C, hC⟩ := exists_regular_component E g.1 N R (point i) hg (hN i) (hR i)
    exact ⟨⟨g,C⟩,hC⟩
  exact ⟨fun i => (he i).choose, fun i => (he i).choose_spec⟩

omit [Field E] [IsAlgClosed E] in
/-- Exact weighted regrouping, valid for any finite target type. -/
theorem weighted_assignment_sum {A : Type*} [Fintype A] [DecidableEq A]
    (assign : I → A) (mu : I → ℕ) :
    (∑ a, ∑ i with assign i = a, mu i) = ∑ i, mu i := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := assign) (fun _ _ => Finset.mem_univ _) _

omit [Field E] [IsAlgClosed E] in
/-- Local bounds can be summed without multiplying a point's weight by the
number of components through it. The local hypothesis is still visible. -/
theorem sum_local_slice_bounds {A : Type*} [Fintype A] [DecidableEq A]
    (assign : I → A) (mu : I → ℕ) (cost : A → ℕ) (d : ℕ)
    (hlocal : ∀ a, d * (∑ i with assign i = a, mu i) ≤ cost a) :
    d * (∑ i, mu i) ≤ ∑ a, cost a := by
  rw [← weighted_assignment_sum assign mu, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hlocal a)

/-- The old first-tail polynomial is nonzero on every assigned slice component
through an embedding point, by the k=0 isolation certificate. -/
theorem first_tail_not_mem_assigned (F N A R : Poly)
    (point : I → Fin 3 → E) (assign : I → SliceComponent F N R)
    (hpoint : ∀ i, (assign i).2.1 ≤ RingHom.ker
      (MvPolynomial.aeval (point i) : Poly →ₐ[E] E).toRingHom)
    (hisolated : ∀ i, IsolatedPoint F N A (point i)) (i : I) :
    A ∉ (assign i).2.1 := by
  let g := (assign i).1
  let C := (assign i).2
  exact hisolated i C.1 inferInstance (regularComponent_ne_point E g.1 N R C)
    (hpoint i)
    (C.1.mem_of_dvd (activeFactors_spec F N g).2.1
      (regularComponent_G_mem E g.1 N R C))
    (regularComponent_T_mem E g.1 N R C)

end
end ProximityPrize.SubmissionLower.WeightedSliceAssignment6807


