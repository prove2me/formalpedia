-- Prove2me | Definitions.Def_Yukon_3643feade21abaae244d4f5e
-- name    : Yukon_3643feade21abaae244d4f5e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:57:39.188917+00:00
-- url     : https://prove2.me/theorems/08477f51-2466-4536-adc8-9dad78624fb8
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeClippedOrders.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeClippedOrders.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeClippedOrders.lean
--
--   yukon-proof-operation:foundation-direct-321de4e2e3021456e30c38e88523102f3419bfad2c5eae5db19daed23db1e895
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODhhZWRmMmM1NGVhYmYyOTAzZTk1Njg0NTdiMDM5OGIwMWNlMjM2YTcyNTM1MzA2NzQ0NGVjMWVhZGUwNzIyYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTMyMWRlNGUyZTMwMjE0NTZlMzBjMzhlODg1MjMxMDJmMzQxOWJmYWQyYzVlYWU1ZGIxOWRhZWQyM2RiMWU4OTUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zNjQzZmVhZGUyMWFiYWFlMjQ0ZDRmNWUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9113295e0811404ee8840e2e











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

theorem clipped_affine_order_mass {I : Type*} (support : Finset I) (d : I → ℕ)
    (alpha beta A H cap : ℕ) (hcard : A ≤ support.card)
    (hmass : (∑ i ∈ support, d i) ≤ H) (hcap : ∀ i ∈ support, d i ≤ cap) :
    alpha*A-beta*min H (cap*A) ≤ ∑ i ∈ support, (alpha-beta*d i) := by
  classical
  by_cases hh : H ≤ cap*A
  · rw [Nat.min_eq_left hh]
    exact affine_order_mass support d alpha beta A H hcard hmass
  · rw [Nat.min_eq_right (by omega : cap*A ≤ H)]
    calc
      alpha*A-beta*(cap*A) = (alpha-beta*cap)*A := by rw [Nat.sub_mul,Nat.mul_assoc]
      _ ≤ (alpha-beta*cap)*support.card := Nat.mul_le_mul_left _ hcard
      _ = ∑ _i ∈ support, (alpha-beta*cap) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        Nat.sub_le_sub_left (Nat.mul_le_mul_left beta (hcap i hi)) alpha

/-- The clipped cutoff used by the existing certificates is justified on
the full agreement set. Its upper-weight tail uses the proved contact cap. -/
theorem regular_clipped_order_mass
    {I : Type*} {DF T R B : ℕ} (F : Poly4 K) (hF : Irreducible F)
    (hR : 0 < F.degreeOf 2) (hbox : F ∈ globalCoefficientBox K DF 1 T R)
    (hB : RCN234.wt RCN156.residualYSWeights F ≤ B)
    (f : Polynomial K) (gamma : K) (nodes : I ↪ K) (u0 u1 : I → K)
    (support : Finset I) (w nu alpha beta A : ℕ)
    (hnu : w ≤ nu) (hdegree : f.natDegree ≤ w)
    (hweight : MvPolynomial.weightedTotalDegree (RCN081.contactWeights w) F ≤ nu)
    (hregular : specialization K f gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i+gamma*u1 i)
    (hcard : A ≤ support.card) :
    alpha*A-beta*min (nu-w+1) ((B+R-1)*A) ≤
      ∑ i ∈ support, (alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)) := by
  have hm := regular_contact_mass K F hF.ne_zero f gamma nodes u0 u1 support w nu
    hdegree hweight hregular hagrees
  apply clipped_affine_order_mass support _ alpha beta A (nu-w+1) (B+R-1) hcard
  · omega
  · intro i _
    exact Nat.sub_le_sub_right
      (contactOrder_le_middle_add_slope K F hF hR hbox hB (nodes i) (u0 i) (u1 i)) 1

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


