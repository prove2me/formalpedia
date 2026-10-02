-- Prove2me | Definitions.Def_Yukon_2e408f73c84aa0b97341dc8e
-- name    : Yukon_2e408f73c84aa0b97341dc8e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:10:52.387368+00:00
-- url     : https://prove2.me/theorems/41e7ebe0-1227-4b25-8897-bb65b5381182
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeProfileSupplier.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeProfileSupplier.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeProfileSupplier.lean
--
--   yukon-proof-operation:foundation-direct-3c97b347e99d7a3d765bf30adebb5121a043c51b0aa5f55e8beef667b1337e43
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTE4YTFkMWNjYWRiOGVlYTMyZmZjNTg3ODU1MzgwMTA0MTFlOGQ1YzkyOGMwOTRjYTE1ODc5ZWQ1M2YxNjA4MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTNjOTdiMzQ3ZTk5ZDdhM2Q3NjViZjMwYWRlYmI1MTIxYTA0M2M1MWIwYWE1ZjU1ZThiZWVmNjY3YjEzMzdlNDMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yZTQwOGY3M2M4NGFhMGI5NzM0MWRjOGUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_3643feade21abaae244d4f5e













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeBounded6814.instDecidableEq_proximityPrize_1 : DecidableEq K := Classical.decEq K

def profileRowRank (alpha beta L s T R mu : ℕ) : ℕ :=
  localRankBound (alpha-beta*(mu-1)) L s-
    localRankBound (alpha-beta*(mu-1)-mu) (L-T) (s-R)

/-- A finite envelope of scalar contact rows bounds the actual node sum.
The contact cap is derived from irreducibility, not assumed for the nodes. -/
theorem profile_dimension_test
    {I : Type*} [Fintype I] {DF T R B D w L s nu : ℕ}
    (F : Poly4 K) (hF : Irreducible F) (hR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R)
    (hB : wt RCN156.residualYSWeights F ≤ B)
    (nodes u0 u1 : I → K) (alpha beta : ℕ)
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      Fintype.card I*profileRowRank alpha beta L s T R mu < coefficientCount D w L s) :
    coefficientCount (D-nu) w (L-T) (s-R) +
      (∑ i : I, profileRowRank alpha beta L s T R
        (contactOrder K (nodes i) (u0 i) (u1 i) F)) < coefficientCount D w L s := by
  classical
  let rows := Finset.range (B+R+1)
  have hn : rows.Nonempty := ⟨0,by simp [rows]⟩
  obtain ⟨mu,hmu,heq⟩ := Finset.exists_mem_eq_sup rows hn (profileRowRank alpha beta L s T R)
  have hbound (i : I) : profileRowRank alpha beta L s T R
      (contactOrder K (nodes i) (u0 i) (u1 i) F) ≤
        rows.sup (profileRowRank alpha beta L s T R) := by
    apply Finset.le_sup
    have hc := contactOrder_le_middle_add_slope K F hF hR hbox hB (nodes i) (u0 i) (u1 i)
    simpa [rows] using (show contactOrder K (nodes i) (u0 i) (u1 i) F < B+R+1 by omega)
  have hs : (∑ i : I, profileRowRank alpha beta L s T R
      (contactOrder K (nodes i) (u0 i) (u1 i) F)) ≤
        Fintype.card I*rows.sup (profileRowRank alpha beta L s T R) := by
    calc
      _ ≤ ∑ _i : I, rows.sup (profileRowRank alpha beta L s T R) :=
        Finset.sum_le_sum fun i _ => hbound i
      _ = _ := by simp
  have hc := hrows mu (by have := Finset.mem_range.mp hmu; omega)
  rw [heq] at hs
  exact (Nat.add_le_add_left hs _).trans_lt hc

/-- The profile-facing proper-helper theorem: exactly the finite row
inequalities and clipped cutoff used by the saved arithmetic checks. -/
theorem exists_profile_helper
    {I : Type*} [Fintype I] [DecidableEq I] {DF T R B D w L s nu : ℕ}
    (F : Poly4 K) (hF : Irreducible F) (hRpos : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K DF 1 T R) (hT : T ≤ L) (hR : R ≤ s)
    (hcode : wt (RCN081.contactWeights w) F = nu)
    (htotal : T ≤ wt RCN156.residualTotalWeights F)
    (hslope : R ≤ wt RCN156.residualSWeights F)
    (hB : wt RCN156.residualYSWeights F ≤ B)
    (nodes : I ↪ K) (u0 u1 : I → K) (alpha beta A : ℕ) (hnu : w ≤ nu)
    (hDpos : 0 < D) (hD : D ≤ alpha*A-beta*min (nu-w+1) ((B+R-1)*A))
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      Fintype.card I*profileRowRank alpha beta L s T R mu < coefficientCount D w L s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagreement : ∀ gamma ∈ Gamma, A ≤
      ((Finset.univ : Finset I).filter
        (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card) :
    ∃ Q : Poly4 K, Q ∈ globalCoefficientBox K D w L s ∧ IsRelPrime F Q ∧
      ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0 := by
  classical
  let m : I → ℕ := fun i => alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)
  have hd := profile_dimension_test K F hF hRpos hbox hB nodes u0 u1 alpha beta hrows
  obtain ⟨Q,hQ,hproper,hcontact⟩ := exists_proper_relative_helper K F hF.ne_zero hbox hT hR
    hcode.symm.le htotal hslope nodes u0 u1 m hd
  refine ⟨Q,hQ,hF.isRelPrime_iff_not_dvd.mpr hproper,?_⟩
  intro gamma hgamma
  let support := (Finset.univ : Finset I).filter
    (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)
  have hv : ∀ i ∈ support, (selected gamma).eval (nodes i) = u0 i+gamma*u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmass := regular_clipped_order_mass K F hF hRpos hbox hB (selected gamma) gamma
    nodes u0 u1 support w nu alpha beta A hnu (hdegree gamma hgamma) hcode.le
    (hregular gamma hgamma) hv (hagreement gamma hgamma)
  apply relative_contact_specialization_eq_zero K F Q (selected gamma) gamma nodes u0 u1 support m
    (hsolution gamma hgamma) hv (fun i _ => hcontact i)
  exact (specialization_natDegree_lt K D w L s Q (selected gamma) gamma hDpos hQ
    (hdegree gamma hgamma)).trans_le (hD.trans hmass)

end
end ProximityPrize.SubmissionLower.RelativeBounded6814


