-- Prove2me | Definitions.Def_Yukon_b18ab9084e250f4b6a2f2e45
-- name    : Yukon_b18ab9084e250f4b6a2f2e45
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:13:51.805258+00:00
-- url     : https://prove2.me/theorems/c173348d-eb72-427a-8a13-d833071f201c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberInterpolation6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberInterpolation6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberInterpolation6811.lean
--
--   yukon-proof-operation:foundation-direct-7f621bcfa4cd918a6185035c4f901f396d3db8507a361db683ace30f782a39e2
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODYxYzUyOTdiODQxOWU5ZGU1YTZjNWYxZjI5MDliNGI2ZDBiYWMzNGMzMmRkNjJlZDM0NTllOTMwNWEzNzZiNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTdmNjIxYmNmYTRjZDkxOGE2MTg1MDM1YzRmOTAxZjM5NmQzZGI4NTA3YTM2MWRiNjgzYWNlMzBmNzgyYTM5ZTIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iMThhYjkwODRlMjUwZjRiNmEyZjJlNDUiLCJ2IjoyfQ]

/- Private higher-target research: actual interpolation sources only. -/
import Definitions.Def_Yukon_63a16e90b7724a1f71186e13








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberInterpolation6811
open SecondJetDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

def cutoff (m k n0 h : ℕ) : ℕ := m*181265-SecondJetRelaxedDifferentiation.reserve k n0 h*50196

def Interpolant (m B s U L k n0 : ℕ) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K := K)) : Prop :=
  P ≠ 0 ∧
  (∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧
    e 1+e 2+e 3+e 4 ≤ L ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff m k n0 (e 1)) ∧
  (∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
    (localize (nodes i) (u0 i) (u1 i) P)) ∧
  ∀ d ≤ k, ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181265 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
      specialize f z ((pderiv 1)^[d] P) = 0

theorem exists_of_dimension (m B s U L k n0 : ℕ) (hsB : 2*s ≤ B) (hkm : k < m)
    (hN : Fintype.card N = 262144) (nodes : N ↪ K) (u0 u1 : N → K)
    (hcard : 262144*SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h => (cutoff m k n0 h+B-1)/131071) <
      Fintype.card (SecondJetRelaxedGlobalIndex.Index (cutoff m k n0) 131071 L B s U)) :
    ∃ P, Interpolant m B s U L k n0 nodes u0 u1 P := by
  obtain ⟨P,hP,hbounds,hcontact⟩ := SecondJetRelaxedGlobalIndex.exists_weighted_global_contact
    (cutoff m k n0) 131071 L B s U m hsB (by decide) nodes u0 u1 (by simpa only [hN] using hcard)
  have hc : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P) := fun i =>
    SecondJetGlobalDifferentiation.nested_to_flat_contact _ m (hcontact i)
  refine ⟨P,hP,hbounds,hc,?_⟩
  intro d hd f hf z S hS hvalues
  apply derivative_vanish P m 181265 131071 k n0 d (by decide) (by decide)
    (by omega) hd ?_ nodes u0 u1 hc f hf z S hS hvalues
  intro e he
  have hb := (hbounds e he).2.2.2.2
  dsimp [cutoff] at hb
  norm_num
  omega


end
end ProximityPrize.SubmissionLower.MovingFiberInterpolation6811


