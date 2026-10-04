-- Prove2me | Definitions.Def_Yukon_8b73aecc71f3e1b6f34fc101
-- name    : Yukon_8b73aecc71f3e1b6f34fc101
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T07:58:07.066829+00:00
-- url     : https://prove2.me/theorems/ed63338c-d769-4b56-81dd-9887f3b7b432
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceTwoProfiles6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-902ecc3d0d8ace7ec023410529a2b4970890392b760f5a57c5d4ecc5c5fea9a7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTQ0ZjBjODlhODMxMDBiOWUzNjI4YzUzM2E3MGJmM2U5OTJjYTk1Y2IxM2I2ZWRiMzZlMGI2ZjM4NmRlYmFjMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtOTAyZWNjM2QwZDhhY2U3ZWMwMjM0MTA1MjlhMmI0OTcwODkwMzkyYjc2MGY1YTU3YzVkNGVjYzVjNWZlYTlhNyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzhiNzNhZWNjNzFmM2UxYjZmMzRmYzEwMSIsInYiOjJ9]

import Definitions.Def_Yukon_4f169e935332851cf48361a5





















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Construct the two actual retained profiles used by the unique-owner
envelope, at 181255 agreements. Proper-helper exits are explicit. -/
namespace ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceSourceCounts6814 WholeSpaceSourceKernel6814
open MovingFiberThreeSources6811 MovingSourceCarrierField6814
open RCN234 RCN156

theorem small_dimension :
    262144*SecondJetRelaxedCounts.rankBound 72 995 31 14 98<
      SecondJetRelaxedGlobalCounts.coefficientCount cutoff 131071 995 31 14 98 := by
  decide +kernel

variable {K N : Type} [Field K] [Fintype N]

theorem exists_small_polynomial (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144) :
    ∃ P : WholeSpaceCube6814.Poly (K:=K), P≠0 ∧
      (∀ e ∈ P.support, 2*e 1+e 3≤31 ∧ e 1≤14 ∧ e 1+e 2+e 3≤98 ∧ e 1+e 2+e 3+e 4≤995 ∧
        e 0+131071*e 2+131070*e 3+131069*e 1<cutoff (e 1)) ∧
      ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K:=K)
        (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P) := by
  have hcard : Fintype.card N*SecondJetRelaxedGlobalMap.rankBound 72 995 31 14 98
      (fun h => (cutoff h+31-1)/131071)<
      Fintype.card (SecondJetRelaxedGlobalIndex.Index cutoff 131071 995 31 14 98) := by
    rw [hN,SecondJetRelaxedCounts.rankBound_eq_closed 72 995 31 14 98 _
      (by omega) (by omega) (by omega) (by omega) middle_cap,
      SecondJetRelaxedGlobalCounts.card_index_closed cutoff 131071 995 31 14 98 (by omega)]
    exact small_dimension
  obtain ⟨P,hP,hb,hc⟩ := SecondJetRelaxedGlobalIndex.exists_weighted_global_contact
    cutoff 131071 995 31 14 98 72 (by omega) (by omega) nodes u0 u1 hcard
  exact ⟨P,hP,hb,fun i => SecondJetGlobalDifferentiation.nested_to_flat_contact _ 72 (hc i)⟩

def Profile {F : MvPolynomial (Fin 4) K} (S : Source F) (B U T s k n0 : ℕ) : Prop :=
  S.B=B ∧ S.U=U ∧ S.T=T ∧ S.s=s ∧ S.k=k ∧ S.n0=n0

theorem helpers_or_two_profiles [CharP K 2130706433]
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F) (hFT : 3429<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, WholeSpaceSourceAlternative6814.ProperHelper F Q r y t nodes u0 u1) ∨
    (∃ Q, MovingSourceZSupplier6814.ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ S : Source F, ∃ Sz : Source F, Profile S 31 98 995 14 2 3 ∧ Profile Sz 53 177 3429 24 6 8 := by
  obtain ⟨P,hP,hbounds,hcontact⟩ := exists_small_polynomial nodes u0 u1 hN
  have hwide : Bounds P := by
    intro e he
    have hh := hbounds e he
    exact ⟨hh.1,hh.2.1,hh.2.2.1,by omega,hh.2.2.2.2⟩
  rcases WholeSpaceSourceAlternative6814.helper_or_retained nodes u0 u1 P hP hwide hcontact
    F hFi (by omega) r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  obtain ⟨Q,hQ⟩ := MovingSourceZSupplier6814.exists_interpolant nodes u0 u1 hN
  rcases MovingSourceZSupplier6814.helper_or_retained nodes u0 u1 Q hQ F hFi hFT
    r y t hr hy ht hF with hhelp | hz
  · exact Or.inr (Or.inl hhelp)
  let S : Source F := {
    P := P, B := 31, U := 98, T := 995, s := 14, k := 2, n0 := 3
    hS := fun e he => (hbounds e he).2.1
    hshape := fun e he => ⟨(hbounds e he).1,(hbounds e he).2.2.1,(hbounds e he).2.2.2.1⟩
    hBU := by omega
    hUT := by omega
    hdn := by omega
    hB := by omega
    hn := hret.1
    hdiv := hret.2 }
  let Sz : Source F := {
    P := Q, B := 53, U := 177, T := 3429, s := 24, k := 6, n0 := 8
    hS := fun e he => (hQ.2.1 e he).2.1
    hshape := fun e he => ⟨(hQ.2.1 e he).1,(hQ.2.1 e he).2.2.1,(hQ.2.1 e he).2.2.2.1⟩
    hBU := by omega
    hUT := by omega
    hdn := by omega
    hB := by omega
    hn := hz.1
    hdiv := hz.2 }
  exact Or.inr (Or.inr ⟨S,Sz,by repeat' constructor,by repeat' constructor⟩)

theorem source_nonzero (F : MvPolynomial (Fin 4) K) (S : Source F) : S.P≠0 := by
  intro hz
  have hh := S.hn
  rw [hz,map_zero,Polynomial.natDegree_zero] at hh
  have hd := S.hdn
  omega

theorem canonical_source_power [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (S : Source F)
    (hT : S.T<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hk : S.k<2130706433) :
    (asS S.P).map (carrierMap F)≠0 ∧
      (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^S.d ∣
        (asS S.P).map (carrierMap F) := by
  have hn := carrier_polynomial_nonzero F S.P (source_nonzero F S) S.T
    (fun e he => (S.hshape e he).2.2) hT
  exact ⟨hn,SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd S.P F (carrierMap F)
    S.s S.k S.hS (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hn
    (SecondJetOwnShape.factorial_ne S.k hk) S.hdiv⟩





end
end ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814


