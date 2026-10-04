-- Prove2me | Definitions.Def_Yukon_5f00e2c5310c2b2de34fe4e2
-- name    : Yukon_5f00e2c5310c2b2de34fe4e2
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:21:58.230231+00:00
-- url     : https://prove2.me/theorems/c7add2a0-bc75-4c28-9338-4b439a287610
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceZSupplier6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceZSupplier6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceZSupplier6814.lean
--
--   yukon-proof-operation:certificate-direct-imports-95fe7f581cee911a0dd229419601e23452b3a055989c60de692413ad22c4e093
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTE2NGY1ZTRiNGFjZGI3OWYyY2RkZjBhNDdkNWUxMTA4NGZiODA5MWQ0NjVjMTcyMjk1ZWVlZTI5NjMzYzUwMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWRpcmVjdC1pbXBvcnRzLTk1ZmU3ZjU4MWNlZTkxMWEwZGQyMjk0MTk2MDFlMjM0NTJiM2EwNTU5ODljNjBkZTY5MjQxM2FkMjJjNGUwOTMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81ZjAwZTJjNTMxMGMyYjJkZTM0ZmU0ZTIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_d87b28dfbb072e6a2718acca
















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The retained Z source is constructed at the new agreement threshold.
The low-degree arm includes degree seven (n0=8, k=6); it uses the stronger
low-block cutoff, not an unavailable seventh derivative-vanishing claim. -/
namespace ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedDifferentiation MovingSourceZCounts6814 MovingFiberThreeSources6811
open RCN234 RCN156

variable {K N : Type} [Field K] [Fintype N]

def Bounds (P : Poly (K:=K)) : Prop := ∀ e ∈ P.support,
  2*e 1+e 3≤53 ∧ e 1≤24 ∧ e 1+e 2+e 3≤177 ∧ e 1+e 2+e 3+e 4≤3429 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1<cutoff (e 1)

def Interpolant (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K)) : Prop :=
  P≠0 ∧ Bounds P ∧ ∀ i, MvPolynomial.X 0^130 ∣ SecondJetDifferentiation.substitute (K:=K)
    (localize (nodes i) (u0 i) (u1 i) P)

theorem exists_interpolant (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144) :
    ∃ P, Interpolant nodes u0 u1 P := by
  have hcard : Fintype.card N*SecondJetRelaxedGlobalMap.rankBound 130 3429 53 24 177
      (fun h => (cutoff h+53-1)/131071)<
      Fintype.card (SecondJetRelaxedGlobalIndex.Index cutoff 131071 3429 53 24 177) := by
    rw [hN,source_rank,source_card]
    norm_num
  obtain ⟨P,hP,hbounds,hcontact⟩ := SecondJetRelaxedGlobalIndex.exists_weighted_global_contact
    cutoff 131071 3429 53 24 177 130 (by omega) (by omega) nodes u0 u1 hcard
  exact ⟨P,hP,hbounds,fun i => SecondJetGlobalDifferentiation.nested_to_flat_contact _ 130 (hcontact i)⟩

theorem derivative_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (d : ℕ) (hd : d≤6) (f : Polynomial K) (hf : f.natDegree≤131071)
    (z : K) (S : Finset N) (hS : 181255≤S.card)
    (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) :
    specialize f z ((pderiv 1)^[d] P)=0 := by
  apply SecondJetRelaxedDifferentiation.derivative_vanish P 130 181255 131071 6 8 d
    (by omega) (by omega) (by omega) hd ?_ nodes u0 u1 hP.2.2 f hf z S hS hvalues
  intro e he
  have hh := (hP.2.1 e he).2.2.2.2
  dsimp [cutoff] at hh
  norm_num
  omega

theorem low_coefficient_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (d : ℕ) (hd : d<8) (hfact : (d.factorial : K)≠0)
    (f : Polynomial K) (hf : f.natDegree≤131071) (z : K) (S : Finset N)
    (hS : 181255≤S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z)
    (hh : ∀ j, d<j → coefficientSpecialize f z ((asS P).coeff j)=0) :
    coefficientSpecialize f z ((asS P).coeff d)=0 := by
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(130-d)*181255 := by
    intro e he
    have hb := (hP.2.1 _ (coefficient_support P d e he)).2.2.2.2
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [cutoff,reserve,if_pos hd] at hb
    omega
  have hdeg := MovingFiberLeadingCoefficient6811.coefficient_degree ((asS P).coeff d)
    f z 131071 ((130-d)*181255) hf (by omega) hweight
  have htop := MovingFiberLeadingCoefficient6811.specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P)=0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (130-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (show d≤130 by omega)] using hP.2.2 i
    · rw [htop]
      exact ((Polynomial.natDegree_smul_le d.factorial _).trans_lt hdeg).trans_le
        (Nat.mul_le_mul_left (130-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (by
    simpa only [map_natCast] using Polynomial.C_ne_zero.mpr hfact)

def ProperHelper (F Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q≤53+24*(r-1) ∧ wt residualYSWeights Q≤177+24*(y-1) ∧
    wt residualTotalWeights Q≤3429+24*(t-1)) ∧
  ∀ f : Polynomial K, f.natDegree≤131071 → ∀ z : K, ∀ S : Finset N,
    181255≤S.card → (∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) →
      RCN319.specialization K f z F=0 → RCN319.specialization K f z Q=0

theorem helper_or_retained [CharP K 2130706433]
    (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F) (hFT : 3429<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      (8≤(asS P).natDegree ∧ ∀ d≤6, F∣helper P F (24-d) d) := by
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3≤53 ∧ e 1+e 2+e 3≤177 ∧ e 1+e 2+e 3+e 4≤3429 :=
    fun e he => ⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1≤24 := fun e he => (hP.2.1 e he).2.1
  have hdegree : (asS P).natDegree≤24 := by simpa using asS_derivative_degree P 24 0 hS
  by_cases hn : (asS P).natDegree<8
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP.1 F 3429
      (fun e he => (hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw := derivative_coefficient_weights P 53 177 3429 0 n hflags
      simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
      change wt residualSWeights ((asS P).coeff n)≤53+24*(r-1) ∧
        wt residualYSWeights ((asS P).coeff n)≤177+24*(y-1) ∧
        wt residualTotalWeights ((asS P).coeff n)≤3429+24*(t-1)
      omega
    · intro f hf z S hSc hvalues _
      apply low_coefficient_vanish nodes u0 u1 P hP n hn
        (SecondJetOwnShape.factorial_ne n (by dsimp [n]; omega)) f hf z S hSc hvalues
      intro j hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]
  · by_cases hdiv : ∀ d≤6, F∣helper P F (24-d) d
    · exact Or.inr ⟨by omega,hdiv⟩
    · left
      push_neg at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (24-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F 53 177 3429 24 d t y r
          (by omega) (by omega) (by omega) (by omega) hr hy ht hflags hF
        have hrr := Nat.mul_le_mul_right (r-1) (Nat.sub_le 24 d)
        have hyy := Nat.mul_le_mul_right (y-1) (Nat.sub_le 24 d)
        have htt := Nat.mul_le_mul_right (t-1) (Nat.sub_le 24 d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact helper_vanish P F (24-d) d (asS_derivative_degree P 24 d hS) f z hFzero
          (derivative_vanish nodes u0 u1 P hP d hd f hf z S hSc hvalues)

theorem exists_helper_or_z_source [CharP K 2130706433]
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F) (hFT : 3429<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ S : Source F, S.d=7 ∧ S.flag=⟨3252,132,51⟩ ∧ S.k=6 := by
  obtain ⟨P,hP⟩ := exists_interpolant nodes u0 u1 hN
  rcases helper_or_retained nodes u0 u1 P hP F hFi hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  right
  let S : Source F := {
    P := P
    B := 53
    U := 177
    T := 3429
    s := 24
    k := 6
    n0 := 8
    hS := fun e he => (hP.2.1 e he).2.1
    hshape := fun e he => ⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
    hBU := by omega
    hUT := by omega
    hdn := by omega
    hB := by omega
    hn := hret.1
    hdiv := hret.2 }
  exact ⟨S,rfl,by norm_num [S,Source.flag,Source.d,SecondJetRelaxedFlag.budgetFlag],rfl⟩





end
end ProximityPrize.SubmissionLower.MovingSourceZSupplier6814


