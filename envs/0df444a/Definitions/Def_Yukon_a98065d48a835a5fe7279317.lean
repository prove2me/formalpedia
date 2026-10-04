-- Prove2me | Definitions.Def_Yukon_a98065d48a835a5fe7279317
-- name    : Yukon_a98065d48a835a5fe7279317
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:54:51.524979+00:00
-- url     : https://prove2.me/theorems/6a24c0eb-af06-4d82-83bf-e2ec7a4c505c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpaceSourceAlternative6814.lean
--
--   yukon-proof-operation:certificate-split-3370d7b11968f048616f823409af1eee3ddc4c5e442092c83cbeea7c81e968a7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZmRkYTI1MzMxN2JhNTljMjNhOGY1MzM5MmRmMmZmYTAyZmQ2OTNiNzhkZGE2Y2E4MzZmYjg0ZDhiMjUwMTgzZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTMzNzBkN2IxMTk2OGYwNDg2MTZmODIzNDA5YWYxZWVlM2RkYzRjNWU0NDIwOTJjODNjYmVlYTdjODFlOTY4YTciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hOTgwNjVkNDhhODM1YTVmZTcyNzkzMTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_3d5a9ed4cebf933826368088
















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Concrete 181255-agreement source alternative. The source is chosen
outside J^3 before taking the helper/retention alternative. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceKernel6814
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper
open SecondJetHelperWeights RCN234 RCN156

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]

def ProperHelper (F Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q ≤ 31+14*(r-1) ∧
    wt residualYSWeights Q ≤ 98+14*(y-1) ∧
    wt residualTotalWeights Q ≤ 1700+14*(t-1)) ∧
  ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181255 ≤ S.card → (∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) →
    RCN319.specialization K f z F=0 → RCN319.specialization K f z Q=0

theorem helper_or_retained
    (nodes : N ↪ K) (u0 u1 : N → K)
    (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) (hb : Bounds P)
    (hc : ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
      (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P))
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F)
    (hFT : 1700 < wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1 ≤ r) (hy : 1 ≤ y) (ht : 1 ≤ t)
    (hF : wt residualSWeights F ≤ r ∧ wt residualYSWeights F ≤ y ∧ wt residualTotalWeights F ≤ t) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      (3 ≤ (asS P).natDegree ∧ ∀ d ≤ 2, F ∣ helper P F (14-d) d) := by
  classical
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ 31 ∧
      e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700 :=
    fun e he => ⟨(hb e he).1,(hb e he).2.2.1,(hb e he).2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ 14 := fun e he => (hb e he).2.1
  have hdegree : (asS P).natDegree ≤ 14 := by
    simpa using asS_derivative_degree P 14 0 hS
  have hfact : ∀ d ≤ 14, (d.factorial : K) ≠ 0 := by
    intro d hd
    exact SecondJetOwnShape.factorial_ne (K := K) d (by omega)
  by_cases hn : (asS P).natDegree < 3
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP F 1700
      (fun e he => (hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw := derivative_coefficient_weights P 31 98 1700 0 n hflags
      simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
      change wt residualSWeights ((asS P).coeff n) ≤ 31+14*(r-1) ∧
        wt residualYSWeights ((asS P).coeff n) ≤ 98+14*(y-1) ∧
        wt residualTotalWeights ((asS P).coeff n) ≤ 1700+14*(t-1)
      omega
    · intro f hf z S hSc hvalues _
      have hv := source_derivative_vanish nodes u0 u1 P hb hc n (by dsimp [n]; omega)
        f hf z S hSc hvalues
      have htop := MovingFiberLeadingCoefficient6811.specialize_top P f z n
        (by intro j hj; rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero])
      rw [htop,nsmul_eq_mul] at hv
      change coefficientSpecialize f z ((asS P).coeff n)=0
      apply (mul_eq_zero.mp hv).resolve_left
      simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr (hfact n hdegree))
  · by_cases hdiv : ∀ d ≤ 2, F ∣ helper P F (14-d) d
    · exact Or.inr ⟨by omega,hdiv⟩
    · left
      push_neg at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (14-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F 31 98 1700 14 d t y r
          (by omega) (by omega) (by omega) (by omega) hr hy ht hflags hF
        have hrr := Nat.mul_le_mul_right (r-1) (Nat.sub_le 14 d)
        have hyy := Nat.mul_le_mul_right (y-1) (Nat.sub_le 14 d)
        have htt := Nat.mul_le_mul_right (t-1) (Nat.sub_le 14 d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact helper_vanish P F (14-d) d (asS_derivative_degree P 14 d hS) f z hFzero
          (source_derivative_vanish nodes u0 u1 P hb hc d hd f hf z S hSc hvalues)








end
end ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814


