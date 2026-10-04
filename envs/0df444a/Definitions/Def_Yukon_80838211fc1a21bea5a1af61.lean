-- Prove2me | Definitions.Def_Yukon_80838211fc1a21bea5a1af61
-- name    : Yukon_80838211fc1a21bea5a1af61
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T21:02:50.53469+00:00
-- url     : https://prove2.me/theorems/0e7975f9-36e9-4a70-a22d-f4ae65653163
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.CofactorOwnership6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.CofactorOwnership6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/CofactorOwnership6814.lean
--
--   yukon-proof-operation:certificate-split-35db1b70714d13a8f094dabb984f69ebc624d953a73a33b98b97f6ea322e40b7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzZjYjE4N2Q4YzIwYmIwZjUzNDkyNzRmNGFjYzg1NTljZmJkOGQwNDRlM2FiM2JiYjYzZmYyMzFiYjM3M2EwMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTM1ZGIxYjcwNzE0ZDEzYThmMDk0ZGFiYjk4NGY2OWViYzYyNGQ5NTNhNzNhMzNiOThiOTdmNmVhMzIyZTQwYjciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84MDgzODIxMWZjMWEyMWJlYTVhMWFmNjEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_3c19b1443a389ff3be7252a3










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Exact multiplicity split used by the cofactor audit. The factorization
is finite and nonzero, and the cofactor is explicitly nonvanishing at the
chosen root. The conclusion is not a desired geometric counting bound. -/
namespace ProximityPrize.SubmissionLower.CofactorOwnership6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial UniqueCurvatureOwner6814

variable {ι E : Type*} [Field E]
local instance  _root_.ProximityPrize.SubmissionLower.CofactorOwnership6814.instDecidableEq_proximityPrize : DecidableEq ι := Classical.decEq ι

def owningCopies (s : Finset ι) (e m : ι → ℕ) : ℕ :=
  ∑ i ∈ s, if 0 < m i then e i else 0

theorem owner_copy_split (s : Finset ι) (e m : ι → ℕ)
    (hpos : 0 < ∑ i ∈ s, e i*m i) :
    2 ≤ owningCopies s e m ∨
      ∃ i ∈ s, e i = 1 ∧ 0 < m i ∧ (∑ j ∈ s, e j*m j) = m i ∧
        ∀ j ∈ s, j ≠ i → e j = 0 ∨ m j = 0 := by
  classical
  by_cases htwo : 2 ≤ owningCopies s e m
  · exact Or.inl htwo
  right
  obtain ⟨i,hi,hprod⟩ := Finset.sum_pos_iff.mp hpos
  have he : 0 < e i := by nlinarith
  have hm : 0 < m i := by nlinarith
  let copies : ι → ℕ := fun j => if 0 < m j then e j else 0
  have htotal : (∑ j ∈ s, copies j) ≤ 1 := by
    change owningCopies s e m ≤ 1
    omega
  have hei : copies i = e i := if_pos hm
  have hile := Finset.single_le_sum (f := copies) (fun _ _ => Nat.zero_le _) hi
  have heone : e i = 1 := by omega
  have hsplit := Finset.sum_erase_add s copies hi
  have herase : ∑ j ∈ s.erase i, copies j = 0 := by omega
  have hothers : ∀ j ∈ s, j ≠ i → e j = 0 ∨ m j = 0 := by
    intro j hj hji
    have hjle := Finset.single_le_sum (f := copies) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hji,hj⟩)
    rw [herase] at hjle
    by_cases hmj : 0 < m j
    · left
      simpa only [copies,if_pos hmj,Nat.le_zero] using hjle
    · exact Or.inr (by omega)
  refine ⟨i,hi,heone,hm,?_,hothers⟩
  rw [Finset.sum_eq_single i]
  · rw [heone,one_mul]
  · intro j hj hji
    exact mul_eq_zero.mpr (hothers j hj hji)
  · exact fun hn => False.elim (hn hi)

theorem rootMultiplicity_prod_powers (s : Finset ι) (p : ι → Polynomial E)
    (e : ι → ℕ) (t : E) (hp : ∀ i ∈ s, p i ≠ 0) :
    (∏ i ∈ s, p i ^ e i).rootMultiplicity t =
      ∑ i ∈ s, e i*(p i).rootMultiplicity t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpa := hp a (Finset.mem_insert_self _ _)
    have hps : ∀ i ∈ s, p i ≠ 0 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hn : (∏ i ∈ s, p i ^ e i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hps i hi))
    rw [Finset.prod_insert ha,Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hpa) hn),
      rootMultiplicity_power _ _ _ hpa,ih hps,Finset.sum_insert ha]




















end
end ProximityPrize.SubmissionLower.CofactorOwnership6814


