-- Prove2me | solution 1 for AlgebraicCurve.twelve_mul_eq_of_sum_ordDiff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a63255dd-b4ba-54e6-864a-7b55a6eaeb1e

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_twelve_mul_eq_of_sum_ordDiff_eq

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F) (S₀ S₁ Sinf : Finset (Place K F)) (ψ : ℕ) (g : ℤ) (h₀ : ∀ v ∈ S₀, v.ordDiff (KaehlerDifferential.D K F t) = v.ord t - 1 ∧ 0 < v.ord t ∧ v.ord t ∣ 3) (h₁ : ∀ v ∈ S₁, v.ordDiff (KaehlerDifferential.D K F t) = v.ord (t - algebraMap K F 1728) - 1 ∧ 0 < v.ord (t - algebraMap K F 1728) ∧ v.ord (t - algebraMap K F 1728) ∣ 2) (hinf : ∀ v ∈ Sinf, v.ordDiff (KaehlerDifferential.D K F t) = v.ord t - 1 ∧ v.ord t < 0) (hψ₀ : ∑ v ∈ S₀, v.ord t = ψ) (hψ₁ : ∑ v ∈ S₁, v.ord (t - algebraMap K F 1728) = ψ) (hψinf : ∑ v ∈ Sinf, -v.ord t = ψ) (S : Finset (Place K F)) (hS : ∀ v, v ∈ S ↔ v ∈ S₀ ∨ v ∈ S₁ ∨ v ∈ Sinf) (hcan : ∑ v ∈ S, v.ordDiff (KaehlerDifferential.D K F t) = 2 * g - 2) : 12 * g = 12 + ψ - 3 * ((S₁.filter fun v => v.ord (t - algebraMap K F 1728) = 1).card : ℤ) - 4 * ((S₀.filter fun v => v.ord t = 1).card : ℤ) - 6 * (Sinf.card : ℤ) := by
  letI : DecidableEq (Place K F) := Classical.decEq _

  have houter : Disjoint (S₀ ∪ S₁) Sinf := by
    rw [Finset.disjoint_left]
    intro v hv hvi
    have hi1 := (hinf v hvi).1
    have hi2 := (hinf v hvi).2
    rcases Finset.mem_union.mp hv with h | h
    · have := (h₀ v h).2.1
      omega
    · have h1 := (h₁ v h).1
      have h2 := (h₁ v h).2.1
      omega

  have hSeq : S = (S₀ ∪ S₁) ∪ Sinf := by
    ext v
    rw [hS v, Finset.mem_union, Finset.mem_union, or_assoc]

  have hov : ∀ v ∈ S₀ ∩ S₁, v.ordDiff (KaehlerDifferential.D K F t) = 0 := by
    intro v hv
    obtain ⟨hv0, hv1⟩ := Finset.mem_inter.mp hv
    obtain ⟨e0, p0, d3⟩ := h₀ v hv0
    obtain ⟨e1, p1, d2⟩ := h₁ v hv1
    have hle3 : v.ord t ≤ 3 := Int.le_of_dvd (by omega) d3
    have hne2 : ¬ v.ord t = 2 := by
      intro h
      rw [h] at d3
      omega
    have hle2 : v.ord (t - algebraMap K F 1728) ≤ 2 := Int.le_of_dvd (by omega) d2
    omega
  have hzero : ∑ v ∈ S₀ ∩ S₁, v.ordDiff (KaehlerDifferential.D K F t) = 0 := by
    rw [Finset.sum_congr rfl hov, Finset.sum_const, smul_zero]
  have hinner : ∑ v ∈ S₀ ∪ S₁, v.ordDiff (KaehlerDifferential.D K F t) = (∑ v ∈ S₀, v.ordDiff (KaehlerDifferential.D K F t)) + ∑ v ∈ S₁, v.ordDiff (KaehlerDifferential.D K F t) := by
    have h := Finset.sum_union_inter (s₁ := S₀) (s₂ := S₁) (f := fun v => v.ordDiff (KaehlerDifferential.D K F t))
    rw [hzero] at h
    omega
  rw [hSeq, Finset.sum_union houter, hinner] at hcan

  have hE0 : (∑ v ∈ S₀, v.ordDiff (KaehlerDifferential.D K F t)) + (S₀.card : ℤ) = (ψ : ℤ) := by
    have hpt : ∀ v ∈ S₀, v.ordDiff (KaehlerDifferential.D K F t) + 1 = v.ord t := by
      intro v hv
      have h := (h₀ v hv).1
      omega
    have hdist : ∑ v ∈ S₀, (v.ordDiff (KaehlerDifferential.D K F t) + 1) = (∑ v ∈ S₀, v.ordDiff (KaehlerDifferential.D K F t)) + (S₀.card : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← hdist, Finset.sum_congr rfl hpt, hψ₀]
  have hE1 : (∑ v ∈ S₁, v.ordDiff (KaehlerDifferential.D K F t)) + (S₁.card : ℤ) = (ψ : ℤ) := by
    have hpt : ∀ v ∈ S₁, v.ordDiff (KaehlerDifferential.D K F t) + 1 = v.ord (t - algebraMap K F 1728) := by
      intro v hv
      have h := (h₁ v hv).1
      omega
    have hdist : ∑ v ∈ S₁, (v.ordDiff (KaehlerDifferential.D K F t) + 1) = (∑ v ∈ S₁, v.ordDiff (KaehlerDifferential.D K F t)) + (S₁.card : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← hdist, Finset.sum_congr rfl hpt, hψ₁]
  have hEinf : (∑ v ∈ Sinf, v.ordDiff (KaehlerDifferential.D K F t)) + (Sinf.card : ℤ) + (ψ : ℤ) = 0 := by
    have hpt : ∀ v ∈ Sinf, (v.ordDiff (KaehlerDifferential.D K F t) + 1) + -v.ord t = 0 := by
      intro v hv
      have h := (hinf v hv).1
      omega
    have hz : ∑ v ∈ Sinf, ((v.ordDiff (KaehlerDifferential.D K F t) + 1) + -v.ord t) = 0 := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hz
    have hneg := hψinf
    omega

  have key0 : ∀ v ∈ S₀.filter (fun v => ¬ v.ord t = 1), v.ord t = 3 := by
    intro v hv
    obtain ⟨hvS, hne⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, hp, hd⟩ := h₀ v hvS
    have hle : v.ord t ≤ 3 := Int.le_of_dvd (by omega) hd
    have h2 : ¬ v.ord t = 2 := by
      intro h
      rw [h] at hd
      omega
    omega
  have hsplit0 : (∑ v ∈ S₀.filter (fun v => v.ord t = 1), v.ord t) + ∑ v ∈ S₀.filter (fun v => ¬ v.ord t = 1), v.ord t = ∑ v ∈ S₀, v.ord t := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hA0 : ∑ v ∈ S₀.filter (fun v => v.ord t = 1), v.ord t = ((S₀.filter fun v => v.ord t = 1).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB0 : ∑ v ∈ S₀.filter (fun v => ¬ v.ord t = 1), v.ord t = ((S₀.filter (fun v => ¬ v.ord t = 1)).card : ℤ) * 3 := by
    rw [Finset.sum_congr rfl key0, Finset.sum_const, nsmul_eq_mul]
  have hcards0 : (S₀.filter fun v => v.ord t = 1).card + (S₀.filter (fun v => ¬ v.ord t = 1)).card = S₀.card := by
    rw [Finset.card_filter_add_card_filter_not]

  have key1 : ∀ v ∈ S₁.filter (fun v => ¬ v.ord (t - algebraMap K F 1728) = 1), v.ord (t - algebraMap K F 1728) = 2 := by
    intro v hv
    obtain ⟨hvS, hne⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, hp, hd⟩ := h₁ v hvS
    have hle : v.ord (t - algebraMap K F 1728) ≤ 2 := Int.le_of_dvd (by omega) hd
    omega
  have hsplit1 : (∑ v ∈ S₁.filter (fun v => v.ord (t - algebraMap K F 1728) = 1), v.ord (t - algebraMap K F 1728)) + ∑ v ∈ S₁.filter (fun v => ¬ v.ord (t - algebraMap K F 1728) = 1), v.ord (t - algebraMap K F 1728) = ∑ v ∈ S₁, v.ord (t - algebraMap K F 1728) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hA1 : ∑ v ∈ S₁.filter (fun v => v.ord (t - algebraMap K F 1728) = 1), v.ord (t - algebraMap K F 1728) = ((S₁.filter fun v => v.ord (t - algebraMap K F 1728) = 1).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB1 : ∑ v ∈ S₁.filter (fun v => ¬ v.ord (t - algebraMap K F 1728) = 1), v.ord (t - algebraMap K F 1728) = ((S₁.filter (fun v => ¬ v.ord (t - algebraMap K F 1728) = 1)).card : ℤ) * 2 := by
    rw [Finset.sum_congr rfl key1, Finset.sum_const, nsmul_eq_mul]
  have hcards1 : (S₁.filter fun v => v.ord (t - algebraMap K F 1728) = 1).card + (S₁.filter (fun v => ¬ v.ord (t - algebraMap K F 1728) = 1)).card = S₁.card := by
    rw [Finset.card_filter_add_card_filter_not]
  omega

end S_AlgebraicCurve_twelve_mul_eq_of_sum_ordDiff_eq
end P2MW
export P2MW.S_AlgebraicCurve_twelve_mul_eq_of_sum_ordDiff_eq (solution)
