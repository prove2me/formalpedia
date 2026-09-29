-- Prove2me | solution 1 for AlgebraicCurve.carrier_hypotheses_of_endSlopes_of_nodePairs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6a5874cd-a993-5249-a736-e9a552b0ff03

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs

set_option autoImplicit false

open AlgebraicCurve

namespace PinCoreH
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg' (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem hasValue_zero_of_ord_pos (v : Place K F) {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := mem_of_ord_nonneg' v hg h.le
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  have : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord g = 0 at h0
    omega
  rwa [← IsLocalRing.residue_eq_zero_iff] at this

theorem eq_zero_of_hasValue_algebraMap_zero (v : Place K F) {c : K} (h : v.HasValue (algebraMap K F c) 0) : c = 0 :=
  (v.hasValue_algebraMap c).unique h

end PinCoreH

open Classical in

theorem solution
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (hSne : S.Nonempty)
    (hS₁₂ : ∀ s ∈ S, ∃ t ∈ S, t.2 = s.1) (hS₂₁ : ∀ s ∈ S, ∃ t ∈ S, t.1 = s.2)
    (Fx : Place k F → Prop) (hFx : ∀ s ∈ S, Fx s.1 ∧ Fx s.2)
    (T₁ T₂ : Finset (Place k F)) (hT₁ : ∀ v ∈ T₁, ¬ Fx v) (hT₂ : ∀ v ∈ T₂, ¬ Fx v)
    (Ebar₁ Ebar₂ EE₁ EE₂ : Place k F → ℤ)
    (hEbar₁ : ∀ v, Ebar₁ v = if v ∈ T₁ then 1 else 0) (hEbar₂ : ∀ v, Ebar₂ v = if v ∈ T₂ then 1 else 0)
    (hEE₁ : ∀ v, 0 ≤ EE₁ v) (hEE₂ : ∀ v, 0 ≤ EE₂ v)
    (u₁ u₂ : F) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (O1₁ : ∀ v, ¬ Fx v → (v.ord u₁ : ℤ) = EE₁ v - Ebar₁ v)
    (O1₂ : ∀ v, ¬ Fx v → (v.ord u₂ : ℤ) = EE₂ v - Ebar₂ v)
    (O2₁ : ∀ v, Fx v → (∀ s ∈ S, v ≠ s.1) → 0 ≤ v.ord u₁)
    (O2₂ : ∀ v, Fx v → (∀ s ∈ S, v ≠ s.2) → 0 ≤ v.ord u₂)
    (e : Place k F × Place k F → ℕ) (he : ∀ s ∈ S, 1 ≤ e s) (δ : ℚ)
    (A₁ : ∀ s ∈ S, δ ≤ (e s : ℚ) * ((s.1.ord u₁ : ℤ) : ℚ))
    (A₂ : ∀ s ∈ S, -((e s : ℚ) * ((s.2.ord u₂ : ℤ) : ℚ)) ≤ δ)
    (B : ∀ s ∈ S, δ = 0 → s.2.ord u₂ = 0 → s.1.ord u₁ = 0 ∧ ∃ c : k, s.1.HasValue u₁ c ∧ s.2.HasValue u₂ c)
    (hgp₁ : ∀ h : F, (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ S.image Prod.fst, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F, (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : k, h = algebraMap k F c) :
    (∀ v, v ∉ T₁ → 0 ≤ v.ord u₁) ∧ (∀ v ∈ T₁, -1 ≤ v.ord u₁) ∧
    (∀ v, v ∉ T₂ → 0 ≤ v.ord u₂) ∧ (∀ v ∈ T₂, -1 ≤ v.ord u₂) ∧
    (∀ s ∈ S, ∃ c : k, s.1.HasValue u₁ c ∧ s.2.HasValue u₂ c) := by
  classical

  have hfst_notT₁ : ∀ v, (∃ s ∈ S, v = s.1) → v ∉ T₁ := fun v ⟨s, hs, hv⟩ h => hT₁ v h (hv ▸ (hFx s hs).1)
  have hsnd_notT₂ : ∀ v, (∃ s ∈ S, v = s.2) → v ∉ T₂ := fun v ⟨s, hs, hv⟩ h => hT₂ v h (hv ▸ (hFx s hs).2)
  have he' : ∀ s ∈ S, (0 : ℚ) < e s := fun s hs => by exact_mod_cast he s hs

  have B₁ : ∀ v, (¬ ∃ s ∈ S, v = s.1) → (v ∉ T₁ → 0 ≤ v.ord u₁) ∧ (v ∈ T₁ → -1 ≤ v.ord u₁) := by
    intro v hvW
    have hvW' : ∀ s ∈ S, v ≠ s.1 := fun s hs hv => hvW ⟨s, hs, hv⟩
    by_cases hv : Fx v
    · exact ⟨fun _ => O2₁ v hv hvW', fun h => absurd hv (hT₁ v h)⟩
    · have h := O1₁ v hv
      constructor
      · intro hvT; rw [hEbar₁, if_neg hvT] at h; have := hEE₁ v; omega
      · intro hvT; rw [hEbar₁, if_pos hvT] at h; have := hEE₁ v; omega
  have B₂ : ∀ v, (¬ ∃ s ∈ S, v = s.2) → (v ∉ T₂ → 0 ≤ v.ord u₂) ∧ (v ∈ T₂ → -1 ≤ v.ord u₂) := by
    intro v hvW
    have hvW' : ∀ s ∈ S, v ≠ s.2 := fun s hs hv => hvW ⟨s, hs, hv⟩
    by_cases hv : Fx v
    · exact ⟨fun _ => O2₂ v hv hvW', fun h => absurd hv (hT₂ v h)⟩
    · have h := O1₂ v hv
      constructor
      · intro hvT; rw [hEbar₂, if_neg hvT] at h; have := hEE₂ v; omega
      · intro hvT; rw [hEbar₂, if_pos hvT] at h; have := hEE₂ v; omega

  have hi : ¬ 0 < δ := by
    intro hlt
    have hpos : ∀ s ∈ S, 1 ≤ s.1.ord u₁ := fun s hs => by
      have h1 := A₁ s hs
      have h2 : (0 : ℚ) < (e s : ℚ) * ((s.1.ord u₁ : ℤ) : ℚ) := lt_of_lt_of_le hlt h1
      have h3 : (0 : ℚ) < ((s.1.ord u₁ : ℤ) : ℚ) := (pos_iff_pos_of_mul_pos h2).mp (he' s hs)
      have h4 : (0 : ℤ) < s.1.ord u₁ := by exact_mod_cast h3
      omega
    have hb : ∀ v, v ∉ T₁ → 0 ≤ v.ord u₁ := fun v hvT => by
      by_cases hvW : ∃ s ∈ S, v = s.1
      · obtain ⟨s, hs, rfl⟩ := hvW; exact le_trans (by norm_num) (hpos s hs)
      · exact (B₁ v hvW).1 hvT
    have hb' : ∀ v ∈ T₁, -1 ≤ v.ord u₁ := fun v hvT => (B₁ v (fun h => hfst_notT₁ v h hvT)).2 hvT
    have hz : ∀ w ∈ S.image Prod.fst, w.HasValue u₁ 0 := fun w hw => by
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
      exact PinCoreH.hasValue_zero_of_ord_pos s.1 hu₁ (by have := hpos s hs; omega)
    exact hu₁ (hgp₁ u₁ hb hb' hz)

  have hii : ¬ δ < 0 := by
    intro hlt
    have hpos : ∀ s ∈ S, 1 ≤ s.2.ord u₂ := fun s hs => by
      have h1 := A₂ s hs
      have h2 : -((e s : ℚ) * ((s.2.ord u₂ : ℤ) : ℚ)) < 0 := lt_of_le_of_lt h1 hlt
      have h3 : (0 : ℚ) < (e s : ℚ) * ((s.2.ord u₂ : ℤ) : ℚ) := by linarith
      have h4 : (0 : ℚ) < ((s.2.ord u₂ : ℤ) : ℚ) := (pos_iff_pos_of_mul_pos h3).mp (he' s hs)
      have h5 : (0 : ℤ) < s.2.ord u₂ := by exact_mod_cast h4
      omega
    have hb : ∀ v, v ∉ T₂ → 0 ≤ v.ord u₂ := fun v hvT => by
      by_cases hvW : ∃ s ∈ S, v = s.2
      · obtain ⟨s, hs, rfl⟩ := hvW; exact le_trans (by norm_num) (hpos s hs)
      · exact (B₂ v hvW).1 hvT
    have hb' : ∀ v ∈ T₂, -1 ≤ v.ord u₂ := fun v hvT => (B₂ v (fun h => hsnd_notT₂ v h hvT)).2 hvT
    obtain ⟨c, hc⟩ := hgp₂ u₂ hb hb'
    obtain ⟨s₀, hs₀⟩ := hSne
    have hval0 : s₀.2.HasValue u₂ 0 := PinCoreH.hasValue_zero_of_ord_pos s₀.2 hu₂ (by have := hpos s₀ hs₀; omega)
    rw [hc] at hval0
    have hc0 := PinCoreH.eq_zero_of_hasValue_algebraMap_zero s₀.2 hval0
    apply hu₂; rw [hc, hc0, map_zero]
  have hδ : δ = 0 := le_antisymm (not_lt.mp hi) (not_lt.mp hii)

  have hn₁ : ∀ s ∈ S, 0 ≤ s.1.ord u₁ := fun s hs => by
    have h1 := A₁ s hs; rw [hδ] at h1
    have h2 : (0 : ℚ) ≤ ((s.1.ord u₁ : ℤ) : ℚ) := (mul_nonneg_iff_of_pos_left (he' s hs)).mp h1
    exact_mod_cast h2
  have hn₂ : ∀ s ∈ S, 0 ≤ s.2.ord u₂ := fun s hs => by
    have h1 := A₂ s hs; rw [hδ] at h1
    have h2 : (0 : ℚ) ≤ (e s : ℚ) * ((s.2.ord u₂ : ℤ) : ℚ) := by linarith
    have h3 : (0 : ℚ) ≤ ((s.2.ord u₂ : ℤ) : ℚ) := (mul_nonneg_iff_of_pos_left (he' s hs)).mp h2
    exact_mod_cast h3
  have C₁ : ∀ v, v ∉ T₁ → 0 ≤ v.ord u₁ := fun v hvT => by
    by_cases hvW : ∃ s ∈ S, v = s.1
    · obtain ⟨s, hs, rfl⟩ := hvW; exact hn₁ s hs
    · exact (B₁ v hvW).1 hvT
  have C₁' : ∀ v ∈ T₁, -1 ≤ v.ord u₁ := fun v hvT => (B₁ v (fun h => hfst_notT₁ v h hvT)).2 hvT
  have C₂ : ∀ v, v ∉ T₂ → 0 ≤ v.ord u₂ := fun v hvT => by
    by_cases hvW : ∃ s ∈ S, v = s.2
    · obtain ⟨s, hs, rfl⟩ := hvW; exact hn₂ s hs
    · exact (B₂ v hvW).1 hvT
  have C₂' : ∀ v ∈ T₂, -1 ≤ v.ord u₂ := fun v hvT => (B₂ v (fun h => hsnd_notT₂ v h hvT)).2 hvT

  obtain ⟨c₂, hc₂⟩ := hgp₂ u₂ C₂ C₂'
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; apply hu₂; rw [hc₂, map_zero]
  have hord₂ : ∀ v : Place k F, v.ord u₂ = 0 := fun v => by
    rw [hc₂]; exact (v.hasValue_algebraMap c₂).ord_eq_zero hc₂0

  exact ⟨C₁, C₁', C₂, C₂', fun s hs => (B s hs hδ (hord₂ s.2)).2⟩

#print axioms solution

end S_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs
end P2MW
export P2MW.S_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs (solution)
