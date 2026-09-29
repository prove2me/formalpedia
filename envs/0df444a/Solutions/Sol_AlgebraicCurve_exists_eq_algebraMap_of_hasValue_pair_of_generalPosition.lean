-- Prove2me | solution 1 for AlgebraicCurve.exists_eq_algebraMap_of_hasValue_pair_of_generalPosition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ea1fbda5-2e03-541b-9e58-3fdf660fbc69

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_eq_algebraMap_of_hasValue_pair_of_generalPosition

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace RigidityGPH

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem hasValue_sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

theorem ord_nonneg_of_mem' {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg' {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_sub_nonneg_of_mem {f g : F} (hf : 0 ≤ v.ord f) (hg : g ∈ v.toValuationSubring) :
    0 ≤ v.ord (f - g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_sub]
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [neg_zero, Place.ord_zero]
    · exact ord_nonneg_of_mem' v (neg_mem hg)
  · exact ord_nonneg_of_mem' v (sub_mem (mem_of_ord_nonneg' v hf0 hf) hg)

theorem neg_one_le_ord_sub_of_mem {f g : F} (hf : -1 ≤ v.ord f) (hg : g ∈ v.toValuationSubring) :
    -1 ≤ v.ord (f - g) := by
  classical
  rcases eq_or_ne (f - g) 0 with h0 | h0
  · rw [h0, Place.ord_zero]; norm_num
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : ((π : v.toValuationSubring) : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπ1 : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hmem : (f - g) * (π : F) ∈ v.toValuationSubring := by
    rw [sub_mul]
    refine sub_mem ?_ (mul_mem hg (SetLike.coe_mem _))
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [zero_mul]; exact zero_mem _
    · apply mem_of_ord_nonneg' v (mul_ne_zero hf0 hπ0)
      rw [v.ord_mul hf0 hπ0, hπ1]; omega
  have h := ord_nonneg_of_mem' v hmem
  rw [v.ord_mul h0 hπ0, hπ1] at h
  omega

end RigidityGPH

theorem solution
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (E₁ E₂ : Finset (Place k F))
    (hgp₁ : ∀ h : F,
      (∀ v : Place k F, v ∉ E₁ → 0 ≤ v.ord h) → (∀ v ∈ E₁, -1 ≤ v.ord h) →
      (∀ s ∈ S, s.1.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F,
      (∀ v : Place k F, v ∉ E₂ → 0 ≤ v.ord h) → (∀ v ∈ E₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k F c)
    (h₁ h₂ : F)
    (hh₁ : ∀ v : Place k F, v ∉ E₁ → 0 ≤ v.ord h₁) (hh₁' : ∀ v ∈ E₁, -1 ≤ v.ord h₁)
    (hh₂ : ∀ v : Place k F, v ∉ E₂ → 0 ≤ v.ord h₂) (hh₂' : ∀ v ∈ E₂, -1 ≤ v.ord h₂)
    (hval : ∀ s ∈ S, ∃ c : k, s.1.HasValue h₁ c ∧ s.2.HasValue h₂ c) :
    ∃ c : k, h₁ = algebraMap k F c ∧ h₂ = algebraMap k F c := by

  obtain ⟨c, hc⟩ := hgp₂ h₂ hh₂ hh₂'
  refine ⟨c, ?_, hc⟩

  have hCmem : ∀ v : Place k F, algebraMap k F c ∈ v.toValuationSubring :=
    fun v => (Place.hasValue_algebraMap v c).mem
  have hzero : h₁ - algebraMap k F c = 0 := by
    apply hgp₁ (h₁ - algebraMap k F c)
    · intro v hv; exact RigidityGPH.ord_sub_nonneg_of_mem v (hh₁ v hv) (hCmem v)
    · intro v hv; exact RigidityGPH.neg_one_le_ord_sub_of_mem v (hh₁' v hv) (hCmem v)
    · intro s hs
      obtain ⟨c', hc₁, hc₂⟩ := hval s hs
      have hc₂' : s.2.HasValue h₂ c := by rw [hc]; exact Place.hasValue_algebraMap _ c
      have hcc : c' = c := hc₂.unique hc₂'
      have := RigidityGPH.hasValue_sub s.1 hc₁ (Place.hasValue_algebraMap s.1 c)
      rwa [hcc, sub_self] at this
  exact sub_eq_zero.mp hzero

end S_AlgebraicCurve_exists_eq_algebraMap_of_hasValue_pair_of_generalPosition
end P2MW
export P2MW.S_AlgebraicCurve_exists_eq_algebraMap_of_hasValue_pair_of_generalPosition (solution)
