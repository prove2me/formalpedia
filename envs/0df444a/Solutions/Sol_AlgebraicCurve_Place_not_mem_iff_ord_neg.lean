-- Prove2me | solution 1 for AlgebraicCurve.Place.not_mem_iff_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:43.134195+00:00
-- url     : https://prove2.me/submissions/d65f84c7-3429-4af0-b5ef-697a7d0d19f7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

namespace AlgebraicCurve.Place

/-- A normalized place has negative order exactly outside its valuation ring. -/
theorem _root_.solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) : f ∉ v.toValuationSubring ↔ v.ord f < 0 := by
  by_cases hf : f = 0
  · subst f
    simp
  have hmem : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    constructor
    · intro h
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨f, h⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf) hπ
      have he : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
        have hcoe := congrArg Subtype.val hu
        push_cast at hcoe
        rw [zpow_natCast]
        exact hcoe
      rw [he, v.ord_unit_smul_zpow u hπ (n : ℤ)]
      exact Int.natCast_nonneg n
    · intro h
      obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
      rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from
        (Int.toNat_of_nonneg h).symm, zpow_natCast]
      exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
  exact hmem.not.trans not_le

end AlgebraicCurve.Place
