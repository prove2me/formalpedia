-- Prove2me | solution 1 for AlgebraicCurve.Place.mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/085f400c-23a2-54f7-936a-a524af325f5c

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily

set_option autoImplicit false

open AlgebraicCurve

namespace GReadAux

theorem mem_nonunits_iff_mem_and {L : Type*} [Field L] (B : ValuationSubring L) (y : L) :
    y ∈ B.nonunits ↔ y ∈ B ∧ (y = 0 ∨ y⁻¹ ∉ B) := by
  constructor
  · intro hy
    have hyB : y ∈ B := B.nonunits_subset hy
    refine ⟨hyB, ?_⟩
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · right
      intro hinv
      have hunit : IsUnit (⟨y, hyB⟩ : B) :=
        ⟨⟨⟨y, hyB⟩, ⟨y⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy0), Subtype.ext (inv_mul_cancel₀ hy0)⟩, rfl⟩
      have h1 := (B.valuation_eq_one_iff ⟨y, hyB⟩).mp hunit
      have h2 := (B.mem_nonunits_iff).mp hy
      rw [show B.valuation y = B.valuation ((⟨y, hyB⟩ : B) : L) from rfl, h1] at h2
      exact lt_irrefl _ h2
  · rintro ⟨hyB, hy⟩
    rw [B.mem_nonunits_iff]
    rcases hy with hy0 | hinv
    · rw [hy0, map_zero]; exact zero_lt_one
    · rcases lt_or_eq_of_le (B.valuation_le_one ⟨y, hyB⟩) with hlt | heq
      · exact hlt
      · exfalso
        obtain ⟨u, hu⟩ := (B.valuation_eq_one_iff ⟨y, hyB⟩).mpr heq
        apply hinv
        have h3 : ((u⁻¹ : Bˣ) : B) * (u : B) = 1 := u.inv_mul
        have h4 : (((u⁻¹ : Bˣ) : B) : L) * y = 1 := by
          have := congrArg (Subtype.val) h3
          rw [hu] at this
          simpa using this
        rw [← (eq_inv_of_mul_eq_one_left h4)]
        exact ((u⁻¹ : Bˣ) : B).2

end GReadAux

theorem solution
    {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (x : F) [FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →ₐ[K] E) (s : AlgebraicCurve.Place K F) (w : AlgebraicCurve.Place K E)
    (T : Set F)

    (hT : ∀ t ∈ T, φ t ∈ w.toValuationSubring)

    (hvan : ∀ t ∈ T, ∀ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits →
      φ t - algebraMap K E c ∈ w.toValuationSubring.nonunits)

    (hO : ∃ t ∈ T, ∃ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits ∧ t ≠ algebraMap K F c)

    (hsep : ∀ s' : AlgebraicCurve.Place K F, (∀ t ∈ T, t ∈ s'.toValuationSubring) →
      (∀ t ∈ T, ∀ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits →
        t - algebraMap K F c ∈ s'.toValuationSubring.nonunits) → s' = s)
    (g : F) :
    g ∈ s.toValuationSubring ↔ φ g ∈ w.toValuationSubring := by
  classical

  set O' : ValuationSubring F := w.toValuationSubring.comap φ.toRingHom with hO'_def
  have hmemO' : ∀ y : F, y ∈ O' ↔ φ y ∈ w.toValuationSubring := fun y => Iff.rfl
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hnonO' : ∀ y : F, y ∈ O'.nonunits ↔ φ y ∈ w.toValuationSubring.nonunits := by
    intro y
    rw [GReadAux.mem_nonunits_iff_mem_and O' y, GReadAux.mem_nonunits_iff_mem_and w.toValuationSubring (φ y), hmemO', map_eq_zero_iff φ hφinj, ← map_inv₀, hmemO']
  have hK' : ∀ a : K, algebraMap K F a ∈ O' := fun a => by
    rw [hmemO', φ.commutes]
    exact w.algebraMap_mem' a

  have hne : O' ≠ ⊤ := by
    obtain ⟨t, ht, c, hc, htc⟩ := hO
    have hu0 : t - algebraMap K F c ≠ 0 := sub_ne_zero.mpr htc
    have hwn : φ (t - algebraMap K F c) ∈ w.toValuationSubring.nonunits := by
      rw [map_sub, φ.commutes]; exact hvan t ht c hc
    intro htop
    have hinv : (t - algebraMap K F c)⁻¹ ∈ O' := htop.symm ▸ ValuationSubring.mem_top _
    rw [hmemO', map_inv₀] at hinv
    rcases ((GReadAux.mem_nonunits_iff_mem_and _ _).mp hwn).2 with h0 | h
    · exact (map_ne_zero_iff φ.toRingHom hφinj).mpr hu0 h0
    · exact h hinv

  obtain ⟨s', hs'⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x O' hK' hne
  have h1 : ∀ t ∈ T, t ∈ s'.toValuationSubring := fun t ht => by
    rw [hs', hmemO']; exact hT t ht
  have h2 : ∀ t ∈ T, ∀ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits →
      t - algebraMap K F c ∈ s'.toValuationSubring.nonunits := fun t ht c hc => by
    rw [hs', hnonO', map_sub, φ.commutes]; exact hvan t ht c hc
  have hss : s' = s := hsep s' h1 h2
  rw [← hss, hs', hmemO']

end S_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily (solution)
