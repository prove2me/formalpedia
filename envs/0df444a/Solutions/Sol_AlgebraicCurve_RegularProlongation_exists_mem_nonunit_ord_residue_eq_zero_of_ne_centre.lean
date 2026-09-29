-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/696321de-87bf-5585-91d8-842dedf78674

import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace R4Sep1k

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem ord_eq_zero_iff_adicValuation_eq_one {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [Place.ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := WithZero.exp_log (v.adicValuation_ne_zero hf)
    rw [h, WithZero.exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, WithZero.log_one]

theorem mem_maximalIdeal_iff_ord_pos {x : F} (hx : x ≠ 0) (hmem : x ∈ v.toValuationSubring) :
    (⟨x, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      0 < v.ord x := by
  have hnonneg : 0 ≤ v.ord x := ord_nonneg_of_mem v hmem
  have hcoe : ((⟨x, hmem⟩ : v.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    hcoe, ← ord_eq_zero_iff_adicValuation_eq_one v hx]
  omega

end R4Sep1k

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {FSS : Type} [Field FSS] [Algebra (ResidueField ↥A) FSS]
    (R : RegularProlongation A F FSS)
    (O : Subring F) [IsLocalRing ↥O] (hOR : ∀ f : F, f ∈ O → f ∈ R.integers)
    (Bx : Subring F) (hBO : Bx ≤ O)
    (hloc : ∀ f : F, f ∈ O ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
    (nd y : Place (ResidueField ↥A) FSS)

    (huniq : ∀ y' : Place (ResidueField ↥A) FSS,
      (∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring) →
      (∀ (b : F) (hb : b ∈ Bx), ¬ IsUnit (⟨b, hBO hb⟩ : ↥O) →
        ∃ hm : R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring, (⟨_, hm⟩ : ↥y'.toValuationSubring) ∈ maximalIdeal ↥y'.toValuationSubring) →
      y' = nd)
    (hy : ∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y.toValuationSubring)
    (hne : y ≠ nd) :
    ∃ (g : F) (hg : g ∈ Bx), ¬ IsUnit (⟨g, hBO hg⟩ : ↥O) ∧
      y.ord (R.residue ⟨g, hOR g (hBO hg)⟩) = 0 ∧ R.residue ⟨g, hOR g (hBO hg)⟩ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  refine huniq y hy ?_
  intro b hb hbu
  refine ⟨hy b hb, ?_⟩
  by_cases h0 : R.residue ⟨b, hOR b (hBO hb)⟩ = 0
  · have : (⟨R.residue ⟨b, hOR b (hBO hb)⟩, hy b hb⟩ : ↥y.toValuationSubring) = 0 :=
      Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  · rw [R4Sep1k.mem_maximalIdeal_iff_ord_pos y h0 (hy b hb)]
    have hnn := R4Sep1k.ord_nonneg_of_mem y (hy b hb)
    have hne0 : y.ord (R.residue ⟨b, hOR b (hBO hb)⟩) ≠ 0 := fun h => h0 (hcon b hb hbu h)
    omega

end S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre (solution)
