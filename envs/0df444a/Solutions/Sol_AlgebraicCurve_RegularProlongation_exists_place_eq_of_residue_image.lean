-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_place_eq_of_residue_image
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1b38f24b-1761-5fef-8ad9-1bf9bb15f35c

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 3200000 in
theorem solution
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (S : Subring F) [IsLocalRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)

    (O : ValuationSubring Fbar) (hOtop : O ≠ ⊤) (hOpir : IsPrincipalIdealRing ↥O)
    (hO : ∀ g : Fbar, g ∈ O ↔ ∃ f : ↥S, R.residue ⟨(f : F), hSR f⟩ = g)

    (hloc : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ R.residue ⟨(f : F), hSR f⟩ ∈ O.nonunits)

    (hrat : ∀ f : ↥S, ∃ a : ↥A, f - ⟨algebraMap L F (a : L), hAS a⟩ ∈ maximalIdeal ↥S) :
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.toValuationSubring = O ∧
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ R.integers), f ∈ S ∧ R.residue ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ R.integers), Q.ord (R.residue ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by
  classical
  let red : ↥S → Fbar := fun f => R.residue ⟨(f : F), hSR f⟩
  have hred : ∀ f, red f = R.residue ⟨(f : F), hSR f⟩ := fun f => rfl
  let ρ₀ : ↥S →+* ↥R.integers := (S.subtype).codRestrict R.integers.toSubring (fun f => hSR f)
  let redH : ↥S →+* Fbar := R.residue.comp ρ₀
  have hredH : ∀ f, redH f = red f := fun f => rfl

  have hconstS : ∀ a : ↥A, red ⟨algebraMap L F (a : L), hAS a⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
    intro a
    rw [hred, ← R.residue_algebraMap a]
  have hconst : ∀ z : ResidueField ↥A, algebraMap (ResidueField ↥A) Fbar z ∈ O := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    rw [hO]
    exact ⟨⟨algebraMap L F (a : L), hAS a⟩, hconstS a⟩

  obtain ⟨Q, rfl⟩ : ∃ Q : Place (ResidueField ↥A) Fbar, Q.toValuationSubring = O := ⟨⟨O, hconst, hOtop, hOpir⟩, rfl⟩
  have hredO : ∀ f : ↥S, red f ∈ Q.toValuationSubring := fun f => (hO _).mpr ⟨f, rfl⟩

  have hunitO : ∀ (g : Fbar) (hg : g ∈ Q.toValuationSubring), IsUnit (⟨g, hg⟩ : ↥Q.toValuationSubring) ↔ g ∉ Q.toValuationSubring.nonunits := by
    intro g hg
    rw [ValuationSubring.valuation_eq_one_iff, ValuationSubring.mem_nonunits_iff, not_lt]
    constructor
    · intro h; exact h.symm.le
    · intro h; exact le_antisymm (Q.toValuationSubring.valuation_le_one ⟨g, hg⟩) h
  have hunitS : ∀ f : ↥S, IsUnit f ↔ IsUnit (⟨red f, hredO f⟩ : ↥Q.toValuationSubring) := by
    intro f
    rw [hunitO, ← hloc, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥Q.toValuationSubring
  have hπ0 : ((π : ↥Q.toValuationSubring) : Fbar) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  have hordO : ∀ (g : Fbar) (hg : g ∈ Q.toValuationSubring), IsUnit (⟨g, hg⟩ : ↥Q.toValuationSubring) ↔ Q.ord g = 0 ∧ g ≠ 0 := by
    intro g hg
    constructor
    · intro hu
      refine ⟨?_, ?_⟩
      · have := Q.ord_coe_unit hu.unit
        rwa [IsUnit.unit_spec] at this
      · intro h0
        rw [show (⟨g, hg⟩ : ↥Q.toValuationSubring) = 0 from Subtype.ext h0] at hu
        exact not_isUnit_zero hu
    · rintro ⟨h0, hne⟩
      obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hne hπ
      rw [h0, zpow_zero, mul_one] at hu
      have : (⟨g, hg⟩ : ↥Q.toValuationSubring) = (u : ↥Q.toValuationSubring) := Subtype.ext hu
      rw [this]; exact u.isUnit
  refine ⟨Q, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨f, hf⟩ := (hO (g : Fbar)).mp g.2
    obtain ⟨a, ha⟩ := hrat f
    refine ⟨IsLocalRing.residue ↥A a, ?_⟩
    have h1 : red (f - ⟨algebraMap L F (a : L), hAS a⟩) ∈ Q.toValuationSubring.nonunits := (hloc _).mp ha
    have h2 : red (f - ⟨algebraMap L F (a : L), hAS a⟩) = red f - red ⟨algebraMap L F (a : L), hAS a⟩ := by
      rw [← hredH, ← hredH, ← hredH, map_sub]
    rw [h2, hconstS] at h1
    have h3 : (g - algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a) : ↥Q.toValuationSubring) ∈
        maximalIdeal ↥Q.toValuationSubring := by
      rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
      have : ((g - algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a) : ↥Q.toValuationSubring) : Fbar) =
          red f - algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
        push_cast; rw [Place.coe_algebraMap, ← hf]
      rw [this]; exact h1

    have h4 : IsLocalRing.residue ↥Q.toValuationSubring g =
        IsLocalRing.residue ↥Q.toValuationSubring (algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a)) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact h3
    rw [h4]
    first
      | rfl
      | (rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply])
  ·
    intro f; exact ⟨hSR f, hredO f⟩
  ·
    intro g hg
    obtain ⟨f, hf⟩ := (hO g).mp hg
    exact ⟨(f : F), hSR f, f.2, hf⟩
  ·
    intro f hR
    have : R.residue ⟨(f : F), hR⟩ = red f := rfl
    rw [this, hunitS, hordO]
  ·
    obtain ⟨T, hT⟩ := (hO (π : Fbar)).mp π.2
    refine ⟨T, hSR T, ?_⟩
    show Q.ord (red T) = 1
    rw [hred, hT]; exact Q.ord_coe_irreducible hπ
  ·
    intro Q' hQ'
    have hle : Q.toValuationSubring ≤ Q'.toValuationSubring := by
      intro g hg
      obtain ⟨f, hf⟩ := (hO g).mp hg
      obtain ⟨hR, hm⟩ := hQ' f
      rw [← hf]; exact hm
    apply Place.ext
    by_contra hne
    apply Q'.ne_top'
    obtain ⟨g, hgQ', hgO⟩ : ∃ g, g ∈ Q'.toValuationSubring ∧ g ∉ Q.toValuationSubring := by
      by_contra h
      push Not at h
      exact hne (le_antisymm (fun g hg => h g hg) hle)
    have hg0 : g ≠ 0 := fun h0 => hgO (h0 ▸ Q.toValuationSubring.zero_mem)
    obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hg0 hπ
    have hordneg : Q.ord g < 0 := by
      by_contra h
      push Not at h
      apply hgO
      rw [hu]
      refine mul_mem (u : ↥Q.toValuationSubring).2 ?_
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
      rw [hn, zpow_natCast]; exact pow_mem π.2 n

    have hπinv : ((π : ↥Q.toValuationSubring) : Fbar)⁻¹ ∈ Q'.toValuationSubring := by
      obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat (le_of_lt hordneg)
      have hm1 : 1 ≤ m := by omega
      set u' : Fbar := (((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring) : Fbar) with hu'def
      have huinv : ((u : ↥Q.toValuationSubring) : Fbar) * u' = 1 := congrArg Subtype.val u.mul_inv
      have hgu : g * u' = ((π : ↥Q.toValuationSubring) : Fbar) ^ (-(m : ℤ)) := by
        rw [hu, hm, mul_assoc, mul_comm (((π : ↥Q.toValuationSubring) : Fbar) ^ _), ← mul_assoc, huinv, one_mul]
      have e1 : ((π : ↥Q.toValuationSubring) : Fbar)⁻¹ = g * u' * ((π : ↥Q.toValuationSubring) : Fbar) ^ (m - 1) := by
        rw [hgu, ← zpow_natCast, Nat.cast_sub hm1, Nat.cast_one, ← zpow_add₀ hπ0]
        have : (-(m : ℤ) + ((m : ℤ) - 1)) = -1 := by ring
        rw [this, zpow_neg_one]
      rw [e1]
      exact mul_mem (mul_mem hgQ' (hle ((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring).2)) (pow_mem (hle π.2) _)
    refine eq_top_iff.mpr fun x _ => ?_
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem _
    obtain ⟨v, hv⟩ := Q.exists_unit_mul_zpow hx0 hπ
    rw [hv]
    refine mul_mem (hle (v : ↥Q.toValuationSubring).2) ?_
    rcases le_or_gt 0 (Q.ord x) with h | h
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
      rw [hn, zpow_natCast]; exact pow_mem (hle π.2) n
    · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt h)
      rw [hn, zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hπinv n

end S_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image (solution)
