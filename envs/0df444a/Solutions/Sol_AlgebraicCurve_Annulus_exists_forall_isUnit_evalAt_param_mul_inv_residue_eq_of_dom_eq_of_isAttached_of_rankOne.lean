-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/83e3493d-b29f-511f-869c-d5a00d059ba6

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace ANR

theorem isUnit_of_evalAt_ne_zero {K F : Type} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (hne : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hu
  apply hne
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hu
  have hres : residue v.toValuationSubring ⟨f, hf⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
  rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem ord_eq_zero_of_evalAt_ne_zero {K F : Type} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hu := isUnit_of_evalAt_ne_zero v hf hne
  have := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec] at this

theorem ne_zero_of_evalAt_ne_zero {K F : Type} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hne : v.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hne
  rw [v.evalAt_of_mem (zero_mem _)]
  have : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [this, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem false_of_zpow_eq_unit {L : Type} [Field L] (A : ValuationSubring L) {t : L} (htA : t ∈ A)
    (htm : (⟨t, htA⟩ : A) ∈ maximalIdeal A) {n : ℤ} (hn : n ≠ 0) (u : Aˣ)
    (h : ((u : A) : L) = t ^ n) : False := by
  have key : ∀ k : ℕ, k ≠ 0 → ∀ w : Aˣ, ((w : A) : L) = t ^ k → False := by
    intro k hk w hw
    have hmem : (w : A) ∈ maximalIdeal A := by
      have : (w : A) = (⟨t, htA⟩ : A) ^ k := Subtype.ext (by push_cast; exact hw)
      rw [this]
      exact Ideal.pow_mem_of_mem _ htm k (Nat.pos_of_ne_zero hk)
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (Units.isUnit w)
  rcases Int.natAbs_eq n with hk | hk
  · rw [hk, zpow_natCast] at h
    exact key n.natAbs (Int.natAbs_ne_zero.2 hn) u h
  · rw [hk, zpow_neg, zpow_natCast] at h
    refine key n.natAbs (Int.natAbs_ne_zero.2 hn) u⁻¹ ?_
    have hu : (((u : A) : L)) * (((u⁻¹ : Aˣ) : A) : L) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
    rw [h] at hu
    have ht0 : t ^ n.natAbs ≠ 0 := by
      intro h0; rw [h0, inv_zero, zero_mul] at hu; exact zero_ne_one hu
    calc (((u⁻¹ : Aˣ) : A) : L) = (t ^ n.natAbs) * ((t ^ n.natAbs)⁻¹ * (((u⁻¹ : Aˣ) : A) : L)) := by
          rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
      _ = t ^ n.natAbs := by rw [hu, mul_one]

end ANR

open ANR in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (An₁ An₂ : Annulus A F) (hdom : An₂.dom = An₁.dom)
    (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar) (hx : x.IsRational)
    (hatt : An₁.IsAttached C x)
    (hz₂ : ∃ h : An₂.param ∈ C.integers, C.residue ⟨An₂.param, h⟩ ≠ 0) :
    ∃ r : IsLocalRing.ResidueField A, r ≠ 0 ∧
      ∀ P ∈ An₁.dom, ∃ h : P.evalAt An₂.param * (P.evalAt An₁.param)⁻¹ ∈ A,
        IsUnit (⟨_, h⟩ : A) ∧ IsLocalRing.residue A ⟨_, h⟩ = r := by
  classical

  rcases (An₁.dom).eq_empty_or_nonempty with hempty | ⟨P₀, hP₀⟩
  · refine ⟨1, one_ne_zero, fun P hP => ?_⟩
    rw [hempty] at hP; exact absurd hP (Set.notMem_empty P)
  obtain ⟨hz₂C, hres₂⟩ := hz₂
  obtain ⟨-, hz₁C, hord₁, hslope⟩ := hatt

  have dom₂ : ∀ P, P ∈ An₁.dom → P ∈ An₂.dom := fun P hP => hdom.symm ▸ hP
  have h1 : ∀ P ∈ An₁.dom, An₁.param ∈ P.toValuationSubring ∧ (∃ h : P.evalAt An₁.param ∈ A,
      (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧ P.evalAt An₁.param ≠ 0 := fun P hP =>
    ⟨(An₁.mem_dom P hP).2.1, (An₁.mem_dom P hP).2.2.1, (An₁.mem_dom P hP).2.2.2.1⟩
  have h2 : ∀ P ∈ An₁.dom, An₂.param ∈ P.toValuationSubring ∧ (∃ h : P.evalAt An₂.param ∈ A,
      (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧ P.evalAt An₂.param ≠ 0 := fun P hP =>
    ⟨(An₂.mem_dom P (dom₂ P hP)).2.1, (An₂.mem_dom P (dom₂ P hP)).2.2.1, (An₂.mem_dom P (dom₂ P hP)).2.2.2.1⟩
  have hord1 : ∀ P ∈ An₁.dom, P.ord An₁.param = 0 := fun P hP =>
    ord_eq_zero_of_evalAt_ne_zero P (h1 P hP).1 (h1 P hP).2.2
  have hord2 : ∀ P ∈ An₁.dom, P.ord An₂.param = 0 := fun P hP =>
    ord_eq_zero_of_evalAt_ne_zero P (h2 P hP).1 (h2 P hP).2.2
  have hz₁0 : An₁.param ≠ 0 := ne_zero_of_evalAt_ne_zero P₀ (h1 P₀ hP₀).2.2
  have hz₂0 : An₂.param ≠ 0 := ne_zero_of_evalAt_ne_zero P₀ (h2 P₀ hP₀).2.2

  set a : ℤ := x.ord (C.residue ⟨An₂.param, hz₂C⟩) with ha
  have hsl : ∀ P ∈ An₁.dom, ∃ h : P.evalAt An₂.param * (P.evalAt An₁.param) ^ (-a) ∈ A, IsUnit (⟨_, h⟩ : A) :=
    hslope An₂.param hz₂C hres₂ hord2

  obtain ⟨m, c, hc0, hup⟩ := An₂.unit_principle An₁.param hz₁0 (fun P hP => hord1 P (hdom ▸ hP))

  have ha1 : 1 ≤ a := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨h, hu⟩ := hsl P₀ hP₀
    obtain ⟨hA₂, hm₂⟩ := (h2 P₀ hP₀).2.1
    obtain ⟨hA₁, -⟩ := (h1 P₀ hP₀).2.1
    apply (IsLocalRing.mem_maximalIdeal _).1 ?_ hu
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -a)
    have : (⟨_, h⟩ : A) = ⟨P₀.evalAt An₂.param, hA₂⟩ * ⟨P₀.evalAt An₁.param, hA₁⟩ ^ k :=
      Subtype.ext (by push_cast; rw [hk, zpow_natCast])
    rw [this]
    exact Ideal.mul_mem_right _ _ hm₂

  have hpow : ∀ P ∈ An₁.dom, ∃ w : Aˣ, (P.evalAt An₁.param) ^ (1 - a * m) = c * ((w : A) : L) := by
    intro P hP
    obtain ⟨hu₁, hu⟩ := hsl P hP
    obtain ⟨hv₁, hv⟩ := hup P (dom₂ P hP)
    set z1 := P.evalAt An₁.param with hz1
    set z2 := P.evalAt An₂.param with hz2
    have hz10 : z1 ≠ 0 := (h1 P hP).2.2
    have hz20 : z2 ≠ 0 := (h2 P hP).2.2
    refine ⟨hv.unit * hu.unit ^ m, ?_⟩
    have coe_zpow : ∀ (u : Aˣ) (k : ℤ), (((u ^ k : Aˣ) : A) : L) = (((u : A) : L)) ^ k := by
      intro u k
      have : (((u ^ k : Aˣ) : A) : L) = ((Units.map (A.subtype : A →* L) (u ^ k) : Lˣ) : L) := rfl
      rw [this, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
    have hvL : (((hv.unit : Aˣ) : A) : L) = z1 * c⁻¹ * z2 ^ (-m) := congrArg Subtype.val hv.unit_spec
    have huL : (((hu.unit : Aˣ) : A) : L) = z2 * z1 ^ (-a) := congrArg Subtype.val hu.unit_spec
    rw [Units.val_mul, Subring.coe_mul, coe_zpow, hvL, huL, mul_zpow, ← zpow_mul, neg_mul, zpow_neg, zpow_neg,
      zpow_sub₀ hz10, zpow_one, zpow_mul]
    field_simp

  have ham : a * m = 1 := by
    by_contra hne
    have hn : (1 - a * m) ≠ 0 := fun h => hne (by omega)

    obtain ⟨-, hreg, ⟨hA₁, hm₁⟩, hne0, m', hm', hmod⟩ := An₁.mem_dom P₀ hP₀
    have hex : ∃ t : A, t ∈ maximalIdeal A ∧ (t : L) ≠ 0 ∧
        ∃ Q ∈ An₁.dom, Q.evalAt An₁.param = (t : L) * P₀.evalAt An₁.param := by
      by_cases hm'0 : (m' : L) = 0
      ·
        refine ⟨⟨_, hA₁⟩, hm₁, hne0, ?_⟩
        obtain ⟨Q, ⟨hQ, hQv⟩, -⟩ := An₁.existsUnique_evalAt_eq (⟨_, hA₁⟩ * ⟨_, hA₁⟩) (Ideal.mul_mem_left _ _ hm₁)
          (by push_cast; exact mul_ne_zero hne0 hne0) ⟨0, Ideal.zero_mem _, by rw [hmod, hm'0]; push_cast; ring⟩
        exact ⟨Q, hQ, by rw [hQv]; push_cast; ring⟩
      ·
        obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (m' : L) two_pos
        have htA : t ∈ A := by
          rw [← A.valuation_le_one_iff]
          have : A.valuation (t ^ 2) ≤ 1 := by rw [ht]; exact (A.valuation_le_one_iff _).2 m'.2
          rw [map_pow] at this
          by_contra hgt
          exact absurd this (not_le.mpr (one_lt_pow' (not_le.mp hgt) two_ne_zero))
        have htm : (⟨t, htA⟩ : A) ∈ maximalIdeal A := by
          apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem 2
          have : (⟨t, htA⟩ : A) ^ 2 = m' := Subtype.ext (by push_cast; exact ht)
          rw [this]; exact hm'
        have ht0 : t ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at ht; exact hm'0 ht.symm
        refine ⟨⟨t, htA⟩, htm, ht0, ?_⟩
        obtain ⟨Q, ⟨hQ, hQv⟩, -⟩ := An₁.existsUnique_evalAt_eq (⟨t, htA⟩ * ⟨_, hA₁⟩) (Ideal.mul_mem_left _ _ hm₁)
          (by push_cast; exact mul_ne_zero ht0 hne0)
          ⟨⟨t, htA⟩, htm, by rw [hmod, ← ht]; push_cast; ring⟩
        exact ⟨Q, hQ, by rw [hQv]; rfl⟩
    obtain ⟨t, htm, ht0, Q, hQ, hQv⟩ := hex
    obtain ⟨wP, hwP⟩ := hpow P₀ hP₀
    obtain ⟨wQ, hwQ⟩ := hpow Q hQ
    have hwP0 : ((wP : A) : L) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hwP
      exact (zpow_ne_zero _ (h1 P₀ hP₀).2.2) hwP

    apply false_of_zpow_eq_unit A t.2 htm hn (wQ * wP⁻¹)
    rw [hQv, mul_zpow, hwP] at hwQ
    have hwPinv : (((wP⁻¹ : Aˣ) : A) : L) = (((wP : A) : L))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel]; rfl
    rw [Units.val_mul, Subring.coe_mul, hwPinv, mul_inv_eq_iff_eq_mul₀ hwP0]
    apply mul_left_cancel₀ hc0
    linear_combination (-1 : L) * hwQ
  have ha_eq : a = 1 := Int.eq_one_of_mul_eq_one_right (by omega) ham

  have hsl1 : ∀ P ∈ An₁.dom, ∃ h : P.evalAt An₂.param * 1⁻¹ * (P.evalAt An₁.param) ^ (-(1 : ℤ)) ∈ A,
      IsUnit (⟨_, h⟩ : A) := by
    intro P hP
    have hsl' := hsl P hP
    rw [ha_eq] at hsl'
    obtain ⟨h, hu⟩ := hsl'
    exact ⟨by simpa only [inv_one, mul_one] using h, by simpa only [inv_one, mul_one] using hu⟩
  haveI : HasPrincipalDivisors L F := IsCurveOver.hasPrincipalDivisors
  have hval := AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit A An₁ An₂.param hz₂0 hord2 1 1 one_ne_zero hsl1
  have hmem : ∀ P ∈ An₁.dom, P.evalAt An₂.param * (P.evalAt An₁.param)⁻¹ ∈ A := by
    intro P hP
    obtain ⟨h, -⟩ := hsl1 P hP
    rwa [inv_one, mul_one, zpow_neg_one] at h
  have hunit : ∀ P (hP : P ∈ An₁.dom), IsUnit (⟨_, hmem P hP⟩ : A) := by
    intro P hP
    obtain ⟨h, hu⟩ := hsl1 P hP
    simpa only [inv_one, mul_one, zpow_neg_one] using hu
  refine ⟨residue A ⟨_, hmem P₀ hP₀⟩, ?_, fun P hP => ⟨hmem P hP, hunit P hP, ?_⟩⟩
  · exact ((hunit P₀ hP₀).map (residue A)).ne_zero
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    have := hval P P₀ hP hP₀
    simpa [zpow_neg_one] using this

end S_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne (solution)
