-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.forall_mem_and_isUnit_iff_of_mem_packageDisc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d2dea29b-6557-5ca1-8d37-76a9ace65875

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (S : Subring F) (φT : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A) (Dp : Set (Place L F))
    (hpk :
            (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
            (φT).FormallySmooth ∧ (φT).FormallyUnramified ∧
            (∀ a : ↥A, ((φT (Polynomial.C a) : ↥(S)) : F) = algebraMap L F (a : L)) ∧
            (∀ a : ↥A, χ₀ (φT (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φT Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φT Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φT Polynomial.X : ↥(S)) : F) ∈ R.integers,
              Q.ord (R.residue ⟨((φT Polynomial.X : ↥(S)) : F), hR⟩) = 1) ∧
            (∀ P, P ∈ Dp ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ Dp ∧ ∀ f : ↥(S), P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
            (∀ P ∈ Dp, ∀ f : F, f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
            (∀ f : F, f ≠ 0 → (∀ P ∈ Dp, P.ord f = 0) →
              ∃ (c : L) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥(S)) : F)) ∧
            (∀ f : F, f ∈ R.integers → (∀ P ∈ Dp, f ∈ P.toValuationSubring) → f ∈ S))
    (P : Place L F) (hP : P ∈ Dp) :
    ∀ f : F, f ∈ S → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
      (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ S, f * g = 1) := by
  classical
  obtain ⟨hA_S, -, -, hC, hχC, -, -, -, -, hDp, -, -, h13, -⟩ := hpk
  obtain ⟨hPrat, hreg, hval⟩ := (hDp P).mp hP
  intro f hfS
  set fS : ↥S := ⟨f, hfS⟩ with hfSdef
  have hfreg : f ∈ P.toValuationSubring := (hreg fS).1
  have hfA : P.evalAt f ∈ A := (hreg fS).2
  refine ⟨hfreg, hfA, ?_⟩

  have hunit_iff : IsUnit (⟨P.evalAt f, hfA⟩ : ↥A) ↔ χ₀ fS ≠ 0 := by
    rw [ValuationSubring.valuation_eq_one_iff]
    constructor
    · intro h1 h0
      have hlt := (hval fS).mpr h0
      have : A.valuation (P.evalAt f) = 1 := h1
      rw [this] at hlt
      exact lt_irrefl _ hlt
    · intro hn
      exact le_antisymm (A.valuation_le_one ⟨P.evalAt f, hfA⟩) (not_lt.mp (fun hlt => hn ((hval fS).mp hlt)))
  rw [hunit_iff]
  constructor
  ·
    intro hχ
    have hf0 : f ≠ 0 := by
      intro h0
      apply hχ
      have : fS = 0 := Subtype.ext h0
      rw [this, map_zero]

    have hord : ∀ P' ∈ Dp, P'.ord f = 0 := by
      intro P' hP'
      obtain ⟨hP'rat, hreg', hval'⟩ := (hDp P').mp hP'
      have hfreg' : f ∈ P'.toValuationSubring := (hreg' fS).1
      have hfA' : P'.evalAt f ∈ A := (hreg' fS).2
      have hne : P'.evalAt f ≠ 0 := by
        intro h0
        apply hχ
        apply (hval' fS).mp
        show A.valuation (P'.evalAt f) < 1
        rw [h0, map_zero]; exact zero_lt_one
      have hres : IsLocalRing.residue P'.toValuationSubring ⟨f, hfreg'⟩ ≠ 0 := by
        rw [← P'.algebraMap_evalAt hP'rat hfreg']
        exact (map_ne_zero _).mpr hne
      have hu : IsUnit (⟨f, hfreg'⟩ : P'.toValuationSubring) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
      have h0 := P'.ord_coe_unit hu.unit
      rwa [IsUnit.unit_spec] at h0
    obtain ⟨c, u, hc0, hcu⟩ := h13 f hf0 hord

    have hcA : c ∈ A := by
      by_contra hcA
      have hc'A : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hnu : ¬ IsUnit (⟨c⁻¹, hc'A⟩ : ↥A) := by
        intro hu
        obtain ⟨w, hw⟩ := hu
        apply hcA
        have h1 : ((w⁻¹ : (↥A)ˣ) : ↥A) * (w : ↥A) = 1 := Units.inv_mul w
        have h2 : (((w⁻¹ : (↥A)ˣ) : ↥A) : L) * c⁻¹ = 1 := by
          have := congrArg (fun x : ↥A => (x : L)) h1
          simpa [hw] using this
        have h3 : (((w⁻¹ : (↥A)ˣ) : ↥A) : L) = c := (mul_inv_eq_one₀ hc0).mp h2
        rw [← h3]; exact ((w⁻¹ : (↥A)ˣ) : ↥A).2
      have hres0 : IsLocalRing.residue ↥A ⟨c⁻¹, hc'A⟩ = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
      apply hχ

      have hfeq : fS = φT (Polynomial.C ⟨c⁻¹, hc'A⟩) * (u : ↥S) := by
        apply Subtype.ext
        show f = ((φT (Polynomial.C ⟨c⁻¹, hc'A⟩) : ↥S) : F) * ((u : ↥S) : F)
        rw [hC, ← hcu, ← mul_assoc, ← map_mul]
        show f = algebraMap L F (c⁻¹ * c) * f
        rw [inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [hfeq, map_mul, hχC, hres0, zero_mul]

    refine ⟨((φT (Polynomial.C ⟨c, hcA⟩) : ↥S) : F) * (((u⁻¹ : (↥S)ˣ) : ↥S) : F), ?_, ?_⟩
    · exact S.mul_mem (φT (Polynomial.C ⟨c, hcA⟩)).2 ((u⁻¹ : (↥S)ˣ) : ↥S).2
    · rw [hC, ← mul_assoc, mul_comm f, hcu]
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  ·
    rintro ⟨g, hgS, hfg⟩ h0
    have : fS * ⟨g, hgS⟩ = 1 := Subtype.ext hfg
    have h1 := congrArg χ₀ this
    rw [map_mul, map_one, h0, zero_mul] at h1
    exact zero_ne_one h1

end S_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc (solution)
