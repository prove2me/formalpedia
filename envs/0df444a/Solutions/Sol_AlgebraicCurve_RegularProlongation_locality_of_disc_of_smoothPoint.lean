-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.locality_of_disc_of_smoothPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8fbfb4f1-a663-5236-923d-a6f710b8c394

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_locality_of_disc_of_smoothPoint

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace SPPDelta

theorem exists_eq_unit_mul_pow_of_forall_prime_dvd {S : Type*} [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]
    (ϖ : S) (hϖ : Prime ϖ) (x : S) (hx : x ≠ 0)
    (h : ∀ p : S, Prime p → p ∣ x → Associated p ϖ) :
    ∃ (n : ℕ) (u : Sˣ), x = (u : S) * ϖ ^ n := by
  obtain ⟨n, y, hy, rfl⟩ := WfDvdMonoid.max_power_factor hx hϖ.irreducible

  have hy0 : y ≠ 0 := fun h0 => hx (by rw [h0, mul_zero])
  have hyu : IsUnit y := by
    by_contra hyu
    obtain ⟨q, hqirr, hqy⟩ := WfDvdMonoid.exists_irreducible_factor hyu hy0
    have hq : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hqirr
    have hqx : q ∣ ϖ ^ n * y := hqy.trans (Dvd.intro_left _ rfl)
    have hqϖ : Associated q ϖ := h q hq hqx
    apply hy
    exact hqϖ.symm.dvd.trans hqy
  obtain ⟨u, rfl⟩ := hyu
  exact ⟨n, u, mul_comm _ _⟩

end SPPDelta

open SPPDelta AlgebraicCurve.GaussReduction in
theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F] [IsScalarTower k₀ L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (F₀ : IntermediateField k₀ F)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)

    (K₁ : IntermediateField k₀ L) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A) (D₁ : Set (Place L F))
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))

    (ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c))
    (hlocal : IsLocalRing ↥S₁) (hmax : ∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0)
    (hnoeth : IsNoetherianRing ↥S₁) (hufd : UniqueFactorizationMonoid ↥S₁)
    (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
    (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
    (hld : ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
      LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
    (hdvr : ∀ O : ValuationSubring F, (∀ x : L, algebraMap L F x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O)
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (hprime : Prime (φ₁ (Polynomial.C ϖ)))
    (hRint : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F)))

    (hker : ∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))})

    (hbranch : ∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x) :
    (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → f ≠ 0 → (∀ P ∈ D₁, P.ord f = 0) →
      ∃ (c : ↥K₁) (u : (↥S₁)ˣ), c ≠ 0 ∧ algebraMap L F (c : L) * f = ((u : ↥S₁) : F)) ∧
    (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → f ∈ R.integers → (∀ P ∈ D₁, f ∈ P.toValuationSubring) → f ∈ S₁) := by
  classical
  haveI := hlocal
  haveI := hnoeth
  haveI := hufd
  letI : GCDMonoid ↥S₁ := UniqueFactorizationMonoid.toGCDMonoid ↥S₁
  have hϖ₁ := hprime

  have key : ∀ (p : ↥S₁), Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) → ∀ (f : F) (g h : ↥S₁),
      f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      IsUnit (gcd g h) → f * (h : F) = (g : F) → (∀ P ∈ D₁, f ∈ P.toValuationSubring) → ¬ p ∣ h := by
    intro p hp hpϖ f g h hf hcop hfh hdisc hph
    obtain ⟨P, hPD, hPcen⟩ :=
      AlgebraicCurve.RegularProlongation.exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime
        F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch p hp hpϖ
    obtain ⟨p', hp', -, hcen', hval'⟩ :=
      AlgebraicCurve.RegularProlongation.exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc
        F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch P hPD
    have hpp' : p' ∣ p := (hcen' p).mp ((hPcen p).mpr dvd_rfl)
    have hp'h : p' ∣ h := hpp'.trans hph
    obtain ⟨g', h', hp'h', hfh'⟩ := (hval' f hf).mp (hdisc P hPD)
    have hgh : g * h' = g' * h := by
      apply Subtype.ext
      push_cast
      rw [← hfh, ← hfh']; ring
    have hp'g : p' ∣ g := by
      have : p' ∣ g * h' := hgh ▸ (hp'h.mul_left g')
      exact (hp'.dvd_or_dvd this).resolve_right hp'h'
    exact hp'.not_unit (isUnit_of_dvd_unit (dvd_gcd hp'g hp'h) hcop)

  have hcoprime : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → f ≠ 0 →
      ∃ g h : ↥S₁, g ≠ 0 ∧ h ≠ 0 ∧ IsUnit (gcd g h) ∧ f * (h : F) = (g : F) := by
    intro f hf hf0
    obtain ⟨g₀, h₀, hh₀, hfh₀⟩ := hfrac f hf
    have hh₀' : h₀ ≠ 0 := fun h0 => hh₀ (by rw [h0]; rfl)
    have hg₀ : g₀ ≠ 0 := by
      intro h0
      apply hf0
      have : f * (h₀ : F) = 0 := by rw [hfh₀, h0]; rfl
      exact (mul_eq_zero.mp this).resolve_right hh₀
    obtain ⟨g, h, hg, hh, hu⟩ := extract_gcd g₀ h₀
    have hd0 : gcd g₀ h₀ ≠ 0 := fun h0 => hg₀ (by rw [hg, h0, zero_mul])
    refine ⟨g, h, fun h0 => hg₀ (by rw [hg, h0, mul_zero]), fun h0 => hh₀' (by rw [hh, h0, mul_zero]), hu, ?_⟩
    have hdF : ((gcd g₀ h₀ : ↥S₁) : F) ≠ 0 := fun h0 => hd0 (Subtype.ext (by simpa using h0))
    have hhF : ((h₀ : ↥S₁) : F) = ((gcd g₀ h₀ : ↥S₁) : F) * (h : F) := by
      have := congrArg Subtype.val hh
      rwa [Subring.coe_mul] at this
    have hgF : ((g₀ : ↥S₁) : F) = ((gcd g₀ h₀ : ↥S₁) : F) * (g : F) := by
      have := congrArg Subtype.val hg
      rwa [Subring.coe_mul] at this
    apply mul_left_cancel₀ hdF
    calc ((gcd g₀ h₀ : ↥S₁) : F) * (f * (h : F)) = f * ((h₀ : ↥S₁) : F) := by rw [hhF]; ring
      _ = (g₀ : F) := hfh₀
      _ = ((gcd g₀ h₀ : ↥S₁) : F) * (g : F) := hgF
  refine ⟨fun f hf hf0 hord => ?_, fun f hf hR hdisc => ?_⟩
  ·
    have hdisc : ∀ P ∈ D₁, f ∈ P.toValuationSubring := fun P hP => mem_of_ord_nonneg_gen P hf0 (hord P hP).ge
    have hdisc' : ∀ P ∈ D₁, f⁻¹ ∈ P.toValuationSubring := fun P hP =>
      mem_of_ord_nonneg_gen P (inv_ne_zero hf0) (by rw [Place.ord_inv, hord P hP]; simp)
    obtain ⟨g, h, hg0, hh0, hcop, hfh⟩ := hcoprime f hf hf0
    have hf₁ : f⁻¹ ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ := inv_mem hf
    have hf'g : f⁻¹ * (g : F) = (h : F) := by
      rw [← hfh, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
    have hcop' : IsUnit (gcd h g) := (gcd_comm' h g).isUnit_iff.mpr hcop

    have hnoh : ∀ q : ↥S₁, Prime q → q ∣ h → Associated q (φ₁ (Polynomial.C ϖ)) := fun q hq hqh => by
      by_contra hqϖ; exact key q hq hqϖ f g h hf hcop hfh hdisc hqh
    have hnog : ∀ q : ↥S₁, Prime q → q ∣ g → Associated q (φ₁ (Polynomial.C ϖ)) := fun q hq hqg => by
      by_contra hqϖ; exact key q hq hqϖ f⁻¹ h g hf₁ hcop' hf'g hdisc' hqg
    obtain ⟨a, u, hu⟩ := exists_eq_unit_mul_pow_of_forall_prime_dvd _ hϖ₁ g hg0 hnog
    obtain ⟨b, w, hw⟩ := exists_eq_unit_mul_pow_of_forall_prime_dvd _ hϖ₁ h hh0 hnoh

    have hϖK0 : ((ϖ : ↥A₁) : ↥K₁) ≠ 0 := fun h0 => hϖ0 (Subtype.ext h0)
    refine ⟨((ϖ : ↥A₁) : ↥K₁) ^ b * (((ϖ : ↥A₁) : ↥K₁) ^ a)⁻¹, u * w⁻¹,
      mul_ne_zero (pow_ne_zero _ hϖK0) (inv_ne_zero (pow_ne_zero _ hϖK0)), ?_⟩
    have hϖF : ((φ₁ (Polynomial.C ϖ) : ↥S₁) : F) = algebraMap L F (((ϖ : ↥A₁) : ↥K₁) : L) := hφC ϖ
    have hϖF0 : algebraMap L F (((ϖ : ↥A₁) : ↥K₁) : L) ≠ 0 := by
      rw [← hϖF]; exact fun h0 => hϖ₁.ne_zero (Subtype.ext (by simpa using h0))
    have hhF : (h : F) ≠ 0 := fun h0 => hh0 (Subtype.ext (by simpa using h0))
    have hfeq : f = (g : F) * (h : F)⁻¹ := by rw [← hfh, mul_inv_cancel_right₀ hhF]
    have hwinv : (((w⁻¹ : (↥S₁)ˣ) : ↥S₁) : F) = ((((w : (↥S₁)ˣ) : ↥S₁) : F))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by
        rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, OneMemClass.coe_one])
    set x : F := algebraMap L F (((ϖ : ↥A₁) : ↥K₁) : L) with hx
    have hcF : algebraMap L F ((( ((ϖ : ↥A₁) : ↥K₁) ^ b * (((ϖ : ↥A₁) : ↥K₁) ^ a)⁻¹ : ↥K₁) : L)) = x ^ b * (x ^ a)⁻¹ := by
      rw [hx]
      simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_inv, map_mul, map_pow,
        map_inv₀]
    have hx0 : x ≠ 0 := by rw [hx]; exact hϖF0
    have hw0 : (((w : (↥S₁)ˣ) : ↥S₁) : F) ≠ 0 := fun h0 => w.ne_zero (Subtype.ext (by simpa using h0))
    have hgF' : ((g : ↥S₁) : F) = (((u : (↥S₁)ˣ) : ↥S₁) : F) * x ^ a := by
      have := congrArg Subtype.val hu
      rw [Subring.coe_mul, SubmonoidClass.coe_pow, hϖF] at this
      exact this
    have hhF' : ((h : ↥S₁) : F) = (((w : (↥S₁)ˣ) : ↥S₁) : F) * x ^ b := by
      have := congrArg Subtype.val hw
      rw [Subring.coe_mul, SubmonoidClass.coe_pow, hϖF] at this
      exact this
    rw [hcF, hfeq, hgF', hhF', Units.val_mul, Subring.coe_mul, hwinv]
    field_simp
  ·
    by_cases hf0 : f = 0
    · rw [hf0]; exact S₁.zero_mem
    obtain ⟨g, h, hg0, hh0, hcop, hfh⟩ := hcoprime f hf hf0
    obtain ⟨g₁, h₁, hϖh₁, hfh₁⟩ := (hRint f hf).mp hR

    have hϖh : ¬ φ₁ (Polynomial.C ϖ) ∣ h := by
      intro hdvd
      have hgh : g * h₁ = g₁ * h := by
        apply Subtype.ext; push_cast; rw [← hfh, ← hfh₁]; ring
      have : φ₁ (Polynomial.C ϖ) ∣ g := by
        have : φ₁ (Polynomial.C ϖ) ∣ g * h₁ := hgh ▸ hdvd.mul_left g₁
        exact (hϖ₁.dvd_or_dvd this).resolve_right hϖh₁
      exact hϖ₁.not_unit (isUnit_of_dvd_unit (dvd_gcd this hdvd) hcop)

    have hhu : IsUnit h := by
      by_contra hnu
      obtain ⟨q, hqirr, hqh⟩ := WfDvdMonoid.exists_irreducible_factor hnu hh0
      have hq : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hqirr
      by_cases hqϖ : Associated q (φ₁ (Polynomial.C ϖ))
      · exact hϖh (hqϖ.symm.dvd.trans hqh)
      · exact key q hq hqϖ f g h hf hcop hfh hdisc hqh
    obtain ⟨w, rfl⟩ := hhu
    have hwF : ((w : ↥S₁) : F) ≠ 0 := fun h0 => hh0 (Subtype.ext (by simpa using h0))
    have : f = ((g * (w⁻¹ : (↥S₁)ˣ) : ↥S₁) : F) := by
      rw [← mul_inv_cancel_right₀ hwF f, hfh]
      push_cast
      congr 1
      exact (eq_inv_of_mul_eq_one_left (by
        rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, OneMemClass.coe_one])).symm
    rw [this]; exact SetLike.coe_mem _

end S_AlgebraicCurve_RegularProlongation_locality_of_disc_of_smoothPoint
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_locality_of_disc_of_smoothPoint (solution)
