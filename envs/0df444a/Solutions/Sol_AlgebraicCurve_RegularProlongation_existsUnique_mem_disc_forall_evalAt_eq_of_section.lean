-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.existsUnique_mem_disc_forall_evalAt_eq_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8525c795-ca64-5163-ae07-290dfcb60d4d

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime
import Theorems.Thm_AlgebraicCurve_Place_existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_mem_disc_forall_evalAt_eq_of_section
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 6400000 in
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
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x)
    (χ : ↥S₁ →+* ↥A₁) (hχa : ∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a)
    (hχres : ∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) :
    ∃! P, P ∈ D₁ ∧ ∀ f : ↥S₁, P.evalAt (f : F) = ((χ f : ↥K₁) : L) := by
  classical
  haveI := hlocal

  have ev_add : ∀ (P : Place L F), P.IsRational → ∀ {f g : F}, f ∈ P.toValuationSubring → g ∈ P.toValuationSubring →
      P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
    intro P hP f g hf hg
    apply P.algebraMap_residueField_injective
    rw [map_add, P.algebraMap_evalAt hP (add_mem hf hg), P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg, ← map_add]
    rfl
  have ev_neg : ∀ (P : Place L F), P.IsRational → ∀ {f : F}, f ∈ P.toValuationSubring → P.evalAt (-f) = -P.evalAt f := by
    intro P hP f hf
    apply P.algebraMap_residueField_injective
    rw [map_neg, P.algebraMap_evalAt hP (neg_mem hf), P.algebraMap_evalAt hP hf, ← map_neg]
    rfl
  have ev_sub : ∀ (P : Place L F), P.IsRational → ∀ {f g : F}, f ∈ P.toValuationSubring → g ∈ P.toValuationSubring →
      P.evalAt (f - g) = P.evalAt f - P.evalAt g := by
    intro P hP f g hf hg
    rw [sub_eq_add_neg, ev_add P hP hf (neg_mem hg), ev_neg P hP hg, ← sub_eq_add_neg]
  have ev_zero_iff : ∀ (P : Place L F), P.IsRational → ∀ {f : F} (hf : f ∈ P.toValuationSubring),
      P.evalAt f = 0 ↔ (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring := by
    intro P hP f hf
    rw [← IsLocalRing.residue_eq_zero_iff, ← P.algebraMap_evalAt hP hf, map_eq_zero_iff _ P.algebraMap_residueField_injective]
  have ev_const : ∀ (P : Place L F) (x : L), algebraMap L F x ∈ P.toValuationSubring ∧ P.evalAt (algebraMap L F x) = x :=
    fun P x => ⟨P.algebraMap_mem' x, AlgebraicCurve.Place.evalAt_algebraMap P x⟩

  set c : ↥A₁ := χ (φ₁ Polynomial.X) with hcdef
  set p : ↥S₁ := φ₁ Polynomial.X - φ₁ (Polynomial.C c) with hpdef
  have hkerχ : RingHom.ker χ = Ideal.span {p} := hker χ hχa hχres
  have hp0 : p ≠ 0 := sub_ne_zero.mpr (ht c)
  have hp : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hkerχ]
    exact RingHom.ker_isPrime χ
  have hdvdχ : ∀ f : ↥S₁, p ∣ f ↔ χ f = 0 := by
    intro f
    rw [← Ideal.mem_span_singleton, ← hkerχ, RingHom.mem_ker]
  have hpϖ : ¬ Associated p (φ₁ (Polynomial.C ϖ)) := by
    intro h
    have h1 : p ∣ φ₁ (Polynomial.C ϖ) := h.dvd
    rw [hdvdχ, hχa] at h1
    exact hϖ0 h1

  obtain ⟨P, hPD, hPp⟩ := AlgebraicCurve.RegularProlongation.exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime
    F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch p hp hpϖ
  obtain ⟨hPrat, hPS, hPker⟩ := (hD P).mp hPD
  have hval : ∀ f : ↥S₁, P.evalAt (f : F) = ((χ f : ↥K₁) : L) := by
    intro f
    have h1 : p ∣ (f - φ₁ (Polynomial.C (χ f))) := by
      rw [hdvdχ, map_sub, hχa, sub_self]
    have h2 := (hPp (f - φ₁ (Polynomial.C (χ f)))).mpr h1
    have h3 : ((f - φ₁ (Polynomial.C (χ f)) : ↥S₁) : F) = (f : F) - algebraMap L F ((χ f : ↥K₁) : L) := by
      push_cast; rw [hφC]
    rw [h3, ev_sub P hPrat (hPS f).1 (ev_const P _).1, (ev_const P _).2, sub_eq_zero] at h2
    exact h2
  refine ⟨P, ⟨hPD, hval⟩, ?_⟩

  rintro P' ⟨hP'D, hP'v⟩
  obtain ⟨hP'rat, hP'S, hP'ker⟩ := (hD P').mp hP'D
  have hcoe0 : ∀ f : ↥S₁, ((χ f : ↥K₁) : L) = 0 ↔ χ f = 0 := by
    intro f
    constructor
    · intro h; apply Subtype.ext; apply Subtype.ext; exact h
    · intro h; rw [h]; rfl
  have hz' : ∀ f : ↥S₁, P'.evalAt (f : F) = 0 ↔ p ∣ f := by
    intro f; rw [hP'v f, hcoe0, hdvdχ]

  obtain ⟨p₁, hp₁, -, hp₁z, hp₁tr⟩ :=
    AlgebraicCurve.RegularProlongation.exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch P hPD
  obtain ⟨p₂, hp₂, -, hp₂z, hp₂tr⟩ :=
    AlgebraicCurve.RegularProlongation.exists_prime_forall_evalAt_eq_zero_iff_dvd_of_mem_disc F₀ hgen A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ D₁ hAS hφC hχC hχt hD ht hlocal hmax hnoeth hufd hS₁F₁ hfrac hld hdvr ϖ hϖ hϖ0 hprime hRint hker hbranch P' hP'D
  have hd₁ : ∀ f : ↥S₁, p₁ ∣ f ↔ p ∣ f := fun f => by rw [← hp₁z, hPp]
  have hd₂ : ∀ f : ↥S₁, p₂ ∣ f ↔ p ∣ f := fun f => by rw [← hp₂z, hz']
  have htr : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ P.toValuationSubring ↔ ∃ g h : ↥S₁, ¬ p ∣ h ∧ f * (h : F) = (g : F)) := by
    intro f hf; rw [hp₁tr f hf]; simp only [hd₁]
  have htr' : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ P'.toValuationSubring ↔ ∃ g h : ↥S₁, ¬ p ∣ h ∧ f * (h : F) = (g : F)) := by
    intro f hf; rw [hp₂tr f hf]; simp only [hd₂]

  set FL : IntermediateField k₀ F := IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ with hFLdef
  let V₁ : ValuationSubring ↥FL := P.toValuationSubring.comap (algebraMap ↥FL F)
  have memV : ∀ x : ↥FL, x ∈ V₁ ↔ (x : F) ∈ P.toValuationSubring := fun x => ValuationSubring.mem_comap
  have hconstFL : ∀ x : ↥K₁, algebraMap L F (x : L) ∈ FL := fun x =>
    (le_sup_left : _ ≤ FL) (IntermediateField.subset_adjoin k₀ _ ⟨(x : L), x.2, rfl⟩)
  have hmemS_P : ∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring := fun f => (hPS f).1
  have hne0 : ∀ h : ↥S₁, ¬ p ∣ h → (h : F) ≠ 0 := by
    intro h hh h0
    apply hh
    have : h = 0 := Subtype.ext h0
    rw [this]; exact dvd_zero p
  have hχne0 : ∀ h : ↥S₁, ¬ p ∣ h → ((χ h : ↥K₁) : L) ≠ 0 := by
    intro h hh h0; exact hh ((hdvdχ h).mpr ((hcoe0 h).mp h0))

  have hfracV : ∀ v : ↥V₁, ∃ g h : ↥S₁, ¬ p ∣ h ∧ ((v : ↥FL) : F) * (h : F) = (g : F) := by
    intro v
    exact (htr _ v.1.2).mp ((memV _).mp v.2)
  have hK₁V : ∀ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ FL), (⟨algebraMap L F (x : L), hx⟩ : ↥FL) ∈ V₁ :=
    fun x hx => (memV _).mpr (ev_const P _).1

  have hpFL : ((p : ↥S₁) : F) ∈ FL := hS₁F₁ _ p.2
  have hpV : (⟨(p : F), hpFL⟩ : ↥FL) ∈ V₁ := (memV _).mpr (hPS p).1
  set pV : ↥V₁ := ⟨⟨(p : F), hpFL⟩, hpV⟩ with hpVdef
  haveI : IsDiscreteValuationRing ↥V₁ := by

    have hSFL : ∀ s : ↥S₁, ((s : ↥S₁) : F) ∈ FL := fun s => hS₁F₁ _ s.2
    have mkV_mem : ∀ (g h : ↥S₁), ¬ p ∣ h → ∃ w : ↥V₁, ((w : ↥FL) : F) = (g : F) / (h : F) := by
      intro g h hh
      have hFLmem : (g : F) / (h : F) ∈ FL := div_mem (hSFL g) (hSFL h)
      have hPmem : (g : F) / (h : F) ∈ P.toValuationSubring :=
        (htr _ hFLmem).mpr ⟨g, h, hh, by rw [div_mul_cancel₀ _ (hne0 h hh)]⟩
      exact ⟨⟨⟨_, hFLmem⟩, (memV _).mpr hPmem⟩, rfl⟩
    have hcoeV_inj : ∀ w w' : ↥V₁, ((w : ↥FL) : F) = ((w' : ↥FL) : F) → w = w' :=
      fun w w' h => Subtype.ext (Subtype.ext h)
    have hcoeV_mul : ∀ w w' : ↥V₁, (((w * w' : ↥V₁) : ↥FL) : F) = ((w : ↥FL) : F) * ((w' : ↥FL) : F) := fun _ _ => rfl
    have hcoeV_one : (((1 : ↥V₁) : ↥FL) : F) = 1 := rfl
    have hcoeV_pow : ∀ (w : ↥V₁) (n : ℕ), (((w ^ n : ↥V₁) : ↥FL) : F) = (((w : ↥FL) : F)) ^ n := by
      intro w n; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, hcoeV_mul, ih, pow_succ]

    have unitV : ∀ (g h : ↥S₁), ¬ p ∣ g → ¬ p ∣ h → ∀ w : ↥V₁, ((w : ↥FL) : F) = (g : F) / (h : F) → IsUnit w := by
      intro g h hg hh w hw
      obtain ⟨w', hw'⟩ := mkV_mem h g hg
      refine isUnit_iff_exists_inv.mpr ⟨w', hcoeV_inj _ _ ?_⟩
      rw [hcoeV_mul, hw, hw', hcoeV_one, div_mul_div_comm, mul_comm ((h : ↥S₁) : F) ((g : ↥S₁) : F),
        div_self (mul_ne_zero (hne0 g hg) (hne0 h hh))]

    have hpV_nu : ¬ IsUnit pV := by
      intro hu
      obtain ⟨u, hu⟩ := hu
      have hinvP : ((p : ↥S₁) : F)⁻¹ ∈ P.toValuationSubring := by
        have e2 : ((((u⁻¹ : (↥V₁)ˣ) : ↥V₁) : ↥FL) : F) * (((u : ↥V₁) : ↥FL) : F) = 1 := by
          rw [← hcoeV_mul, u.inv_mul]; rfl
        have e3 : (((u : ↥V₁) : ↥FL) : F) = (p : F) := by rw [hu]
        rw [← e3, ← eq_inv_of_mul_eq_one_left e2]
        exact (memV _).mp ((u⁻¹ : (↥V₁)ˣ) : ↥V₁).2
      have hpinvFL : ((p : ↥S₁) : F)⁻¹ ∈ FL := inv_mem (hSFL p)
      obtain ⟨g, h, hh, hgh⟩ := (htr _ hpinvFL).mp hinvP
      apply hh
      have hp0F : ((p : ↥S₁) : F) ≠ 0 := fun h0 => hp0 (Subtype.ext h0)
      have : (h : F) = (p : F) * (g : F) := by
        rw [← hgh, ← mul_assoc, mul_inv_cancel₀ hp0F, one_mul]
      exact ⟨g, Subtype.ext (by push_cast; exact this)⟩

    have hfact : ∀ {w : ↥V₁}, w ≠ 0 → ∃ n : ℕ, Associated (pV ^ n) w := by
      intro w hw0
      obtain ⟨g, h, hh, hgh⟩ := hfracV w
      have hg0 : g ≠ 0 := by
        intro h0
        apply hw0
        apply hcoeV_inj
        have : ((w : ↥FL) : F) = 0 := by
          have := hgh; rw [h0] at this
          exact (mul_eq_zero.mp (by simpa using this)).resolve_right (hne0 h hh)
        rw [this]; rfl
      obtain ⟨n, g', hg', hgeq⟩ := WfDvdMonoid.max_power_factor hg0 hp.irreducible
      obtain ⟨u, hu⟩ := mkV_mem g' h hh
      have huU := unitV g' h hg' hh u hu
      refine ⟨n, ⟨huU.unit, hcoeV_inj _ _ ?_⟩⟩
      rw [hcoeV_mul, hcoeV_pow, IsUnit.unit_spec, hu]
      show ((p : F)) ^ n * ((g' : F) / (h : F)) = ((w : ↥FL) : F)
      have hw' : ((w : ↥FL) : F) = (g : F) / (h : F) := by
        rw [eq_div_iff (hne0 h hh)]; exact hgh
      have hgeq' : ((g : ↥S₁) : F) = ((p : ↥S₁) : F) ^ n * (g' : F) := by
        rw [hgeq]; push_cast; rfl
      rw [hw', hgeq', mul_div_assoc]

    have hpV0 : pV ≠ 0 := by
      intro h0; apply hp0; apply Subtype.ext
      have := congrArg (fun z : ↥V₁ => ((z : ↥FL) : F)) h0
      exact this
    have hirr : Irreducible pV := by
      refine ⟨hpV_nu, fun a b hab => ?_⟩
      have ha0 : a ≠ 0 := by intro h; apply hpV0; rw [hab, h, zero_mul]
      have hb0 : b ≠ 0 := by intro h; apply hpV0; rw [hab, h, mul_zero]
      obtain ⟨i, hua⟩ := hfact ha0
      obtain ⟨j, hub⟩ := hfact hb0

      have key : Associated (pV ^ (i + j)) pV := by
        have := hua.mul_mul hub
        rwa [← pow_add, ← hab] at this
      rcases Nat.lt_or_ge (i + j) 1 with hlt | hge
      · have hij : i + j = 0 := by omega
        rw [hij, pow_zero] at key
        exact absurd ((associated_one_iff_isUnit).mp key.symm) hpV_nu
      · rcases Nat.lt_or_ge (i + j) 2 with hlt2 | hge2
        · have hij : i + j = 1 := by omega
          rcases Nat.eq_zero_or_pos i with hi | hi
          · left; rw [hi, pow_zero] at hua; exact (associated_one_iff_isUnit).mp hua.symm
          · right
            have hj : j = 0 := by omega
            rw [hj, pow_zero] at hub; exact (associated_one_iff_isUnit).mp hub.symm
        · exfalso
          apply hpV_nu
          obtain ⟨u, hu⟩ := key

          have : pV * (pV ^ (i + j - 1) * (u : ↥V₁)) = pV * 1 := by
            rw [mul_one, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ i + j), hu]
          have h2 := mul_left_cancel₀ hpV0 this
          have h3 : pV * (pV ^ (i + j - 2) * (u : ↥V₁)) = 1 := by
            rw [← mul_assoc, ← pow_succ', show i + j - 2 + 1 = i + j - 1 by omega, h2]
          exact isUnit_iff_exists_inv.mpr ⟨_, h3⟩
    exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨pV, hirr, hfact⟩
  have hrat : ∀ v : ↥V₁, ∃ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ FL), v - ⟨⟨algebraMap L F (x : L), hx⟩, hK₁V x hx⟩ ∈ maximalIdeal ↥V₁ := by
    intro v
    obtain ⟨g, h, hh, hvh⟩ := hfracV v
    set x : ↥K₁ := (χ g : ↥K₁) * ((χ h : ↥K₁))⁻¹ with hxdef
    refine ⟨x, hconstFL x, ?_⟩

    have hvP : ((v : ↥FL) : F) ∈ P.toValuationSubring := (memV _).mp v.2
    have hev : P.evalAt ((v : ↥FL) : F) = (x : L) := by
      have h1 := AlgebraicCurve.Place.evalAt_mul P hPrat hvP (hmemS_P h)
      rw [hvh, hval g, hval h] at h1

      have h2 : ((χ h : ↥K₁) : L) ≠ 0 := hχne0 h hh
      rw [hxdef]; push_cast
      field_simp
      rw [h1]

    have hreg : ((v : ↥FL) : F) - algebraMap L F (x : L) ∈ P.toValuationSubring := sub_mem hvP (ev_const P _).1
    have hzero : P.evalAt (((v : ↥FL) : F) - algebraMap L F (x : L)) = 0 := by
      rw [ev_sub P hPrat hvP (ev_const P _).1, (ev_const P _).2, hev, sub_self]
    have hmax' := (ev_zero_iff P hPrat hreg).mp hzero

    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax'
    obtain ⟨u, hu'⟩ := hu
    have hinv : (((v : ↥FL) : F) - algebraMap L F (x : L))⁻¹ ∈ P.toValuationSubring := by
      have e1 : (((u⁻¹ : (↥V₁)ˣ) : ↥V₁) : ↥FL) * ((u : ↥V₁) : ↥FL) = 1 := congrArg Subtype.val u.inv_mul
      have e2 : ((((u⁻¹ : (↥V₁)ˣ) : ↥V₁) : ↥FL) : F) * (((u : ↥V₁) : ↥FL) : F) = 1 := by
        have := congrArg (fun z : ↥FL => (z : F)) e1; push_cast at this; exact this
      have e3 : (((u : ↥V₁) : ↥FL) : F) = ((v : ↥FL) : F) - algebraMap L F (x : L) := by
        rw [hu']; rfl
      rw [← e3, ← eq_inv_of_mul_eq_one_left e2]
      exact (memV _).mp ((u⁻¹ : (↥V₁)ˣ) : ↥V₁).2
    have hne : ((v : ↥FL) : F) - algebraMap L F (x : L) ≠ 0 := by
      intro h0
      apply u.ne_zero
      apply Subtype.ext; apply Subtype.ext
      show (((u : ↥V₁) : ↥FL) : F) = (((0 : ↥V₁) : ↥FL) : F)
      rw [hu']
      exact h0
    exact ⟨⟨⟨_, hreg⟩, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩
  obtain ⟨huniq, -⟩ := AlgebraicCurve.Place.existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem
    F₀ K₁ hgen halg V₁ hK₁V hrat
  have hPtr : ∀ f : ↥FL, (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁ := fun f => (memV f).symm
  have hP'tr : ∀ f : ↥FL, (f : F) ∈ P'.toValuationSubring ↔ f ∈ V₁ := by
    intro f; rw [memV, htr' (f : F) f.2, htr (f : F) f.2]
  exact huniq.unique hP'tr hPtr

end S_AlgebraicCurve_RegularProlongation_existsUnique_mem_disc_forall_evalAt_eq_of_section
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_existsUnique_mem_disc_forall_evalAt_eq_of_section (solution)
