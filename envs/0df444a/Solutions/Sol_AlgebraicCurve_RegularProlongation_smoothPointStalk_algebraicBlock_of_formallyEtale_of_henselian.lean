-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c7ceb20e-d350-5935-a01b-dadaa4f5f0be

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_IsLocalRing_isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing
import Theorems.Thm_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated
import Theorems.Thm_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd
import Theorems.Thm_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)

    (K₁ : IntermediateField k₀ L) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A)
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)

    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁]
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)

    [IsLocalRing ↥S₁] (hmax : RingHom.ker χ₁ = maximalIdeal ↥S₁)

    (hφs : φ₁.FormallySmooth) (hφu : φ₁.FormallyUnramified) (hφf : φ₁.EssFiniteType)

    (hSR : ∀ f : ↥S₁, (f : F) ∈ R.integers)
    (hcen : ∀ f : ↥S₁, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ₁ (Polynomial.C ϖ) ∣ f) :
    letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra

    ∀ (F₀ : IntermediateField k₀ F)
      (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
      (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)),

    (∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c)) ∧

    (∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0) ∧
    maximalIdeal ↥S₁ = Ideal.span {φ₁ (Polynomial.C ϖ), φ₁ Polynomial.X} ∧

    IsNoetherianRing ↥S₁ ∧ UniqueFactorizationMonoid ↥S₁ ∧

    Prime (φ₁ (Polynomial.C ϖ)) ∧
    (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F))) ∧

    (∀ c : ↥A₁, IsLocalRing.residue ↥A ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ = 0 →
      ∃! χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) ∧
        χ (φ₁ Polynomial.X) = c) ∧
    (∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))}) ∧

    (∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x) ∧

    (∃ G : Finset F, ↑G ⊆ (S₁ : Set F) ∧ ∀ f ∈ S₁, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      (∃ u : (↥S₁)ˣ, ((u : ↥S₁) : F) = h) ∧ f * h = g) := by
  intro F₀ hgen hS₁F₁ hfrac
  classical

  let ιA : ↥A₁ →+* ↥A :=
    { toFun := fun a => ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hιA : ∀ a : ↥A₁, ιA a = ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩ := fun a => rfl
  have hιAinj : Function.Injective ιA := by
    intro a b h
    have h' : ((a : ↥K₁) : L) = ((b : ↥K₁) : L) := congrArg (fun z : ↥A => (z : L)) h
    exact Subtype.ext (Subtype.ext h')
  haveI hιAloc : IsLocalHom ιA := by
    refine ⟨fun a ha => ?_⟩
    have ha0 : ((a : ↥K₁) : L) ≠ 0 := by
      intro h0
      apply ha.ne_zero
      exact Subtype.ext h0

    obtain ⟨u, hu⟩ := ha
    have hinvA : ((a : ↥K₁) : L)⁻¹ ∈ A := by
      have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A) * ιA a = 1 := by rw [← hu, Units.inv_mul]
      have h2 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) * ((a : ↥K₁) : L) = 1 := by
        have := congrArg (fun z : ↥A => (z : L)) h1
        simp at this
        exact this
      have h3 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) = ((a : ↥K₁) : L)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [← h3]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
    have hinvK : ((a : ↥K₁) : L)⁻¹ ∈ K₁ := by
      rw [← show (((a : ↥K₁)⁻¹ : ↥K₁) : L) = ((a : ↥K₁) : L)⁻¹ from by simp]
      exact ((a : ↥K₁)⁻¹).2
    have hinvA₁ : ((a : ↥K₁))⁻¹ ∈ A₁ := by
      rw [hA₁]
      simpa using hinvA
    refine isUnit_iff_exists_inv.mpr ⟨⟨(a : ↥K₁)⁻¹, hinvA₁⟩, ?_⟩
    apply Subtype.ext
    show (a : ↥K₁) * (a : ↥K₁)⁻¹ = 1
    exact mul_inv_cancel₀ (fun h => ha0 (by rw [h]; simp))

  set κmap : ResidueField ↥A₁ →+* ResidueField ↥A := IsLocalRing.ResidueField.map ιA with hκmap
  have hκres : ∀ a : ↥A₁, κmap (IsLocalRing.residue ↥A₁ a) = IsLocalRing.residue ↥A (ιA a) :=
    fun a => IsLocalRing.ResidueField.map_residue ιA a
  have hκbij : Function.Bijective κmap := by
    refine ⟨κmap.injective, fun y => ?_⟩
    obtain ⟨a, ha⟩ := hκ₁ y
    exact ⟨IsLocalRing.residue ↥A₁ a, by rw [hκres]; exact ha⟩
  set ε : ResidueField ↥A₁ ≃+* ResidueField ↥A := RingEquiv.ofBijective κmap hκbij with hε
  have hεapp : ∀ z, ε z = κmap z := fun z => rfl

  set χ₀ : ↥S₁ →+* ResidueField ↥A₁ := ε.symm.toRingHom.comp χ₁ with hχ₀
  have hχ₀χ₁ : ∀ f : ↥S₁, κmap (χ₀ f) = χ₁ f := by
    intro f
    rw [← hεapp, hχ₀, RingHom.comp_apply]
    exact ε.apply_symm_apply _
  have hχ₀ker : RingHom.ker χ₀ = maximalIdeal ↥S₁ := by
    rw [← hmax]
    ext f
    simp only [RingHom.mem_ker]
    constructor
    · intro h; rw [← hχ₀χ₁, h, map_zero]
    · intro h; apply κmap.injective; rw [hχ₀χ₁, h, map_zero]
  have hχ₀C : ∀ a : ↥A₁, χ₀ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A₁ a := by
    intro a
    apply κmap.injective
    rw [hχ₀χ₁, hχC, hκres]
    rfl
  have hχ₀t : χ₀ (φ₁ Polynomial.X) = 0 := by
    apply κmap.injective
    rw [hχ₀χ₁, hχt, map_zero]

  have hres0 : ∀ c : ↥A₁,
      IsLocalRing.residue ↥A ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ = 0 ↔ IsLocalRing.residue ↥A₁ c = 0 := by
    intro c
    rw [← hιA, ← hκres]
    constructor
    · intro h; apply κmap.injective; rw [h, map_zero]
    · intro h; rw [h, map_zero]
  have hresχ : ∀ (χ : ↥S₁ →+* ↥A₁) (f : ↥S₁),
      IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f ↔
        IsLocalRing.residue ↥A₁ (χ f) = χ₀ f := by
    intro χ f
    rw [← hιA, ← hκres, ← hχ₀χ₁]
    exact ⟨fun h => κmap.injective h, fun h => by rw [h]⟩

  obtain ⟨hreg, hdim, hm2, hprime⟩ :=
    IsLocalRing.isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing
      ϖ hϖ φ₁ hφs hφu hφf χ₀ hχ₀ker hχ₀C hχ₀t
  haveI := hreg
  haveI hnoeth : IsNoetherianRing ↥S₁ := hreg.toIsNoetherian
  have hufd : UniqueFactorizationMonoid ↥S₁ :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two ↥S₁ hdim
  obtain ⟨hsec, hker⟩ :=
    HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
      φ₁ hφs hφu hφf χ₀ hχ₀ker hχ₀C hχ₀t
  have hbranch := HenselianLocalRing.forall_exists_monic_dvd_eval_of_prime_of_not_associated
      ϖ hϖ φ₁ hφf hm2 hprime χ₀ hχ₀ker hχ₀C
  have hRint := ValuationSubring.mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd
      S₁ (φ₁ (Polynomial.C ϖ)) hprime R.integers hSR hcen

  have hchart : ∀ c : ↥A₁, IsLocalRing.residue ↥A ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ = 0 →
      ∃! χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) ∧
        χ (φ₁ Polynomial.X) = c := by
    intro c hc
    have h := hsec c ((hres0 c).mp hc)
    simp only [hresχ]
    exact h
  have hkerG : ∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))} := by
    intro χ hχC hχres
    exact hker χ hχC (fun f => (hresχ χ f).mp (hχres f))

  have ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c) := by
    intro c heq
    have hϖm : IsLocalRing.residue ↥A₁ ϖ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self ϖ
    obtain ⟨χa, ⟨hχaC, -, hχat⟩, -⟩ := hsec 0 (by simp)
    obtain ⟨χb, ⟨hχbC, -, hχbt⟩, -⟩ := hsec ϖ hϖm
    have h1 : c = 0 := by rw [← hχaC c, ← heq, hχat]
    have h2 : c = ϖ := by rw [← hχbC c, ← heq, hχbt]
    exact hϖ0 (h2 ▸ h1)

  have hfg : ∃ G : Finset F, ↑G ⊆ (S₁ : Set F) ∧ ∀ f ∈ S₁, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      (∃ u : (↥S₁)ˣ, ((u : ↥S₁) : F) = h) ∧ f * h = g := by
    letI algφ : Algebra (Polynomial ↥A₁) ↥S₁ := φ₁.toAlgebra
    obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (self := hφf)
    set B : Subalgebra (Polynomial ↥A₁) ↥S₁ := Algebra.adjoin (Polynomial ↥A₁) (s : Set ↥S₁) with hB
    set G : Finset F := insert ((φ₁ Polynomial.X : ↥S₁) : F) (s.image (fun x : ↥S₁ => (x : F))) with hG
    set Cl : Subring F :=
      Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) with hCl

    have hφmem : ∀ p : Polynomial ↥A₁, ((φ₁ p : ↥S₁) : F) ∈ Cl := by
      intro p
      rw [p.as_sum_range_C_mul_X_pow, map_sum]
      push_cast
      refine Subring.sum_mem _ (fun i _ => ?_)
      rw [map_mul, map_pow]
      push_cast
      refine Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ _)
      · rw [hφC]
        exact Subring.subset_closure (Or.inr ⟨p.coeff i, Set.mem_univ _, rfl⟩)
      · exact Subring.subset_closure (Or.inl (by rw [hG]; exact Finset.mem_insert_self _ _))
    have hBmem : ∀ b : ↥S₁, b ∈ B → (b : F) ∈ Cl := by
      intro b hb
      rw [hB] at hb
      induction hb using Algebra.adjoin_induction with
      | mem x hx =>
        exact Subring.subset_closure (Or.inl (by
          rw [hG]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)))
      | algebraMap p => exact hφmem p
      | add x y _ _ hx hy => push_cast; exact Subring.add_mem _ hx hy
      | mul x y _ _ hx hy => push_cast; exact Subring.mul_mem _ hx hy
    refine ⟨G, ?_, ?_⟩
    · intro y hy
      rw [hG, Finset.coe_insert, Finset.coe_image] at hy
      rcases hy with rfl | ⟨x, -, rfl⟩
      · exact (φ₁ Polynomial.X).2
      · exact x.2
    · intro f hf
      obtain ⟨⟨g, h⟩, e⟩ := IsLocalization.surj
        (Submonoid.comap (algebraMap (↥B) ↥S₁) (IsUnit.submonoid ↥S₁)) (S := ↥S₁) ⟨f, hf⟩
      have hu : IsUnit ((h : ↥B) : ↥S₁) := h.2
      obtain ⟨u, hu⟩ := hu
      refine ⟨((g : ↥S₁) : F), (((h : ↥B) : ↥S₁) : F), hBmem _ g.2, hBmem _ (h : ↥B).2, ⟨u, by rw [hu]⟩, ?_⟩
      have e' := congrArg (fun z : ↥S₁ => (z : F)) e
      simpa using e'
  exact ⟨ht, fun f => by rw [← hmax, RingHom.mem_ker], hm2, hnoeth, hufd, hprime,
    fun f hf => hRint f (hfrac f hf), hchart, hkerG, hbranch, hfg⟩

end S_AlgebraicCurve_RegularProlongation_smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian (solution)
