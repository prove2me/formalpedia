-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_smoothPointStalks_tower_of_base
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/236caae1-2573-50db-9d8a-73e3b017cd4a

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_RegularProlongation_smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_smoothPointStalk_baseChange_layer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalks_tower_of_base
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 12800000 in
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
    (hcen : ∀ f : ↥S₁, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ₁ (Polynomial.C ϖ) ∣ f)
    (Q : Place (ResidueField ↥A) Fbar)
    (hK₁ : FiniteDimensional k₀ ↥K₁)

    (D₁ : Set (Place L F))
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))
    (hres : ∀ f : ↥S₁, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₁ f))
    (hordQ : ∃ hR : ((φ₁ Polynomial.X : ↥S₁) : F) ∈ R.integers,
      Q.ord (R.residue ⟨((φ₁ Polynomial.X : ↥S₁) : F), hR⟩) = 1)

    {ι : Type} (K : ι → IntermediateField k₀ L) (hKle : ∀ n, K₁ ≤ K n) (hKfin : ∀ n, FiniteDimensional k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : L) ∈ A)
    (hκn : ∀ n, Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩))
    (hdvrn : ∀ n, IsDiscreteValuationRing ↥(An n)) (hhensn : ∀ n, HenselianLocalRing ↥(An n)) :
    letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra
    ∀ (F₀ : IntermediateField k₀ F)
      (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
      (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
      (hLD : ∀ (K' : IntermediateField k₀ L), FiniteDimensional k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K' : Set L)) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0),
    ∃ (Sn : ι → Subring F) (φn : ∀ n, Polynomial ↥(An n) →+* ↥(Sn n)) (χn : ∀ n, ↥(Sn n) →+* ResidueField ↥A),

      (∃ hmono₁ : ∀ n, S₁ ≤ Sn n,
        (∀ n, Sn n ≤ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ))) ∧
        (∀ n, ((φ₁ Polynomial.X : ↥S₁) : F) = ((φn n Polynomial.X : ↥(Sn n)) : F)) ∧
        (∀ n (f : ↥S₁), χn n ⟨(f : F), hmono₁ n f.2⟩ = χ₁ f)) ∧
            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap L F ((a : ↥(K n)) : L) ∈ Sn n) ∧

              (φn n).FormallySmooth ∧ (φn n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn n (Polynomial.C a) : ↥(Sn n)) : F) = algebraMap L F ((a : ↥(K n)) : L)) ∧

              (∀ a : ↥(An n), χn n (φn n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩) ∧

              χn n (φn n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : L), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : L), (hAn n _).mp (χ f).2⟩ = χn n f) ∧
                  χ (φn n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn n), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn n f)) ∧

              (∃ hR : ((φn n Polynomial.X : ↥(Sn n)) : F) ∈ R.integers,
                Q.ord (R.residue ⟨((φn n Polynomial.X : ↥(Sn n)) : F), hR⟩) = 1) ∧

              (∀ P, P ∈ D₁ ↔ (P.IsRational ∧
                (∀ f : ↥(Sn n), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
                (∀ f : ↥(Sn n), A.valuation (P.evalAt (f : F)) < 1 ↔ χn n f = 0))) ∧

              (∀ c : ↥(An n), φn n Polynomial.X ≠ φn n (Polynomial.C c)) ∧

              (∃ _ : IsLocalRing ↥(Sn n), ∀ f : ↥(Sn n), f ∈ IsLocalRing.maximalIdeal ↥(Sn n) ↔ χn n f = 0) ∧

              IsNoetherianRing ↥(Sn n) ∧ UniqueFactorizationMonoid ↥(Sn n) ∧

              (∀ f : F, f ∈ Sn n → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀) ∧
              (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀ → ∃ g h : ↥(Sn n), (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧

              (∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀) →
                LinearIndependent ↥(K n) c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0) ∧

              (∃ ϖ : ↥(An n), IsLocalRing.maximalIdeal ↥(An n) = Ideal.span {ϖ} ∧ ϖ ≠ 0 ∧
                Prime (φn n (Polynomial.C ϖ)) ∧
                (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀ →
                  (f ∈ R.integers ↔ ∃ g h : ↥(Sn n), ¬ (φn n (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F))) ∧
                (∀ p : ↥(Sn n), Prime p → ¬ Associated p (φn n (Polynomial.C ϖ)) →
                  ∀ x : ↥(Sn n), ∃ r : Polynomial ↥(An n), r.Monic ∧ p ∣ (r.map ((φn n).comp Polynomial.C)).eval x)) ∧

              (∀ χ : ↥(Sn n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : L), (hAn n _).mp (χ f).2⟩ = χn n f) →
                RingHom.ker χ = Ideal.span {φn n Polynomial.X - φn n (Polynomial.C (χ (φn n Polynomial.X)))}) ∧

              (∃ G : Finset F, ↑G ⊆ (Sn n : Set F) ∧ ∀ f ∈ Sn n, ∃ g h : F,
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) ∧
                (∃ u : (↥(Sn n))ˣ, ((u : ↥(Sn n)) : F) = h) ∧ f * h = g)) ∧
      (∃ hmono : ∀ n n', K n ≤ K n' → Sn n ≤ Sn n',
      (∀ n n', K n ≤ K n' →
        Sn n' ≤ Subring.closure ((Sn n : Set F) ∪ ((fun a : ↥(An n') => algebraMap (L) F ((a : ↥(K n')) : L)) '' Set.univ))) ∧
      (∀ n n', ((φn n Polynomial.X : ↥(Sn n)) : F) = ((φn n' Polynomial.X : ↥(Sn n')) : F)) ∧
      (∀ n n' (h : K n ≤ K n') (f : ↥(Sn n)), χn n' ⟨(f : F), hmono n n' h f.2⟩ = χn n f)) := by
  intro F₀ hgen hS₁F₁ hfrac hLD
  classical
  letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra
  haveI : IsScalarTower k₀ L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  obtain ⟨ht, hmaxiff, -, hnoeth, hufd, hprime, hRint, hchart, hker, hbranch, hfg⟩ :=
    AlgebraicCurve.RegularProlongation.smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian
      A R K₁ halg A₁ hA₁ hκ₁ S₁ φ₁ χ₁ hAS hφC hχC hχt ϖ hϖ hϖ0 hmax hφs hφu hφf hSR hcen F₀ hgen hS₁F₁ hfrac
  have hld₁ := hLD K₁ hK₁

  have hϖex : ∀ n, ∃ ϖ₂ : ↥(An n), maximalIdeal ↥(An n) = Ideal.span {ϖ₂} ∧ ϖ₂ ≠ 0 := by
    intro n
    haveI := hdvrn n
    obtain ⟨ϖ₂, hirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥(An n)
    exact ⟨ϖ₂, hirr.maximalIdeal_eq, hirr.ne_zero⟩
  choose ϖn hϖn hϖn0 using hϖex

  have hG2 := fun n => AlgebraicCurve.RegularProlongation.exists_smoothPointStalk_baseChange_layer
    A R Q K₁ (K n) (hKle n) halg (hKfin n) A₁ hA₁ (An n) (hAn n) hκ₁ (hκn n) inferInstance (hdvrn n) inferInstance (hhensn n)
    (ϖn n) (hϖn n) (hϖn0 n) S₁ φ₁ χ₁ D₁ hAS hφs hφu hφC hχC hχt hchart hker hres hordQ hD ht inferInstance hmaxiff hnoeth hufd
    ϖ hϖ hϖ0 hprime hbranch hfg F₀ hgen hS₁F₁ hfrac hld₁ hRint
  choose Sn φn χn hspec using hG2

  have hmono₁ : ∀ n, S₁ ≤ Sn n := fun n => by obtain ⟨⟨h, -⟩, -⟩ := hspec n; exact h
  have hgen₁ : ∀ n, Sn n ≤ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) :=
    fun n => by obtain ⟨⟨h, h1, -⟩, -⟩ := hspec n; exact h1
  have hpar₁ : ∀ n, ((φ₁ Polynomial.X : ↥S₁) : F) = ((φn n Polynomial.X : ↥(Sn n)) : F) :=
    fun n => by obtain ⟨⟨h, -, h2, -⟩, -⟩ := hspec n; exact h2
  have hchar₁ : ∀ n (f : ↥S₁), χn n ⟨(f : F), hmono₁ n f.2⟩ = χ₁ f :=
    fun n f => by obtain ⟨⟨h, -, -, h3⟩, -⟩ := hspec n; exact h3 f
  have hASn : ∀ n (a : ↥(An n)), algebraMap L F ((a : ↥(K n)) : L) ∈ Sn n :=
    fun n => by obtain ⟨-, h, -⟩ := hspec n; exact h
  have hχCn : ∀ n (a : ↥(An n)), χn n (φn n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩ :=
    fun n => by obtain ⟨-, -, -, -, -, h, -⟩ := hspec n; exact h
  have hφCn : ∀ n (a : ↥(An n)), ((φn n (Polynomial.C a) : ↥(Sn n)) : F) = algebraMap L F ((a : ↥(K n)) : L) :=
    fun n => by obtain ⟨-, -, -, -, h, -⟩ := hspec n; exact h

  have hSeq : ∀ n, Sn n = Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) := by
    intro n
    refine le_antisymm (hgen₁ n) (Subring.closure_le.mpr ?_)
    rintro x (hx | ⟨a, -, rfl⟩)
    · exact hmono₁ n hx
    · exact hASn n a

  have hAnle : ∀ n n', K n ≤ K n' → ∀ a : ↥(An n), ∃ a' : ↥(An n'), ((a' : ↥(K n')) : L) = ((a : ↥(K n)) : L) := by
    intro n n' h a
    refine ⟨⟨⟨((a : ↥(K n)) : L), h (a : ↥(K n)).2⟩, ?_⟩, rfl⟩
    rw [hAn]; exact (hAn n a).mp a.2
  refine ⟨Sn, φn, χn, ⟨hmono₁, hgen₁, hpar₁, hchar₁⟩, ?_, ?_⟩
  ·
    intro n
    obtain ⟨-, hAS₂, hφs₂, hφu₂, hφC₂, hχC₂, hχt₂, hchart₂, hres₂, hordQ₂, hD₂, ht₂, hloc₂, hnoeth₂, hufd₂, hSF₂, hfrac₂,
      hprime₂, hRint₂, hker₂, hbranch₂, hfg₂⟩ := hspec n
    exact ⟨hκn n, hAS₂, hφs₂, hφu₂, hφC₂, hχC₂, hχt₂, hchart₂, hres₂, hordQ₂, hD₂, ht₂, hloc₂, hnoeth₂, hufd₂, hSF₂, hfrac₂,
      hLD (K n) (hKfin n), ⟨ϖn n, hϖn n, hϖn0 n, hprime₂, hRint₂, hbranch₂⟩, hker₂, hfg₂⟩
  ·
    have hmono : ∀ n n', K n ≤ K n' → Sn n ≤ Sn n' := by
      intro n n' h
      rw [hSeq n, hSeq n']
      apply Subring.closure_mono
      rintro x (hx | ⟨a, -, rfl⟩)
      · exact Or.inl hx
      · obtain ⟨a', ha'⟩ := hAnle n n' h a
        exact Or.inr ⟨a', trivial, by show algebraMap L F ((a' : ↥(K n')) : L) = algebraMap L F ((a : ↥(K n)) : L); rw [ha']⟩
    refine ⟨hmono, ?_, ?_, ?_⟩
    · intro n n' h
      rw [hSeq n']
      apply Subring.closure_mono
      rintro x (hx | hx)
      · exact Or.inl (hmono₁ n hx)
      · exact Or.inr hx
    · intro n n'; rw [← hpar₁ n, ← hpar₁ n']
    · intro n n' h f

      let incl : ↥(Sn n) →+* ↥(Sn n') := Subring.inclusion (hmono n n' h)
      let T : Subring ↥(Sn n) := RingHom.eqLocus ((χn n').comp incl) (χn n)
      have hT : ∀ x : F, x ∈ Sn n → ∃ hx : x ∈ Sn n, (⟨x, hx⟩ : ↥(Sn n)) ∈ T := by
        intro x hx
        refine ⟨hx, ?_⟩
        have key : Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) ≤
            T.map (Sn n).subtype := by
          rw [Subring.closure_le]
          rintro y (hy | ⟨a, -, rfl⟩)
          · refine ⟨⟨y, hmono₁ n hy⟩, ?_, rfl⟩
            show χn n' (incl ⟨y, hmono₁ n hy⟩) = χn n ⟨y, hmono₁ n hy⟩
            have e1 : incl ⟨y, hmono₁ n hy⟩ = ⟨y, hmono₁ n' hy⟩ := rfl
            rw [e1, hchar₁ n' ⟨y, hy⟩]
            exact (hchar₁ n ⟨y, hy⟩).symm
          · obtain ⟨a', ha'⟩ := hAnle n n' h a
            refine ⟨⟨_, hASn n a⟩, ?_, rfl⟩
            show χn n' (incl ⟨_, hASn n a⟩) = χn n ⟨_, hASn n a⟩
            have e1 : (⟨algebraMap L F ((a : ↥(K n)) : L), hASn n a⟩ : ↥(Sn n)) = φn n (Polynomial.C a) :=
              Subtype.ext (by rw [hφCn])
            have e2 : incl ⟨algebraMap L F ((a : ↥(K n)) : L), hASn n a⟩ = φn n' (Polynomial.C a') :=
              Subtype.ext (by rw [hφCn, ha']; rfl)
            rw [e2, e1, hχCn, hχCn]
            congr 1
            exact Subtype.ext ha'
        have := key (hSeq n ▸ hx)
        obtain ⟨z, hz, hzx⟩ := this
        have : z = ⟨x, hx⟩ := Subtype.ext hzx
        rw [← this]; exact hz
      obtain ⟨hf, hfT⟩ := hT (f : F) f.2
      have : (⟨(f : F), hf⟩ : ↥(Sn n)) = f := Subtype.ext rfl
      rw [this] at hfT
      exact hfT

end S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalks_tower_of_base
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalks_tower_of_base (solution)
