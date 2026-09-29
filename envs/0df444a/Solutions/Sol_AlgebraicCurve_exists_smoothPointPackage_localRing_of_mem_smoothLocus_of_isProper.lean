-- Prove2me | solution 1 for AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0394a584-a82d-56a9-a756-f7cbff5519ba

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus
import Theorems.Thm_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization
import Theorems.Thm_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
import Theorems.Thm_AlgebraicCurve_exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation
import Theorems.Thm_AlgebraicCurve_exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

namespace M3bAssembly

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (φ : F ≃+* X.functionField)

theorem algebraMap_stalk_functionField_eq (x : X) :
    algebraMap (X.presheaf.stalk x) X.functionField =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))).hom :=
  rfl

theorem mem_localRing_iff (x : X) (g : F) :
    g ∈ SemistableModel.localRing X φ x ↔
      ∃ s : X.presheaf.stalk x, φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s) = g := by
  simp only [SemistableModel.localRing, RingHom.mem_range, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, Function.comp_apply]

theorem algebraMap_stalkSpecializes {x y : X} (h : x ⤳ y) (s : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.stalkSpecializes h).hom s) =
      algebraMap (X.presheaf.stalk y) X.functionField s := by
  rw [algebraMap_stalk_functionField_eq, algebraMap_stalk_functionField_eq,
    ← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem localRing_le_of_specializes {x y : X} (h : x ⤳ y) :
    SemistableModel.localRing X φ y ≤ SemistableModel.localRing X φ x := by
  intro g hg
  obtain ⟨s, rfl⟩ := (mem_localRing_iff φ y g).mp hg
  exact (mem_localRing_iff φ x _).mpr ⟨(X.presheaf.stalkSpecializes h).hom s, by
    rw [algebraMap_stalkSpecializes]⟩

end M3bAssembly

open M3bAssembly in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∃ (Q : Place (ResidueField ↥A) Fbar) (φT : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
      (D : Set (Place L F)),
      Q.IsRational ∧

      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
      φT.FormallySmooth ∧ φT.FormallyUnramified ∧
      (∀ a : ↥A, ((φT (Polynomial.C a) : ↥S) : F) = algebraMap L F (a : L)) ∧
      (∀ a : ↥A, χ₀ (φT (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
      χ₀ (φT Polynomial.X) = 0 ∧
      (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
        ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) ∧
          (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φT Polynomial.X) = c) ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
          algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
      (∃ hR : ((φT Polynomial.X : ↥S) : F) ∈ R.integers,
        Q.ord (R.residue ⟨((φT Polynomial.X : ↥S) : F), hR⟩) = 1) ∧
      (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
      (∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) →
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
        ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
      (∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔
        ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
        ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F)) ∧
      (∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) := by
  intro S

  obtain ⟨ι, hι, t, χ₀, hloc, hunit, hχ₀C, hχ₀t, hφs, hφu, hmS, hprime, htq, hnoeth, hgen, hfrac,
      P, instP1, instP2, instP3, M, instP4, instP5, hPM⟩ :=
    AlgebraicCurve.SemistableModel.exists_etaleCoordinate_localRing_of_mem_smoothLocus
      A X toBase φ hφ x hx hxc hxs η hηx hne hη
  haveI : IsLocalRing ↥S := hloc
  set 𝔮 : Ideal ↥S := (maximalIdeal ↥A).map ι with h𝔮def
  set φT : Polynomial ↥A →+* ↥S := Polynomial.eval₂RingHom ι t with hφTdef
  have hφTC : ∀ a : ↥A, φT (Polynomial.C a) = ι a := fun a => by
    simp [hφTdef]
  have hφTX : φT Polynomial.X = t := by simp [hφTdef]
  have hmax : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ χ₀ f = 0 := fun f => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit f, not_not]
  have hker0 : RingHom.ker χ₀ = maximalIdeal ↥S := by
    ext f; rw [RingHom.mem_ker, hmax]
  have h𝔮max : 𝔮 ≤ maximalIdeal ↥S := by
    rw [h𝔮def, Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap, hmax, hχ₀C, IsLocalRing.residue_eq_zero_iff]
    exact hm
  have htmax : t ∈ maximalIdeal ↥S := (hmax t).mpr hχ₀t
  have hmaxeq : maximalIdeal ↥S = Ideal.span {t} ⊔ 𝔮 := by
    apply le_antisymm
    · intro f hf
      obtain ⟨g, s, hs, rfl⟩ := hmS f ((hmax f).mp hf)
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.mpr ⟨g, rfl⟩))
        (Ideal.mem_sup_right hs)
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr htmax) h𝔮max
  have hne𝔮 : 𝔮 ≠ maximalIdeal ↥S := fun h => htq (h ▸ htmax)

  have hPS : ∀ a : ↥A, algebraMap P ↥S (algebraMap ↥A P a) = φT (Polynomial.C a) := fun a => by
    rw [hPM, hφTC]
  obtain ⟨hhens, hkerχ⟩ :=
    HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallyUnramified_of_isLocalization
      φT hφs hφu P M hPS χ₀ hker0 (fun a => by rw [hφTC, hχ₀C]) (by rw [hφTX, hχ₀t])
  have hhens' : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) ∧
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ t = c := by
    intro c hc
    simpa only [hφTC, hφTX] using hhens c hc
  have hker' : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) →
      (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      RingHom.ker χ = Ideal.span {t - ι (χ t)} := by
    intro χ h1 h2
    simpa only [hφTC, hφTX] using hkerχ χ (fun a => by rw [hφTC]; exact h1 a) h2

  set B : ValuationSubring F := R.integers with hBdef
  have hSB : ∀ f : ↥S, (f : F) ∈ B := fun f => by
    have h : (f : F) ∈ SemistableModel.localRing X φ η := localRing_le_of_specializes φ hηx f.2
    rw [← hR] at h
    exact h
  have hBmem : ∀ f : F, f ∈ B ↔ ∃ g h : ↥S, h ∉ 𝔮 ∧ f * (h : F) = (g : F) := by
    intro f
    rw [← hgen f, ← hR]
    rfl
  have hunitB : ∀ f : ↥S, f ∉ 𝔮 → (f : F) ≠ 0 ∧ (f : F)⁻¹ ∈ B := by
    intro f hf
    have hf0 : (f : F) ≠ 0 := by
      intro h0
      apply hf
      have : f = 0 := Subtype.ext h0
      rw [this]; exact Ideal.zero_mem _
    exact ⟨hf0, (hBmem _).mpr ⟨1, f, hf, by rw [inv_mul_cancel₀ hf0]; simp⟩⟩
  have hB : ∀ f : F, f ∈ B → ∃ g h : ↥S, h ∉ 𝔮 ∧ f * (h : F) = (g : F) := fun f hf => (hBmem f).mp hf
  have he1 : ∀ f : F, f ≠ 0 → ∃ c : L, c ≠ 0 ∧ algebraMap L F c * f ∈ B ∧ (algebraMap L F c * f)⁻¹ ∈ B := by
    intro f hf
    obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf
    have hc' : algebraMap L F c * f ∈ B := by rw [← Algebra.smul_def]; exact hc
    have hu : IsUnit (⟨c • f, hc⟩ : ↥R.integers) := R.isUnit_of_residue_ne_zero hres
    obtain ⟨u, hu⟩ := hu
    refine ⟨c, R.smul_const_ne_zero hc hres, hc', ?_⟩
    have hmul : ((u : ↥R.integers) : F) * (((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers) : F) = 1 :=
      congrArg Subtype.val u.mul_inv
    have hcf : ((u : ↥R.integers) : F) = algebraMap L F c * f := by
      rw [hu, ← Algebra.smul_def]
    rw [← hcf, ← eq_inv_of_mul_eq_one_right hmul]
    exact SetLike.coe_mem _

  letI instAlg : Algebra ↥A ↥S := ι.toAlgebra
  have halg : algebraMap ↥A ↥S = ι := rfl
  haveI : IsLocalHom (algebraMap ↥A ↥S) := ⟨fun a ha => by
    rw [halg] at ha
    have h1 : χ₀ (ι a) ≠ 0 := (hunit _).mp ha
    rw [hχ₀C, ne_eq, IsLocalRing.residue_eq_zero_iff] at h1
    exact (IsLocalRing.notMem_maximalIdeal.mp h1)⟩
  haveI : IsScalarTower ↥A P ↥S := IsScalarTower.of_algebraMap_eq (fun a => (hPM a).symm)
  haveI : Algebra.EssFiniteType P ↥S := Algebra.EssFiniteType.of_isLocalization ↥S M
  haveI : Algebra.EssFiniteType ↥A ↥S := Algebra.EssFiniteType.comp ↥A P ↥S
  have hres : Function.Surjective (algebraMap ↥A (ResidueField ↥S)) := by
    intro q
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective q
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (χ₀ f)
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply ↥A ↥S (ResidueField ↥S), IsLocalRing.ResidueField.algebraMap_eq, halg]
    apply Ideal.Quotient.eq.mpr
    rw [hmax, map_sub, hχ₀C, ha, sub_self]
  have hprime' : ((maximalIdeal ↥A).map (algebraMap ↥A ↥S)).IsPrime := by rw [halg]; exact hprime
  have hmaxeq' : maximalIdeal ↥S = Ideal.span {t} ⊔ (maximalIdeal ↥A).map (algebraMap ↥A ↥S) := by
    rw [halg]; exact hmaxeq
  have hprep : ∀ h : ↥S, h ∉ 𝔮 →
      ∃ (n : ℕ) (u : (↥S)ˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
        h = (u : ↥S) * ∏ i, (t - ι (r i)) := by
    intro h hh
    have hh' : h ∉ (maximalIdeal ↥A).map (algebraMap ↥A ↥S) := by rw [halg]; exact hh
    obtain ⟨n, u, r, hr, e⟩ :=
      ValuationSubring.exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
        A hres t hmaxeq' hprime' h hh'
    exact ⟨n, u, r, hr, by rw [e, halg]⟩

  obtain ⟨D, hD, hsec, hval, hunitp, hlocal⟩ :=
    AlgebraicCurve.exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation
      A S hloc ι hι χ₀ hχ₀C hmax t hfrac B R.algebraMap_mem_iff hSB hunitB hB hprime htq he1
      hhens' hker' hprep

  have hconst : ∀ c : ResidueField ↥A, ∃ a : ↥S, χ₀ a = c ∧
      R.residue ⟨((a : ↥S) : F), hSB a⟩ = algebraMap (ResidueField ↥A) Fbar c := by
    intro c
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨ι a₀, hχ₀C a₀, ?_⟩
    have e : (⟨((ι a₀ : ↥S) : F), hSB (ι a₀)⟩ : ↥R.integers) =
        ⟨algebraMap L F (a₀ : L), (R.algebraMap_mem_iff (a₀ : L)).mpr a₀.2⟩ := Subtype.ext (hι a₀)
    rw [e, R.residue_algebraMap]
  have h𝔮B : ∀ f : ↥S, f ∈ 𝔮 ↔ (⟨(f : F), hSB f⟩ : ↥B) ∈ maximalIdeal ↥B := by
    intro f
    constructor
    · intro hf

      have key : 𝔮 ≤ (maximalIdeal ↥B).comap
          ({ toFun := fun g : ↥S => (⟨(g : F), hSB g⟩ : ↥B), map_one' := rfl, map_mul' := fun _ _ => rfl,
             map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥S →+* ↥B) := by
        rw [h𝔮def, Ideal.map_le_iff_le_comap]
        intro m hm
        simp only [Ideal.mem_comap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        by_cases hm0 : (m : ↥A) = 0
        · apply hu.ne_zero
          apply Subtype.ext
          simp only [ZeroMemClass.coe_zero]
          rw [hι, hm0]; simp
        · obtain ⟨w, hw⟩ := hu
          have hmul : ((w : ↥B) : F) * (((w⁻¹ : (↥B)ˣ) : ↥B) : F) = 1 :=
            congrArg Subtype.val w.mul_inv
          have hwF : ((w : ↥B) : F) = algebraMap L F ((m : ↥A) : L) := by rw [hw]; exact hι m
          have hinv : (algebraMap L F ((m : ↥A) : L))⁻¹ ∈ B := by
            rw [← hwF, ← eq_inv_of_mul_eq_one_right hmul]; exact SetLike.coe_mem _
          rw [← map_inv₀, R.algebraMap_mem_iff] at hinv
          have hunitA : IsUnit (m : ↥A) := by
            have hm0' : ((m : ↥A) : L) ≠ 0 := fun h0 => hm0 (Subtype.ext h0)
            exact IsUnit.of_mul_eq_one (b := ⟨((m : ↥A) : L)⁻¹, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hm0'))
          exact (IsLocalRing.mem_maximalIdeal _).mp hm hunitA
      exact key hf
    · intro hf
      by_contra hf𝔮
      obtain ⟨hf0, hinv⟩ := hunitB f hf𝔮
      apply (IsLocalRing.mem_maximalIdeal _).mp hf
      exact IsUnit.of_mul_eq_one (b := ⟨(f : F)⁻¹, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hf0))
  have hfracB : ∀ b : ↥B, ∃ g h : ↥S, h ∉ 𝔮 ∧ (b : F) * (h : F) = (g : F) := fun b => hB b b.2
  obtain ⟨Q, hQrat, hQuniq, hQres, hQord⟩ :=
    AlgebraicCurve.exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup
      B R.residue R.residue_surjective R.ker_residue S hSB hloc χ₀ hker0 hconst 𝔮 h𝔮B t hmaxeq hne𝔮
      hnoeth hfracB

  refine ⟨Q, φT, χ₀, D, hQrat, ?_, ?_, hφs, hφu, ?_, ?_, ?_, hhens, ?_, ?_, hD, ?_, hval, hunitp, hlocal⟩
  ·
    intro Q' hQ'
    exact hQuniq Q' (fun f => by obtain ⟨_, hm⟩ := hQ' f; exact hm)
  ·
    intro a
    rw [← hι a]; exact (ι a).2
  · intro a; rw [hφTC, hι]
  · intro a; rw [hφTC, hχ₀C]
  · rw [hφTX, hχ₀t]
  ·
    intro f
    obtain ⟨hm, e⟩ := hQres f
    exact ⟨hSB f, hm, e⟩
  ·
    rw [hφTX]
    exact ⟨hSB t, hQord⟩
  ·
    intro χ h1 h2
    exact hsec χ (fun a => by rw [← hφTC]; exact h1 a) h2

end S_AlgebraicCurve_exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper
end P2MW
export P2MW.S_AlgebraicCurve_exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper (solution)
