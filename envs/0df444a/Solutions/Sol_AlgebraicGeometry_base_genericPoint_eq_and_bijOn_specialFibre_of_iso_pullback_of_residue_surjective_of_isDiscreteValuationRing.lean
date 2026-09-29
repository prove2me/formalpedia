-- Prove2me | solution 1 for AlgebraicGeometry.base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9d82241c-641b-5d0b-8e60-582346d0c69d

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace E137

theorem stalk_level_localization_tensor
    {A₀ A₁ : Type} [CommRing A₀] [CommRing A₁] (ι : A₀ →+* A₁)
    {X₀ X₁ : Scheme.{0}} (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (g₁ : X₁ ⟶ X₀)
    (hsq : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι))) (x₁ : X₁) :
    letI : Algebra A₀ A₁ := ι.toAlgebra
    letI : Algebra A₀ (X₀.presheaf.stalk (g₁.base x₁)) :=
      ((X₀.presheaf.germ ⊤ (g₁.base x₁) trivial).hom.comp
        (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X₀.presheaf.stalk (g₁.base x₁)) ⊗[A₀] A₁)) (_ : 𝔮.IsPrime)
      (e : X₁.presheaf.stalk x₁ ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A₀) (S := A₀)
          (A := X₀.presheaf.stalk (g₁.base x₁)) (B := A₁)).toRingHom =
        IsLocalRing.maximalIdeal (X₀.presheaf.stalk (g₁.base x₁)) ∧
      (∀ s : X₀.presheaf.stalk (g₁.base x₁),
        e ((g₁.stalkMap x₁).hom s) =
          algebraMap ((X₀.presheaf.stalk (g₁.base x₁)) ⊗[A₀] A₁) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1)) ∧
      (∀ a : A₁,
        e ((X₁.presheaf.germ ⊤ x₁ trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a))) =
          algebraMap ((X₀.presheaf.stalk (g₁.base x₁)) ⊗[A₀] A₁) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A₀] a)) := by
  letI : Algebra A₀ A₁ := ι.toAlgebra
  obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : X₁ ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)),
      θ.hom ≫ pullback.fst _ _ = g₁ ∧ θ.hom ≫ pullback.snd _ _ = f₁ :=
    ⟨hsq.isoPullback, hsq.isoPullback_hom_fst, hsq.isoPullback_hom_snd⟩
  subst hθ₁ hθ₂
  obtain ⟨𝔮, h𝔮, eP, hcomap, hfst, hsnd⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
      X₀ toBase₀ A₁ (θ.hom.base x₁)

  let eθ : ↑((pullback toBase₀ (Spec.map (CommRingCat.ofHom ι))).presheaf.stalk (θ.hom.base x₁)) ≃+*
      ↑(X₁.presheaf.stalk x₁) := (asIso (θ.hom.stalkMap x₁)).commRingCatIsoToRingEquiv
  have heθ : ∀ t, eθ t = (θ.hom.stalkMap x₁).hom t := fun _ => rfl
  refine ⟨𝔮, h𝔮, eθ.symm.trans eP, hcomap, ?_, ?_⟩
  · intro s
    have h1 : eθ.symm (((θ.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap x₁).hom s) =
        ((pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (θ.hom.base x₁)).hom s := by
      rw [RingEquiv.symm_apply_eq, heθ, Scheme.Hom.stalkMap_comp]
      rfl
    rw [RingEquiv.trans_apply, h1]
    exact hfst s
  · intro a
    have key : (X₁.presheaf.germ ⊤ x₁ trivial).hom ((θ.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a)) =
        eθ (((pullback toBase₀ (Spec.map (CommRingCat.ofHom ι))).presheaf.germ ⊤ (θ.hom.base x₁) trivial).hom
          ((pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι))).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a))) := by
      rw [heθ, Scheme.Hom.comp_appTop]
      exact (Scheme.Hom.germ_stalkMap_apply θ.hom ⊤ x₁ trivial _).symm
    rw [key, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    exact hsnd a

theorem base_eq_closedPoint_iff {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}}
    (f : Z ⟶ Spec (CommRingCat.of R)) (z : Z) :
    f.base z = closedPoint R ↔ ∀ a : R, a ∈ maximalIdeal R →
      ¬ IsUnit ((Z.presheaf.germ ⊤ z trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) := by
  have key : ∀ a : R, IsUnit ((Z.presheaf.germ ⊤ z trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) ↔ a ∉ (f.base z).asIdeal := by
    intro a
    rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top]
    change f.base z ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) ↔
      a ∉ (f.base z).asIdeal
    rw [basicOpen_eq_of_affine (R := CommRingCat.of R) a]
    exact PrimeSpectrum.mem_basicOpen (R := R) a (f.base z)
  constructor
  · intro hz a ha
    rw [key, not_not, hz]
    exact ha
  · intro H
    have hle : maximalIdeal R ≤ (f.base z).asIdeal := fun a ha => by
      have := H a ha
      rwa [key, not_not] at this
    apply PrimeSpectrum.ext
    exact ((maximalIdeal.isMaximal R).eq_of_le (f.base z).isPrime.ne_top hle).symm

theorem specializes_of_base_specializes
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hX : IsIntegral X]
    (hinj : ∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A →
      (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x =
        (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y → x = y)
    (x y : X) (hx : toBase.base x = closedPoint ↥A) (hy : toBase.base y = closedPoint ↥A)
    (h : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x ⤳
      (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y) :
    x ⤳ y := by
  set pr := iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)) with hpr

  have hsq : IsPullback pr toBase toBase₀ (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso (by rw [hpr]) hiso
    rw [hpr, Category.assoc, pullback.condition, ← Category.assoc, hiso]

  have hprbase : pr ≫ toBase₀ = toBase ≫ Spec.map (CommRingCat.ofHom ι) := hsq.w
  have hx₀ : toBase₀.base (pr.base x) = closedPoint A₀ := by
    have := congrArg (fun k : X ⟶ _ => k.base x) hprbase
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [this, hx]
    exact Spec_closedPoint

  let cA : ↥A →+* ↑(X.presheaf.stalk y) :=
    (X.presheaf.germ ⊤ y trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
  let c₀ : A₀ →+* ↑(X₀.presheaf.stalk (pr.base y)) :=
    (X₀.presheaf.germ ⊤ (pr.base y) trivial).hom.comp (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)
  have hyc : ∀ a : ↥A, a ∈ maximalIdeal ↥A → ¬ IsUnit (cA a) := (base_eq_closedPoint_iff toBase y).mp hy
  have hx₀c : ∀ a₀ : A₀, a₀ ∈ maximalIdeal A₀ → ¬ IsUnit ((X₀.presheaf.germ ⊤ (pr.base x) trivial).hom
      (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a₀))) :=
    (base_eq_closedPoint_iff toBase₀ (pr.base x)).mp hx₀

  letI algA : Algebra A₀ ↥A := ι.toAlgebra
  letI alg₀ : Algebra A₀ ↑(X₀.presheaf.stalk (pr.base y)) := c₀.toAlgebra
  obtain ⟨𝔮, h𝔮, e, hcomap, hg, hc⟩ := stalk_level_localization_tensor ι toBase₀ toBase pr hsq y

  let P : Ideal ↑(X₀.presheaf.stalk (pr.base y)) :=
    (maximalIdeal ↑(X₀.presheaf.stalk (pr.base x))).comap (X₀.presheaf.stalkSpecializes h).hom
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hPle : P ≤ maximalIdeal _ := IsLocalRing.le_maximalIdeal hP.ne_top
  have hc₀P : ∀ a₀ : A₀, a₀ ∈ maximalIdeal A₀ → c₀ a₀ ∈ P := by
    intro a₀ ha₀
    change (X₀.presheaf.stalkSpecializes h).hom (c₀ a₀) ∈ maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have : (X₀.presheaf.stalkSpecializes h).hom (c₀ a₀) = (X₀.presheaf.germ ⊤ (pr.base x) trivial).hom
        (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a₀)) := by
      change ((X₀.presheaf.germ ⊤ (pr.base y) trivial) ≫ X₀.presheaf.stalkSpecializes h).hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [this]
    exact hx₀c a₀ ha₀

  let κmap : ResidueField A₀ →+* ResidueField ↥A := IsLocalRing.ResidueField.map ι
  have hκ : Function.Bijective κmap := by
    refine ⟨κmap.injective, fun r => ?_⟩
    obtain ⟨a₀, ha₀⟩ := hres r
    exact ⟨IsLocalRing.residue A₀ a₀, ha₀⟩
  let κeq : ResidueField A₀ ≃+* ResidueField ↥A := RingEquiv.ofBijective κmap hκ
  have hκeq : ∀ a₀ : A₀, κeq (IsLocalRing.residue A₀ a₀) = IsLocalRing.residue ↥A (ι a₀) := fun _ => rfl

  let τ₁ : ResidueField A₀ →+* (↑(X₀.presheaf.stalk (pr.base y)) ⧸ P) :=
    Ideal.Quotient.lift (maximalIdeal A₀) ((Ideal.Quotient.mk P).comp c₀) (fun a₀ ha₀ => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hc₀P a₀ ha₀)
  let σ : ↥A →+* (↑(X₀.presheaf.stalk (pr.base y)) ⧸ P) :=
    τ₁.comp (κeq.symm.toRingHom.comp (IsLocalRing.residue ↥A))
  have hσι : ∀ a₀ : A₀, σ (ι a₀) = Ideal.Quotient.mk P (c₀ a₀) := by
    intro a₀
    change τ₁ (κeq.symm (IsLocalRing.residue ↥A (ι a₀))) = _
    rw [← hκeq, RingEquiv.symm_apply_apply]
    rfl
  have hσ0 : ∀ m : ↥A, m ∈ maximalIdeal ↥A → σ m = 0 := by
    intro m hm
    change τ₁ (κeq.symm (IsLocalRing.residue ↥A m)) = 0
    rw [(IsLocalRing.residue_eq_zero_iff m).mpr hm, map_zero, map_zero]

  let σₐ : ↥A →ₐ[A₀] (↑(X₀.presheaf.stalk (pr.base y)) ⧸ P) :=
    { toRingHom := σ
      commutes' := fun a₀ => by
        change σ (ι a₀) = Ideal.Quotient.mk P (c₀ a₀)
        exact hσι a₀ }
  let Φ : (↑(X₀.presheaf.stalk (pr.base y)) ⊗[A₀] ↥A) →ₐ[A₀] (↑(X₀.presheaf.stalk (pr.base y)) ⧸ P) :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ A₀ P) σₐ (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (r : ↑(X₀.presheaf.stalk (pr.base y))) (a : ↥A), Φ (r ⊗ₜ[A₀] a) = Ideal.Quotient.mk P r * σ a :=
    fun r a => Algebra.TensorProduct.lift_tmul _ _ _ r a
  let J : Ideal (↑(X₀.presheaf.stalk (pr.base y)) ⊗[A₀] ↥A) := RingHom.ker Φ.toRingHom
  haveI hJ : J.IsPrime := RingHom.ker_isPrime Φ.toRingHom
  have hJleft : J.comap (Algebra.TensorProduct.includeLeft (R := A₀) (S := A₀)
      (A := ↑(X₀.presheaf.stalk (pr.base y))) (B := ↥A)).toRingHom = P := by
    ext r
    simp only [Ideal.mem_comap, J, RingHom.mem_ker]
    change Φ (r ⊗ₜ[A₀] 1) = 0 ↔ r ∈ P
    rw [hΦ, map_one, mul_one, Ideal.Quotient.eq_zero_iff_mem]

  have h1m : ∀ m : ↥A, m ∈ maximalIdeal ↥A → (1 : ↑(X₀.presheaf.stalk (pr.base y))) ⊗ₜ[A₀] m ∈ 𝔮 := by
    intro m hm
    by_contra hnot
    have hu : IsUnit (algebraMap _ (Localization.AtPrime 𝔮) ((1 : ↑(X₀.presheaf.stalk (pr.base y))) ⊗ₜ[A₀] m)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮) 𝔮 _).mpr hnot
    rw [← hc m] at hu
    exact hyc m hm (by have h__af := hu.map e.symm; simp at h__af; exact h__af)

  have hdecomp : ∀ t : ↑(X₀.presheaf.stalk (pr.base y)) ⊗[A₀] ↥A,
      ∃ r : ↑(X₀.presheaf.stalk (pr.base y)), t - r ⊗ₜ[A₀] 1 ∈ 𝔮 ∧ Φ t = Ideal.Quotient.mk P r := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul r a =>
      obtain ⟨a₀, ha₀⟩ := hres (IsLocalRing.residue ↥A a)
      have hm : a - ι a₀ ∈ maximalIdeal ↥A := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]; exact ha₀.symm
      refine ⟨a₀ • r, ?_, ?_⟩
      · have : r ⊗ₜ[A₀] a - (a₀ • r) ⊗ₜ[A₀] (1 : ↥A) =
            (r ⊗ₜ[A₀] (1 : ↥A)) * ((1 : ↑(X₀.presheaf.stalk (pr.base y))) ⊗ₜ[A₀] (a - ι a₀)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub, TensorProduct.smul_tmul,
            Algebra.smul_def, mul_one]
          rfl
        rw [this]
        exact Ideal.mul_mem_left _ _ (h1m _ hm)
      · rw [hΦ]
        have : σ a = σ (ι a₀) := by
          rw [← sub_eq_zero, ← map_sub]; exact hσ0 _ hm
        rw [this, hσι, ← map_mul, Algebra.smul_def, mul_comm]
        rfl
    | add s t hs ht =>
      obtain ⟨r₁, h₁, e₁⟩ := hs
      obtain ⟨r₂, h₂, e₂⟩ := ht
      refine ⟨r₁ + r₂, ?_, by rw [map_add, e₁, e₂, map_add]⟩
      have : s + t - (r₁ + r₂) ⊗ₜ[A₀] (1 : ↥A) = (s - r₁ ⊗ₜ[A₀] 1) + (t - r₂ ⊗ₜ[A₀] 1) := by
        rw [TensorProduct.add_tmul]; ring
      rw [this]; exact Ideal.add_mem _ h₁ h₂
  have hJ𝔮 : J ≤ 𝔮 := by
    intro t ht
    obtain ⟨r, hr, hΦt⟩ := hdecomp t
    have hr0 : r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hΦt]; exact ht
    have hr𝔮 : r ⊗ₜ[A₀] (1 : ↥A) ∈ 𝔮 := by
      have : r ∈ 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A₀) (S := A₀)
          (A := ↑(X₀.presheaf.stalk (pr.base y))) (B := ↥A)).toRingHom := by
        rw [hcomap]; exact hPle hr0
      exact this
    have := Ideal.add_mem _ hr hr𝔮
    simpa using this

  have hdisj : Disjoint (↑𝔮.primeCompl : Set (↑(X₀.presheaf.stalk (pr.base y)) ⊗[A₀] ↥A)) ↑J := by
    rw [Set.disjoint_left]; intro t ht htJ; exact ht (hJ𝔮 htJ)
  haveI hQ : (J.map (algebraMap _ (Localization.AtPrime 𝔮))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl (Localization.AtPrime 𝔮) J hJ hdisj
  let Q' : Ideal ↑(X.presheaf.stalk y) := (J.map (algebraMap _ (Localization.AtPrime 𝔮))).comap e.toRingHom
  haveI hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨x', hx'y, hloc⟩ := AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk y Q'
  have hQ'eq : Q' = (maximalIdeal ↑(X.presheaf.stalk x')).comap (X.presheaf.stalkSpecializes hx'y).hom := by
    letI := (X.presheaf.stalkSpecializes hx'y).hom.toAlgebra
    haveI := hloc
    exact (IsLocalization.AtPrime.under_maximalIdeal ↑(X.presheaf.stalk x') Q').symm

  have hx' : toBase.base x' = closedPoint ↥A := by
    refine (base_eq_closedPoint_iff toBase x').mpr (fun a ha => ?_)
    have hgerm : (X.presheaf.germ ⊤ x' trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)) =
        (X.presheaf.stalkSpecializes hx'y).hom (cA a) := by
      change _ = ((X.presheaf.germ ⊤ y trivial) ≫ X.presheaf.stalkSpecializes hx'y).hom _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [hgerm]
    have hmem : cA a ∈ Q' := by
      change e (cA a) ∈ J.map (algebraMap _ (Localization.AtPrime 𝔮))
      have : e (cA a) = algebraMap _ (Localization.AtPrime 𝔮) ((1 : ↑(X₀.presheaf.stalk (pr.base y))) ⊗ₜ[A₀] a) := hc a
      rw [this]
      apply Ideal.mem_map_of_mem
      change Φ ((1 : ↑(X₀.presheaf.stalk (pr.base y))) ⊗ₜ[A₀] a) = 0
      rw [hΦ, map_one, one_mul]; exact hσ0 a ha
    rw [hQ'eq, Ideal.mem_comap] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem

  have hfss : pr.base x' = (X₀.fromSpecStalk (pr.base y)).base
      (PrimeSpectrum.comap (pr.stalkMap y).hom
        (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hx'y).hom (closedPoint ↑(X.presheaf.stalk x')))) := by
    have h1 : pr.base x' = (X.fromSpecStalk x' ≫ pr).base (closedPoint _) := by
      simp only [Scheme.Hom.comp_base, TopCat.comp_app]
      rw [Scheme.fromSpecStalk_closedPoint]
    rw [h1, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hx'y, Category.assoc,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rfl
  have hx₀fss : pr.base x = (X₀.fromSpecStalk (pr.base y)).base
      (PrimeSpectrum.comap (X₀.presheaf.stalkSpecializes h).hom (closedPoint ↑(X₀.presheaf.stalk (pr.base x)))) := by
    have e1 := congrArg (fun F => F.base (closedPoint ↑(X₀.presheaf.stalk (pr.base x))))
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk h)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e1
    rw [Scheme.fromSpecStalk_closedPoint] at e1
    exact e1.symm
  have hcomapQ' : Q'.comap (pr.stalkMap y).hom = P := by
    have hunder := IsLocalization.under_map_of_isPrime_disjoint 𝔮.primeCompl (Localization.AtPrime 𝔮) hJ hdisj
    ext s
    rw [Ideal.mem_comap]
    change e ((pr.stalkMap y).hom s) ∈ J.map (algebraMap _ (Localization.AtPrime 𝔮)) ↔ s ∈ P
    rw [hg s, ← hJleft, Ideal.mem_comap]
    change _ ↔ s ⊗ₜ[A₀] (1 : ↥A) ∈ J
    constructor
    · intro hmem
      have h' : s ⊗ₜ[A₀] (1 : ↥A) ∈ (J.map (algebraMap _ (Localization.AtPrime 𝔮))).under
          (↑(X₀.presheaf.stalk (pr.base y)) ⊗[A₀] ↥A) := hmem
      rwa [hunder] at h'
    · intro hmem
      exact Ideal.mem_map_of_mem _ hmem
  have hprx' : pr.base x' = pr.base x := by
    rw [hfss, hx₀fss]
    congr 1
    apply PrimeSpectrum.ext
    change Ideal.comap (pr.stalkMap y).hom
        (Ideal.comap (X.presheaf.stalkSpecializes hx'y).hom (maximalIdeal ↑(X.presheaf.stalk x'))) = P
    rw [← hQ'eq]
    exact hcomapQ'

  have hxx' := hinj x' x hx' hx hprx'
  rw [← hxx']
  exact hx'y

end E137

namespace BCFibreE133

theorem base_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [Surjective g] :
    g.base (genericPoint X) = genericPoint Y := by
  have hX := genericPoint_spec X
  have hY := genericPoint_spec Y
  have h1 : IsGenericPoint (g.base (genericPoint X)) (⊤ : Set Y) := by
    rw [isGenericPoint_def]
    apply Set.eq_univ_of_univ_subset
    have h2 : g.base '' closure ({genericPoint X} : Set X) ⊆ closure (g.base '' {genericPoint X}) :=
      image_closure_subset_closure_image g.base.hom.continuous
    rw [hX.def, Set.image_singleton] at h2
    intro y _
    obtain ⟨x, rfl⟩ := g.surjective y
    exact h2 ⟨x, trivial, rfl⟩
  exact h1.eq hY

theorem eq_maximalIdeal_of_ne_bot {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (P : Ideal ↥A) [P.IsPrime] (hP : P ≠ ⊥) : P = maximalIdeal ↥A := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
  intro a ha
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨n, c, hc⟩ := hrk a b ha hb0
  have : a ^ n ∈ P := by rw [hc]; exact Ideal.mul_mem_right _ _ hbP
  exact Ideal.IsPrime.mem_of_pow_mem ‹_› n this

end BCFibreE133

open BCFibreE133

set_option maxHeartbeats 3200000 in
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hX : IsIntegral X] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    pr.base (genericPoint X) = genericPoint X₀ ∧
      (∀ x : X, toBase.base x = closedPoint ↥A ↔ toBase₀.base (pr.base x) = closedPoint A₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → pr.base x = pr.base y → x = y) ∧
      (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → ∃ x : X, pr.base x = x₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → (x ⤳ y ↔ pr.base x ⤳ pr.base y)) := by
  classical
  intro pr

  haveI hsurjι : Surjective (Spec.map (CommRingCat.ofHom ι)) := by
    refine ⟨fun q => ?_⟩
    by_cases hq : q.asIdeal = ⊥
    · refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      show Ideal.comap ι ⊥ = q.asIdeal
      rw [hq, Ideal.comap_bot_of_injective ι hι]
    · refine ⟨closedPoint ↥A, ?_⟩
      rw [Spec_closedPoint]
      apply PrimeSpectrum.ext
      haveI := q.isPrime
      exact (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime)).symm
  haveI : Surjective pr := inferInstance

  have hgen : pr.base (genericPoint X) = genericPoint X₀ := base_genericPoint_eq pr

  have hsq : ∀ z : X, toBase₀.base (pr.base z) = (Spec.map (CommRingCat.ofHom ι)).base (toBase.base z) := by
    intro z
    show (pr ≫ toBase₀).base z = (toBase ≫ Spec.map (CommRingCat.ofHom ι)).base z
    have : pr ≫ toBase₀ = toBase ≫ Spec.map (CommRingCat.ofHom ι) := by
      show (iso.hom ≫ pullback.fst _ _) ≫ toBase₀ = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
    rw [this]

  have hspec : ∀ z : X, toBase.base z = closedPoint ↥A ↔ toBase₀.base (pr.base z) = closedPoint A₀ := by
    intro z
    rw [hsq z]
    constructor
    · intro h
      rw [h]
      exact Spec_closedPoint (f := CommRingCat.ofHom ι)
    · intro h

      have hne : (toBase.base z).asIdeal ≠ ⊥ := by
        intro hbot
        have h2 : (((Spec.map (CommRingCat.ofHom ι)).base (toBase.base z))).asIdeal = Ideal.comap ι (toBase.base z).asIdeal := rfl
        rw [h, hbot, Ideal.comap_bot_of_injective ι hι] at h2
        exact IsDiscreteValuationRing.not_a_field A₀ h2
      apply PrimeSpectrum.ext
      haveI := (toBase.base z).isPrime
      exact eq_maximalIdeal_of_ne_bot A hrk _ hne

  have hsurj : ∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → ∃ x : X, pr.base x = x₀ := by
    intro x₀ hx₀
    have h : toBase₀.base x₀ = (Spec.map (CommRingCat.ofHom ι)).base (closedPoint ↥A) := by
      rw [hx₀]; exact (Spec_closedPoint (f := CommRingCat.ofHom ι)).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := toBase₀) (g := Spec.map (CommRingCat.ofHom ι)) x₀ (closedPoint ↥A) h
    refine ⟨iso.inv.base z, ?_⟩
    show (iso.inv ≫ iso.hom ≫ pullback.fst _ _).base z = x₀
    rw [Iso.inv_hom_id_assoc]
    exact hz

  have hinj : ∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → pr.base x = pr.base y → x = y := by

    have hbij : ∀ y' : Spec (CommRingCat.of ↥A), y' = closedPoint ↥A →
        Function.Bijective ((Spec.map (CommRingCat.ofHom ι)).residueFieldMap y').hom := by
      intro y' hy'
      subst hy'
      refine ⟨RingHom.injective _, ?_⟩
      intro r
      obtain ⟨t, rfl⟩ := (Spec (CommRingCat.of ↥A)).residue_surjective (closedPoint ↥A) r

      letI algSt : Algebra ↥A ((Spec (CommRingCat.of ↥A)).presheaf.stalk (closedPoint ↥A)) :=
        (StructureSheaf.toStalk ↥A (closedPoint ↥A)).hom.toAlgebra
      haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of ↥A)).presheaf.stalk (closedPoint ↥A))
          (closedPoint ↥A).asIdeal := StructureSheaf.IsLocalization.to_stalk ↥A (closedPoint ↥A)
      obtain ⟨⟨a, s⟩, hst⟩ := IsLocalization.surj (closedPoint ↥A).asIdeal.primeCompl t
      have hsu : IsUnit (s : ↥A) := by
        by_contra hns
        exact s.2 ((IsLocalRing.mem_maximalIdeal _).mpr hns)
      obtain ⟨a₀, ha₀⟩ := hres (IsLocalRing.residue ↥A (a * ((hsu.unit⁻¹ : (↥A)ˣ) : ↥A)))
      refine ⟨(Spec (CommRingCat.of A₀)).residue _ (((Spec (CommRingCat.of A₀)).presheaf.germ ⊤ _ trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a₀)), ?_⟩

      rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply,
        Scheme.Hom.germ_stalkMap_apply]

      have hnat : (Spec.map (CommRingCat.ofHom ι)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a₀) =
          (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv (ι a₀) := by
        have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι)
        have h2 := congrArg (fun k => CommRingCat.Hom.hom k a₀) h
        exact h2.symm
      erw [hnat]

      have ht : t = algebraMap ↥A _ (a * ((hsu.unit⁻¹ : (↥A)ˣ) : ↥A)) := by
        have : t * algebraMap ↥A _ (s : ↥A) = algebraMap ↥A _ a := hst
        rw [map_mul, ← this, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
      rw [ht]
      show (Spec (CommRingCat.of ↥A)).residue (closedPoint ↥A) (algebraMap ↥A _ (ι a₀)) =
        (Spec (CommRingCat.of ↥A)).residue (closedPoint ↥A) (algebraMap ↥A _ (a * ((hsu.unit⁻¹ : (↥A)ˣ) : ↥A)))
      rw [← sub_eq_zero, ← map_sub, ← map_sub]
      apply (IsLocalRing.residue_eq_zero_iff _).mpr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        IsLocalization.AtPrime.isUnit_to_map_iff _ (closedPoint ↥A).asIdeal]
      intro hmem
      apply hmem
      show ι a₀ - a * ((hsu.unit⁻¹ : (↥A)ˣ) : ↥A) ∈ maximalIdeal ↥A
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ha₀
    intro x y hx hy hxy
    let z₁ := iso.hom.base x
    let z₂ := iso.hom.base y
    have hz : z₁ = z₂ := by
      apply Scheme.Pullback.carrierEquiv.injective
      rw [Scheme.Pullback.carrierEquiv_eq_iff]
      have hT : Scheme.Pullback.Triplet.ofPoint z₁ = Scheme.Pullback.Triplet.ofPoint z₂ := by
        apply Scheme.Pullback.Triplet.ext
        · show (iso.hom ≫ pullback.fst _ _).base x = (iso.hom ≫ pullback.fst _ _).base y
          exact hxy
        · show (iso.hom ≫ pullback.snd _ _).base x = (iso.hom ≫ pullback.snd _ _).base y
          rw [hiso, hx, hy]
      refine ⟨hT, ?_⟩

      set T := Scheme.Pullback.Triplet.ofPoint z₂ with hTdef
      have hTy : T.y = closedPoint ↥A := by
        show (iso.hom ≫ pullback.snd _ _).base y = closedPoint ↥A
        rw [hiso, hy]
      haveI : IsIso ((Spec.map (CommRingCat.ofHom ι)).residueFieldMap T.y) := by
        have hb := hbij T.y hTy
        haveI : IsIso ((forget CommRingCat).map ((Spec.map (CommRingCat.ofHom ι)).residueFieldMap T.y)) :=
          (isIso_iff_bijective _).mpr hb
        exact isIso_of_reflects_iso _ (forget CommRingCat)
      haveI : IsIso (Spec.map (((Spec (CommRingCat.of A₀)).residueFieldCongr T.hy).inv ≫
          (Spec.map (CommRingCat.ofHom ι)).residueFieldMap T.y)) := inferInstance
      haveI hiso1 : IsIso (Spec.map T.tensorInl) := T.isPullback_SpecMap_tensor.isIso_fst_of_isIso
      have hsub : Subsingleton (Spec T.tensor) := by
        constructor
        intro p₁ p₂
        have hinjb : Function.Injective (Spec.map T.tensorInl).base :=
          (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (Spec.map T.tensorInl)))).injective
        apply hinjb
        exact Subsingleton.elim _ _
      exact hsub.elim _ _
    have : x = iso.inv.base (iso.hom.base x) := by
      show x = (iso.hom ≫ iso.inv).base x
      rw [Iso.hom_inv_id]; rfl
    rw [this]
    show iso.inv.base z₁ = y
    rw [hz]
    show (iso.hom ≫ iso.inv).base y = y
    rw [Iso.hom_inv_id]; rfl

  have hspz : ∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → (x ⤳ y ↔ pr.base x ⤳ pr.base y) := by
    intro x y hx hy
    refine ⟨fun h => h.map pr.base.hom.continuous, fun h => ?_⟩
    exact E137.specializes_of_base_specializes A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
      hinj x y hx hy h
  exact ⟨hgen, hspec, hinj, hsurj, hspz⟩

end S_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing (solution)
