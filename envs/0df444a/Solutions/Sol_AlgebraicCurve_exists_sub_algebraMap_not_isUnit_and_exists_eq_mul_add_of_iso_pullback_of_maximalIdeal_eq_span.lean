-- Prove2me | solution 1 for AlgebraicCurve.exists_sub_algebraMap_not_isUnit_and_exists_eq_mul_add_of_iso_pullback_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d3f4c374-ef0c-5918-a018-a7fbc94080e2

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk
import Theorems.Thm_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_sub_algebraMap_not_isUnit_and_exists_eq_mul_add_of_iso_pullback_of_maximalIdeal_eq_span
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

namespace LevelFibreE133

theorem stalkMap_baseToFunctionField {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : X ⟶ Y) (fY : Y ⟶ Spec (CommRingCat.of R)) (fX : X ⟶ Spec (CommRingCat.of S))
    (hsq : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hgen : g.base (genericPoint X) = genericPoint Y) (r : R) :
    (g.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
      (SemistableModel.baseToFunctionField fY r)) = SemistableModel.baseToFunctionField fX (φ r) := by
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ r) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ : CommRingCat.of R ⟶ CommRingCat.of S)
    have h2 := congrArg (fun k => CommRingCat.Hom.hom k r) h
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] using h2
  have hsq' : fY.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom φ)).appTop ≫ fX.appTop := by
    rw [← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop]
  have hsq'' := congrArg (fun k => CommRingCat.Hom.hom k ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hsq'
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hsq''
  simp only [SemistableModel.baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  rw [hnat, ← hsq'']
  rw [← CommRingCat.comp_apply (Y.presheaf.germ ⊤ _ _), TopCat.Presheaf.germ_stalkSpecializes]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

end LevelFibreE133

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (hres₀ : Function.Surjective ((IsLocalRing.residue ↥A).comp ι₀))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w) (hwu : IsUnit ((w : ℕ) : A₀))
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))

    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (θ : X₀.presheaf.stalk ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x) ≃+* ↥𝒩₀)
    (hθv : ∀ g : X₀.presheaf.stalk ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x),
      ((θ g : ↥𝒩₀) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField
        (((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).stalkMap x).hom g)))
    (hle : 𝒩₀ ≤ SemistableModel.localRing X φ x)
    (hAconst : ∀ a : ↥A, algebraMap L F (a : L) ∈ SemistableModel.localRing X φ x)

    (xn yn t : ↥𝒩₀) (ht : (t : F) = algebraMap L F ((ι₀ ϖ₀ : ↥A) : L))
    (hmax₀ : maximalIdeal ↥𝒩₀ = Ideal.span {xn, yn, t}) :
    (∀ q : ↥(SemistableModel.localRing X φ x), ∃ a : ↥A,
      ¬ IsUnit (q - ⟨algebraMap L F (a : L), hAconst a⟩)) ∧
    (∀ q : ↥(SemistableModel.localRing X φ x), ¬ IsUnit q →
      ∃ (α β γ δ : ↥(SemistableModel.localRing X φ x)) (p : ↥A), p ∈ maximalIdeal ↥A ∧
        q = ⟨(xn : F), hle xn.2⟩ * α + ⟨(yn : F), hle yn.2⟩ * β + ⟨(t : F), hle t.2⟩ * γ +
          ⟨algebraMap L F (p : L), hAconst p⟩ * δ) := by
  classical

  let θ₀ : ↑(X.presheaf.stalk x) →+* F := φ.symm.toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  let θx : ↑(X.presheaf.stalk x) →+* ↥(SemistableModel.localRing X φ x) :=
    { toFun := fun s => ⟨θ₀ s, ⟨s, rfl⟩⟩
      map_one' := Subtype.ext (map_one θ₀)
      map_mul' := fun a b => Subtype.ext (map_mul θ₀ a b)
      map_zero' := Subtype.ext (map_zero θ₀)
      map_add' := fun a b => Subtype.ext (map_add θ₀ a b) }
  have hθxv : ∀ s, ((θx s : ↥(SemistableModel.localRing X φ x)) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s) :=
    fun s => rfl
  have hθxinj : Function.Injective θx := fun a b h => by
    have : θ₀ a = θ₀ b := congrArg (fun z : ↥(SemistableModel.localRing X φ x) => (z : F)) h
    exact (φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)) this
  have hθxsurj : Function.Surjective θx := fun q => by
    obtain ⟨s, hs⟩ := q.2
    exact ⟨s, Subtype.ext hs⟩
  have hθxunit : ∀ s, IsUnit (θx s) ↔ IsUnit s := fun s =>
    ⟨fun h => by
      obtain ⟨s', hs'⟩ := hθxsurj ((h.unit⁻¹ : (↥(SemistableModel.localRing X φ x))ˣ) : _)
      refine isUnit_iff_exists_inv.mpr ⟨s', hθxinj ?_⟩
      rw [map_mul, map_one, hs']
      exact h.mul_val_inv,
     fun h => h.map θx⟩
  suffices main : ∀ q : ↥(SemistableModel.localRing X φ x),
      (∃ a : ↥A, ¬ IsUnit (q - ⟨algebraMap L F (a : L), hAconst a⟩)) ∧
      (¬ IsUnit q → ∃ (α β γ δ : ↥(SemistableModel.localRing X φ x)) (p : ↥A), p ∈ maximalIdeal ↥A ∧
        q = ⟨(xn : F), hle xn.2⟩ * α + ⟨(yn : F), hle yn.2⟩ * β + ⟨(t : F), hle t.2⟩ * γ +
          ⟨algebraMap L F (p : L), hAconst p⟩ * δ) from
    ⟨fun q => (main q).1, fun q hq => (main q).2 hq⟩
  intro q

  revert θ hθv

  obtain ⟨sq, hsq⟩ := q.2
  obtain ⟨A₁, _i1, _i2, _i3, ι₁', _i4, ι₁, _i5, hι₁, hcomp, ϖ₁, hϖ₁, X₁, _i6, f₁, g₁, hsqP, e₁, he₁, he₁', hgen, u, hu⟩ :=
    AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he (q : F)

  obtain ⟨hx₁, hN, hfib1, hfib2, -, -, hflat, -⟩ :=
    AlgebraicCurve.stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he
      A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsqP e₁ he₁ he₁'
  rw [← he₁']
  set π : X ⟶ X₁ := e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) with hπ
  intro θ hθv
  haveI : Flat π := hflat

  let ψ : X₁.functionField →+* X.functionField :=
    (X₁.presheaf.stalkSpecializes (specializes_of_eq hgen) ≫ π.stalkMap (genericPoint X)).hom
  have keyPt : ∀ (z : X) (r : X₁.presheaf.stalk (π.base z)),
      ψ (algebraMap (X₁.presheaf.stalk (π.base z)) X₁.functionField r) =
        algebraMap (X.presheaf.stalk z) X.functionField ((π.stalkMap z) r) := by
    intro z r
    show (X₁.presheaf.stalkSpecializes (genericPoint_specializes (π.base z)) ≫
      X₁.presheaf.stalkSpecializes (specializes_of_eq hgen) ≫ π.stalkMap (genericPoint X)).hom r =
      (π.stalkMap z ≫ X.presheaf.stalkSpecializes (genericPoint_specializes z)).hom r
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
      Scheme.Hom.stalkSpecializes_stalkMap π (genericPoint X) z (genericPoint_specializes z)]

  have hu' : u ∈ (algebraMap (X₁.presheaf.stalk (π.base x)) X₁.functionField).range := by
    letI algKL : Algebra X₁.functionField X.functionField := ψ.toAlgebra
    letI algRL : Algebra (X₁.presheaf.stalk (π.base x)) X.functionField :=
      (ψ.comp (algebraMap (X₁.presheaf.stalk (π.base x)) X₁.functionField)).toAlgebra
    haveI : IsScalarTower (X₁.presheaf.stalk (π.base x)) X₁.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    refine IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom (π.stalkMap x).hom (Flat.stalkMap π x)
      X₁.functionField X.functionField (fun r => keyPt x r) u ⟨sq, ?_⟩
    show algebraMap (X.presheaf.stalk x) X.functionField sq = ψ u
    have : φ (q : F) = ψ u := hu
    rw [← this, ← hsq]
    show _ = φ (φ.symm _)
    rw [RingEquiv.apply_symm_apply]
  obtain ⟨r', hr'⟩ := hu'
  have hρq : θx ((π.stalkMap x) r') = q := by
    apply Subtype.ext
    have hψu : ψ u = φ (q : F) := hu.symm
    rw [hθxv, ← keyPt x r', hr', hψu, RingEquiv.symm_apply_apply]

  have hsqπ : π ≫ f₁ = toBase ≫ Spec.map (CommRingCat.ofHom ι₁) := by
    rw [hπ, Category.assoc, pullback.condition, ← Category.assoc, he₁]
  have hconst : ∀ a₁ : A₁, θx ((π.stalkMap x) ((X₁.presheaf.germ ⊤ (π.base x) trivial).hom
      (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a₁)))) =
      ⟨algebraMap L F ((ι₁ a₁ : ↥A) : L), hAconst (ι₁ a₁)⟩ := by
    intro a₁
    apply Subtype.ext
    rw [hθxv, ← keyPt x]
    have h1 : algebraMap (X₁.presheaf.stalk (π.base x)) X₁.functionField ((X₁.presheaf.germ ⊤ (π.base x) trivial).hom
        (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a₁))) = SemistableModel.baseToFunctionField f₁ a₁ := by
      show (X₁.presheaf.germ ⊤ (π.base x) trivial ≫ X₁.presheaf.stalkSpecializes _).hom _ = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [h1]
    show φ.symm ((π.stalkMap (genericPoint X)).hom ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
      (SemistableModel.baseToFunctionField f₁ a₁))) = algebraMap L F ((ι₁ a₁ : ↥A) : L)
    rw [LevelFibreE133.stalkMap_baseToFunctionField ι₁ π f₁ toBase hsqπ hgen a₁, ← hφ, RingEquiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨a₁, ha₁⟩ := hfib1 r'
    refine ⟨ι₁ a₁, fun hunit => ha₁ ?_⟩
    rw [← hρq, ← hconst, ← map_sub, hθxunit, ← map_sub] at hunit
    exact isUnit_of_map_unit (π.stalkMap x).hom _ hunit
  ·
    intro hq

    have hr'nu : r' ∈ maximalIdeal (X₁.presheaf.stalk (π.base x)) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu1
      apply hq
      rw [← hρq, hθxunit]
      exact hu1.map (π.stalkMap x).hom
    have hmem := hfib2 hr'nu

    let ρ : ↑(X₁.presheaf.stalk (π.base x)) →+* ↥(SemistableModel.localRing X φ x) := θx.comp (π.stalkMap x).hom
    have hq1 : q ∈ Ideal.map ρ ((maximalIdeal (X₀.presheaf.stalk (g₁.base (π.base x)))).map (g₁.stalkMap (π.base x)).hom ⊔
        Ideal.span {(X₁.presheaf.germ ⊤ (π.base x) trivial).hom
          (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))}) := by
      rw [← hρq]
      exact Ideal.mem_map_of_mem ρ hmem
    rw [Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton] at hq1
    have hρc : ρ ((X₁.presheaf.germ ⊤ (π.base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))) =
        ⟨algebraMap L F ((ι₁ ϖ₁ : ↥A) : L), hAconst (ι₁ ϖ₁)⟩ := hconst ϖ₁
    rw [hρc] at hq1

    have hρg : ∀ g0 : X₀.presheaf.stalk (g₁.base (π.base x)),
        (ρ.comp (g₁.stalkMap (π.base x)).hom) g0 = ⟨((θ g0 : ↥𝒩₀) : F), hle (θ g0).2⟩ := by
      intro g0
      apply Subtype.ext
      show ((θx ((π.stalkMap x) ((g₁.stalkMap (π.base x)) g0)) : ↥(SemistableModel.localRing X φ x)) : F) = ((θ g0 : ↥𝒩₀) : F)
      rw [hθxv, hθv]
      congr 2
      rw [Scheme.Hom.stalkMap_comp π g₁ x]
      rfl
    have hmaple : (maximalIdeal (X₀.presheaf.stalk (g₁.base (π.base x)))).map (ρ.comp (g₁.stalkMap (π.base x)).hom) ≤
        Ideal.span {(⟨(xn : F), hle xn.2⟩ : ↥(SemistableModel.localRing X φ x)), ⟨(yn : F), hle yn.2⟩, ⟨(t : F), hle t.2⟩} := by
      rw [Ideal.map_le_iff_le_comap]
      intro g0 hg0
      rw [Ideal.mem_comap, hρg]

      have hθm : θ g0 ∈ maximalIdeal ↥𝒩₀ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg0 ⊢
        intro hu1
        apply hg0
        have h2 : IsUnit (θ.symm (θ g0)) := hu1.map θ.symm
        rwa [RingEquiv.symm_apply_apply] at h2
      rw [hmax₀] at hθm
      have himg := Ideal.mem_map_of_mem (Subring.inclusion hle) hθm
      rw [Ideal.map_span] at himg
      have hset : ⇑(Subring.inclusion hle) '' {xn, yn, t} =
          {(⟨(xn : F), hle xn.2⟩ : ↥(SemistableModel.localRing X φ x)), ⟨(yn : F), hle yn.2⟩, ⟨(t : F), hle t.2⟩} := by
        simp only [Set.image_insert_eq, Set.image_singleton]
        rfl
      rw [hset] at himg
      exact himg
    have hq2 : q ∈ Ideal.span {(⟨(xn : F), hle xn.2⟩ : ↥(SemistableModel.localRing X φ x)), ⟨(yn : F), hle yn.2⟩, ⟨(t : F), hle t.2⟩} ⊔
        Ideal.span {(⟨algebraMap L F ((ι₁ ϖ₁ : ↥A) : L), hAconst (ι₁ ϖ₁)⟩ : ↥(SemistableModel.localRing X φ x))} :=
      (sup_le_sup_right hmaple _) hq1

    have hp : ι₁ ϖ₁ ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu1
      have : ϖ₁ ∈ maximalIdeal A₁ := by rw [hϖ₁]; exact Ideal.mem_span_singleton_self ϖ₁
      exact ((IsLocalRing.mem_maximalIdeal _).mp this) (isUnit_of_map_unit ι₁ ϖ₁ hu1)

    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hq2
    obtain ⟨α, y₁, hy₁, rfl⟩ := Ideal.mem_span_insert.mp hy
    obtain ⟨β, y₂, hy₂, rfl⟩ := Ideal.mem_span_insert.mp hy₁
    obtain ⟨γ, rfl⟩ := Ideal.mem_span_singleton'.mp hy₂
    obtain ⟨δ, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨α, β, γ, δ, ι₁ ϖ₁, hp, ?_⟩
    rw [← hyz]
    ring

end S_AlgebraicCurve_exists_sub_algebraMap_not_isUnit_and_exists_eq_mul_add_of_iso_pullback_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_AlgebraicCurve_exists_sub_algebraMap_not_isUnit_and_exists_eq_mul_add_of_iso_pullback_of_maximalIdeal_eq_span (solution)
