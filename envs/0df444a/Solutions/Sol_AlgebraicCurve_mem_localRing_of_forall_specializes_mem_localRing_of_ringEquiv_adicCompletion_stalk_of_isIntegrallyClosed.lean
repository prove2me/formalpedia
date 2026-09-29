-- Prove2me | solution 1 for AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ac918d07-e893-5055-a5d8-36928b8737c8

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk
import Theorems.Thm_IsIntegrallyClosed_of_faithfullyFlat
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Theorems.Thm_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

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

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
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
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))
    :
    ∀ f : F, (∀ y : X, y ⤳ x → y ≠ x → f ∈ SemistableModel.localRing X φ y) → f ∈ SemistableModel.localRing X φ x := by
  intro f hf
  classical

  obtain ⟨A₁, _i1, _i2, _i3, ι₁', _i4, ι₁, _i5, hι₁, hcomp, ϖ₁, hϖ₁, X₁, _i6, f₁, g₁, hsq, e₁, he₁, he₁', hgen, u, hu⟩ :=
    AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he f

  obtain ⟨hx₁, hN, -, -, hdim, -, hflat, hprimes⟩ :=
    AlgebraicCurve.stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he
      A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'
  set π : X ⟶ X₁ := e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) with hπ
  set x₁ : X₁ := π.base x with hx₁def
  haveI : IsNoetherianRing (X₁.presheaf.stalk x₁) := hN
  haveI : Flat π := hflat

  have hnorm : IsIntegrallyClosed (X₁.presheaf.stalk x₁) := by
    letI alg : Algebra (X₁.presheaf.stalk x₁) (X.presheaf.stalk x) := (π.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (X₁.presheaf.stalk x₁) (X.presheaf.stalk x) := Flat.stalkMap π x
    haveI : IsLocalHom (algebraMap (X₁.presheaf.stalk x₁) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
    haveI : Module.FaithfullyFlat (X₁.presheaf.stalk x₁) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    haveI : IsIntegrallyClosed (X.presheaf.stalk x) := hn x
    exact IsIntegrallyClosed.of_faithfullyFlat (X₁.presheaf.stalk x₁) (X.presheaf.stalk x)
  haveI := hnorm

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

  have hkrull : ∀ (p : Ideal (X₁.presheaf.stalk x₁)) [p.IsPrime], p.height = 1 →
      ∃ r s : X₁.presheaf.stalk x₁, s ∉ p ∧ u * algebraMap _ X₁.functionField s = algebraMap _ X₁.functionField r := by
    intro p _ hp1
    have hpne : p ≠ maximalIdeal (X₁.presheaf.stalk x₁) := by
      intro hpeq
      subst hpeq
      have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X₁.presheaf.stalk x₁)
      rw [hp1] at h
      rw [← h] at hdim
      simp at hdim
    obtain ⟨y, hy, hyx, hpy⟩ := hprimes p ‹_› hpne
    obtain ⟨t, ht⟩ := hf y hy hyx

    have hu' : u ∈ (algebraMap (X₁.presheaf.stalk (π.base y)) X₁.functionField).range := by
      letI algKL : Algebra X₁.functionField X.functionField := ψ.toAlgebra
      letI algRL : Algebra (X₁.presheaf.stalk (π.base y)) X.functionField :=
        (ψ.comp (algebraMap (X₁.presheaf.stalk (π.base y)) X₁.functionField)).toAlgebra
      haveI : IsScalarTower (X₁.presheaf.stalk (π.base y)) X₁.functionField X.functionField :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom (π.stalkMap y).hom (Flat.stalkMap π y)
        X₁.functionField X.functionField (fun r => keyPt y r) u ⟨t, ?_⟩
      show algebraMap (X.presheaf.stalk y) X.functionField t = ψ u
      have : φ f = ψ u := hu
      rw [← this, ← ht]
      show _ = φ (φ.symm _)
      rw [RingEquiv.apply_symm_apply]
    obtain ⟨r', hr'⟩ := hu'

    have hyspec : π.base y ⤳ x₁ := hy.map π.base.hom.continuous
    have hp' : p = (maximalIdeal (X₁.presheaf.stalk (π.base y))).comap (X₁.presheaf.stalkSpecializes hyspec).hom := by
      rw [hpy]
      ext s
      simp only [Ideal.mem_comap, RingHom.comp_apply]
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply π y x hy]
      rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
        isUnit_map_iff]

    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X₁.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₁) isOpen_univ
    have hyU : π.base y ∈ U := hyspec.mem_open U.2 hxU
    letI algU := TopCat.Presheaf.algebra_section_stalk X₁.presheaf (⟨π.base y, hyU⟩ : U)
    haveI := hU.isLocalization_stalk ⟨π.base y, hyU⟩
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨π.base y, hyU⟩).asIdeal.primeCompl r'
    have hgerm : ∀ c : Γ(X₁, U), (X₁.presheaf.stalkSpecializes hyspec).hom (X₁.presheaf.germ U x₁ hxU c) =
        X₁.presheaf.germ U (π.base y) hyU c := fun c => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have halg : ∀ c : Γ(X₁, U), algebraMap Γ(X₁, U) (X₁.presheaf.stalk (π.base y)) c = X₁.presheaf.germ U (π.base y) hyU c :=
      fun c => rfl
    refine ⟨X₁.presheaf.germ U x₁ hxU a, X₁.presheaf.germ U x₁ hxU b, ?_, ?_⟩
    · rw [hp', Ideal.mem_comap, hgerm]
      intro hmem
      have hunit : IsUnit (X₁.presheaf.germ U (π.base y) hyU (b : Γ(X₁, U))) := by
        rw [← halg]; exact IsLocalization.map_units _ b
      exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit
    · have e1 : ∀ c : Γ(X₁, U), algebraMap (X₁.presheaf.stalk x₁) X₁.functionField (X₁.presheaf.germ U x₁ hxU c) =
          algebraMap (X₁.presheaf.stalk (π.base y)) X₁.functionField (X₁.presheaf.germ U (π.base y) hyU c) := by
        intro c
        show (X₁.presheaf.germ U _ hxU ≫ X₁.presheaf.stalkSpecializes _).hom c =
          (X₁.presheaf.germ U _ hyU ≫ X₁.presheaf.stalkSpecializes _).hom c
        rw [TopCat.Presheaf.germ_stalkSpecializes]
        try rw [TopCat.Presheaf.germ_stalkSpecializes]
      rw [e1, e1, ← hr', ← map_mul]
      congr 1
      all_goals first | exact hab | (rw [← halg, ← halg]; exact hab)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one X₁.functionField u hkrull

  refine ⟨(π.stalkMap x) r, ?_⟩
  apply φ.injective
  show φ (φ.symm (algebraMap (X.presheaf.stalk x) X.functionField ((π.stalkMap x) r))) = φ f
  rw [RingEquiv.apply_symm_apply, hu, ← hr]
  exact (keyPt x r).symm

end S_AlgebraicCurve_mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed (solution)
