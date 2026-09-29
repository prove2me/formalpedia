-- Prove2me | solution 1 for AlgebraicGeometry.ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6f58ec9d-b633-5c6a-b506-775c81751c14

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

theorem ringKrullDim_le_one_of_maximalIdeal_eq_span {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (t : R) (h : maximalIdeal R = Ideal.span {t}) : ringKrullDim R ≤ 1 := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal R).trans ?_
  rw [h]
  have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (M := R) (Set.finite_singleton t)
  rw [Set.ncard_singleton] at this
  exact_mod_cast this

theorem isDiscreteValuationRing_and_ringKrullDim_eq_one_of_maximalIdeal_eq_span {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (t : R) (h : maximalIdeal R = Ideal.span {t}) (hnf : ¬ IsField R) :
    IsDiscreteValuationRing R ∧ ringKrullDim R = 1 := by
  have hP : (maximalIdeal R).IsPrincipal := ⟨t, by rw [h, Ideal.submodule_span_eq]⟩
  have hdvr : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).mpr hP
  exact ⟨hdvr, IsDiscreteValuationRing.ringKrullDim_eq_one R⟩

theorem false_of_surjective_algebraMap_of_isLocalization_of_isStandardSmoothOfRelativeDimension_one
    {k S T : Type*} [CommRing k] [CommRing S] [CommRing T] [Algebra k S] [Algebra S T] [Algebra k T] [IsScalarTower k S T]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k S] (M : Submonoid S) [IsLocalization M T] (hM : (0 : S) ∉ M)
    [Nontrivial T] (hsurj : Function.Surjective (algebraMap k T)) : False := by
  classical
  haveI : Nontrivial S := (algebraMap S T).domain_nontrivial
  haveI : Algebra.IsStandardSmooth k S := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Subsingleton (Ω[T⁄k]) := KaehlerDifferential.subsingleton_of_surjective k T hsurj
  haveI : IsLocalizedModule M (KaehlerDifferential.map k k S T) := KaehlerDifferential.isLocalizedModule_map k S T M
  have hrank : Module.rank S (Ω[S⁄k]) = 1 := by
    have := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := S) 1
    exact_mod_cast this

  let b := Module.Free.chooseBasis S (Ω[S⁄k])
  have hI : Nonempty (Module.Free.ChooseBasisIndex S (Ω[S⁄k])) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : Module.rank S (Ω[S⁄k]) = 0 := by
      rw [← b.mk_eq_rank'', Cardinal.mk_eq_zero_iff.mpr h]
    rw [h0] at hrank
    exact zero_ne_one hrank
  obtain ⟨i⟩ := hI

  have h1 : (KaehlerDifferential.map k k S T) (b i) = 0 := Subsingleton.elim _ _
  obtain ⟨m, hm⟩ := (IsLocalizedModule.eq_zero_iff M (KaehlerDifferential.map k k S T)).mp h1
  rw [Submonoid.smul_def] at hm
  have h2 := congrArg (fun v => b.repr v i) hm
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero,
    Finsupp.zero_apply] at h2
  exact hM (h2 ▸ m.2)

theorem not_isField_stalk_of_section_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    ¬ IsField (X.presheaf.stalk (σ.base (closedPoint k))) := by
  classical
  intro hfield
  letI := hfield.toField
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) (σ.base (closedPoint k))

  obtain rfl : U = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : p = c.base (σ.base (closedPoint k)) := Subsingleton.elim _ _
    rw [this]; exact e hxV

  letI alg : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := (c.appLE ⊤ V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hstd
  letI algST : Algebra Γ(X, V) (X.presheaf.stalk (σ.base (closedPoint k))) := (X.presheaf.germ V (σ.base (closedPoint k)) hxV).hom.toAlgebra
  letI algT : Algebra Γ(Spec (CommRingCat.of k), ⊤) (X.presheaf.stalk (σ.base (closedPoint k))) :=
    ((algebraMap Γ(X, V) (X.presheaf.stalk (σ.base (closedPoint k)))).comp (algebraMap Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V))).toAlgebra
  haveI : IsScalarTower Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) (X.presheaf.stalk (σ.base (closedPoint k))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (σ.base (closedPoint k))) (hV.primeIdealOf ⟨σ.base (closedPoint k), hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨σ.base (closedPoint k), hxV⟩
  have hM : (0 : Γ(X, V)) ∉ (hV.primeIdealOf ⟨σ.base (closedPoint k), hxV⟩).asIdeal.primeCompl := fun h0 => h0 (Ideal.zero_mem _)

  have hcomp : c.appTop ≫ σ.appTop = 𝟙 _ := by
    have := Scheme.Hom.comp_appTop σ c
    rw [hσ] at this
    simpa using this.symm
  have hgerm : ∀ s : (Spec (CommRingCat.of k)).presheaf.stalk (closedPoint k), ∃ a : Γ(Spec (CommRingCat.of k), ⊤),
      ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial).hom a = s := by
    intro s
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ((stalkClosedPointIso (CommRingCat.of k)).hom s), ?_⟩
    have h := germ_stalkClosedPointIso_hom (CommRingCat.of k)
    have h' : (Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial =
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (stalkClosedPointIso (CommRingCat.of k)).inv := by
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h']
    simp
  have hsurj : Function.Surjective (algebraMap Γ(Spec (CommRingCat.of k), ⊤) (X.presheaf.stalk (σ.base (closedPoint k)))) := by
    intro t
    obtain ⟨a, ha⟩ := hgerm ((σ.stalkMap (closedPoint k)).hom t)
    refine ⟨a, (σ.stalkMap (closedPoint k)).hom.injective ?_⟩
    rw [← ha]
    change (σ.stalkMap (closedPoint k)).hom ((X.presheaf.germ V (σ.base (closedPoint k)) hxV).hom ((c.appLE ⊤ V e).hom a)) = _
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    erw [Scheme.Hom.germ_stalkMap_apply σ ⊤ (closedPoint k) trivial]
    change ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint ↑k) trivial).hom ((c.appTop ≫ σ.appTop).hom a) = _
    rw [hcomp]
    rfl
  exact false_of_surjective_algebraMap_of_isLocalization_of_isStandardSmoothOfRelativeDimension_one
    (k := Γ(Spec (CommRingCat.of k), ⊤)) (S := Γ(X, V)) (T := X.presheaf.stalk (σ.base (closedPoint k))) (hV.primeIdealOf ⟨σ.base (closedPoint k), hxV⟩).asIdeal.primeCompl hM hsurj

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    ringKrullDim (X.presheaf.stalk (σ.base (closedPoint k))) = 1 ∧
      ∃ _ : IsDomain (X.presheaf.stalk (σ.base (closedPoint k))), IsDiscreteValuationRing (X.presheaf.stalk (σ.base (closedPoint k))) := by
  haveI : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  haveI hreg : IsRegularLocalRing (X.presheaf.stalk (σ.base (closedPoint k))) := Smooth.isRegularLocalRing_stalk (f := c) _
  obtain ⟨t, -, hmax⟩ := exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one c σ hσ
  have hbot : maximalIdeal k = ⊥ := (isField_iff_maximalIdeal_eq.mp (Field.toIsField k))
  rw [hbot, Ideal.map_bot, sup_bot_eq] at hmax
  have hle := ringKrullDim_le_one_of_maximalIdeal_eq_span t hmax
  obtain ⟨hdom, -⟩ := IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one (X.presheaf.stalk (σ.base (closedPoint k))) hle
  have hnf := not_isField_stalk_of_section_of_smoothOfRelativeDimension_one c σ hσ
  obtain ⟨hdvr, hdim⟩ := isDiscreteValuationRing_and_ringKrullDim_eq_one_of_maximalIdeal_eq_span t hmax hnf
  exact ⟨hdim, hdom, hdvr⟩

#print axioms solution

end S_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one (solution)
