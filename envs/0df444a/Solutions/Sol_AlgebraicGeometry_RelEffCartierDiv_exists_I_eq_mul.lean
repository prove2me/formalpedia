-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a0b3b226-742c-530c-af5d-5e75b519f205

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Colon
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv
import Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DivisorSum

section colon

variable {B : Type*} [CommRing B]

p2m_open "Ideal AlgebraicGeometry.Ideal"

theorem eq_span_singleton_mul_colon (K : Ideal B) (t : B) (h : K ≤ span {t}) :
    K = span {t} * K.colon {t} := by
  refine le_antisymm (fun x hx => ?_) (span_singleton_mul_le_iff.mpr fun z hz => ?_)
  · obtain ⟨a, rfl⟩ := mem_span_singleton'.mp (h hx)
    exact mem_span_singleton_mul.mpr ⟨a, Submodule.mem_colon_singleton.mpr hx, mul_comm t a⟩
  · have := Submodule.mem_colon_singleton.mp hz
    rwa [smul_eq_mul, mul_comm] at this

theorem colon_span_singleton_mul {t : B} (ht : t ∈ nonZeroDivisors B) (J : Ideal B) :
    (span {t} * J).colon {t} = J := by
  refine le_antisymm (fun x hx => ?_) fun x hx => ?_
  · have hx' : t * x ∈ span {t} * J := by
      simpa [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp hx
    obtain ⟨j, hj, e⟩ := mem_span_singleton_mul.mp hx'
    obtain rfl : j = x := by
      have h0 : (j - x) * t = 0 := by rw [sub_mul, sub_eq_zero, mul_comm j, e, mul_comm]
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ht).2 _ h0)
    exact hj
  · exact Submodule.mem_colon_singleton.mpr (by
      rw [smul_eq_mul, mul_comm x t]; exact mul_mem_mul (mem_span_singleton_self t) hx)

theorem mul_mem_span_singleton_mul_iff {t : B} (ht : t ∈ nonZeroDivisors B) (J : Ideal B)
    (y : B) : y * t ∈ span {t} * J ↔ y ∈ J := by
  constructor
  · intro h
    have hy : y ∈ (span {t} * J).colon {t} :=
      Submodule.mem_colon_singleton.mpr (by rwa [smul_eq_mul])
    rwa [colon_span_singleton_mul ht J] at hy
  · intro hy
    rw [mul_comm y t]
    exact mul_mem_mul (mem_span_singleton_self t) hy

theorem ker_mkQ_comp_toSpanSingleton (K : Ideal B) (t : B) :
    LinearMap.ker (K.mkQ ∘ₗ LinearMap.toSpanSingleton B B t) = K.colon {t} := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon_singleton]

theorem range_mkQ_comp_toSpanSingleton (K : Ideal B) (t : B) :
    LinearMap.range (K.mkQ ∘ₗ LinearMap.toSpanSingleton B B t) =
      Submodule.map K.mkQ (Ideal.span {t}) := by
  rw [LinearMap.range_comp, ← LinearMap.span_singleton_eq_range]

noncomputable def quotColonEquivMapSpan (K : Ideal B) (t : B) :
    (B ⧸ K.colon {t}) ≃ₗ[B] ↥(Submodule.map K.mkQ (Ideal.span {t})) :=
  Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_toSpanSingleton K t).symm ≪≫ₗ
    (K.mkQ ∘ₗ LinearMap.toSpanSingleton B B t).quotKerEquivRange ≪≫ₗ
      LinearEquiv.ofEq _ _ (range_mkQ_comp_toSpanSingleton K t)

noncomputable def quotEquivMapSpanOfMul {t : B} (ht : t ∈ nonZeroDivisors B) (J : Ideal B) :
    (B ⧸ J) ≃ₗ[B] ↥(Submodule.map (span {t} * J).mkQ (Ideal.span {t})) :=
  Submodule.quotEquivOfEq _ _ (colon_span_singleton_mul ht J).symm ≪≫ₗ
    quotColonEquivMapSpan (span {t} * J) t

@[scoped simp] theorem quotEquivMapSpanOfMul_apply_mk {t : B} (ht : t ∈ nonZeroDivisors B)
    (J : Ideal B) (x : B) :
    ((quotEquivMapSpanOfMul ht J (Ideal.Quotient.mk J x) : ↥(Submodule.map (span {t} * J).mkQ
      (Ideal.span {t}))) : B ⧸ span {t} * J) = Ideal.Quotient.mk (span {t} * J) (x * t) := by
  rfl

theorem map_mkQ_eq_ker_factor {K I : Ideal B} (h : K ≤ I) :
    Submodule.map K.mkQ I =
      (RingHom.ker (Ideal.Quotient.factor h)).restrictScalars B := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Submodule.restrictScalars_mem, RingHom.mem_ker, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨y, hy, e⟩
    have : Ideal.Quotient.mk K y = Ideal.Quotient.mk K x := e
    rw [Ideal.Quotient.eq] at this
    simpa using I.sub_mem hy (h this)
  · intro hx
    exact ⟨x, hx, rfl⟩

end colon

section split

variable {R : Type*} [CommRing R] {M P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

theorem nonempty_linearEquiv_ker_prod [Module.Projective R P] (f : M →ₗ[R] P)
    (hf : Function.Surjective f) : Nonempty (M ≃ₗ[R] (LinearMap.ker f × P)) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hfs : ∀ b, f (s b) = b := fun b => LinearMap.congr_fun hs b
  have hmem : ∀ a : M, a - s (f a) ∈ LinearMap.ker f := fun a => by
    simp [LinearMap.mem_ker, hfs]
  refine ⟨LinearEquiv.ofLinear
    (LinearMap.prod ((LinearMap.id - s ∘ₗ f).codRestrict _ hmem) f)
    ((LinearMap.ker f).subtype ∘ₗ LinearMap.fst R _ P + s ∘ₗ LinearMap.snd R _ P) ?_ ?_⟩
  · apply LinearMap.ext
    rintro ⟨⟨k, hk⟩, b⟩
    have hk0 : f k = 0 := LinearMap.mem_ker.mp hk
    ext
    · simp [hk0, hfs]
    · simp [hk0, hfs]
  · apply LinearMap.ext
    intro a
    simp

theorem projective_of_projective_ker [Module.Projective R P] (f : M →ₗ[R] P)
    (hf : Function.Surjective f) [Module.Projective R (LinearMap.ker f)] :
    Module.Projective R M := by
  obtain ⟨e⟩ := nonempty_linearEquiv_ker_prod f hf
  exact Module.Projective.of_equiv e.symm

theorem flat_ker [Module.Projective R P] [Module.Flat R M] (f : M →ₗ[R] P)
    (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_ker_prod f hf
  haveI : Module.Flat R (LinearMap.ker f × P) := Module.Flat.of_linearEquiv e.symm
  exact Module.Flat.of_retract (LinearMap.inl R _ P) (LinearMap.fst R _ P) (by ext; simp)

theorem finite_ker [Module.Projective R P] [Module.Finite R M] (f : M →ₗ[R] P)
    (hf : Function.Surjective f) : Module.Finite R (LinearMap.ker f) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_ker_prod f hf
  haveI : Module.Finite R (LinearMap.ker f × P) := Module.Finite.equiv e
  exact Module.Finite.of_surjective (LinearMap.fst R _ P) Prod.fst_surjective

theorem rankAtStalk_eq_ker_add [Module.Projective R P] [Module.Finite R M] [Module.Flat R M]
    [Module.Finite R P] (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk (LinearMap.ker f) + Module.rankAtStalk P := by
  obtain ⟨e⟩ := nonempty_linearEquiv_ker_prod f hf
  haveI := finite_ker f hf
  haveI := flat_ker f hf
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]

end split

section projective

theorem projective_of_finitePresentation_of_flat {R : Type*} [CommRing R] (P : Type*)
    [AddCommGroup P] [Module R P] [Module.Flat R P] [Module.FinitePresentation R P] :
    Module.Projective R P :=
  Module.Flat.projective_of_finitePresentation

end projective

section generic

p2m_open "AlgebraicGeometry.Scheme"

theorem isClosedImmersion_inclusion {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  haveI : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι

universe v in

theorem flat_localizedModule_of_flat {R₀ A : Type v} [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (p : Submonoid A)
    {M : Type v} [AddCommGroup M] [Module R₀ M] [Module A M] [IsScalarTower R₀ A M]
    [Module.Flat R₀ M] : Module.Flat R₀ (LocalizedModule p M) := by
  rw [Module.Flat.iff_lTensor_exact]
  intro N N' N'' _ _ _ _ _ _ f g hfg
  have hM : Function.Exact (LinearMap.lTensor M f) (LinearMap.lTensor M g) :=
    Module.Flat.iff_lTensor_exact.mp ‹Module.Flat R₀ M› hfg
  have hM' : Function.Exact (TensorProduct.AlgebraTensorModule.lTensor A M f)
      (TensorProduct.AlgebraTensorModule.lTensor A M g) := by
    simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hM
  have key := IsLocalizedModule.map_exact p
      (TensorProduct.AlgebraTensorModule.rTensor R₀ N (LocalizedModule.mkLinearMap p M))
      (TensorProduct.AlgebraTensorModule.rTensor R₀ N' (LocalizedModule.mkLinearMap p M))
      (TensorProduct.AlgebraTensorModule.rTensor R₀ N'' (LocalizedModule.mkLinearMap p M))
      (TensorProduct.AlgebraTensorModule.lTensor A M f)
      (TensorProduct.AlgebraTensorModule.lTensor A M g) hM'
  rw [IsLocalizedModule.map_lTensor, IsLocalizedModule.map_lTensor] at key
  simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using key

theorem hom_predicate_seam {Z Y : Scheme.{u}} (q : Z ⟶ Y) (U : Y.Opens)
    (P : ∀ {R S : CommRingCat.{u}}, (R ⟶ S) → Prop) :
    P ((q ∣_ U).appTop) ↔ P (q.appLE U (q ⁻¹ᵁ U) le_rfl) := by
  rw [morphismRestrict_appTop, q.app_eq_appLE, Scheme.Hom.appLE_map]
  exact (Scheme.Hom.appLE_congr (f := q) le_rfl
    (Scheme.Opens.ι_image_top U).symm
    (show q ⁻¹ᵁ U = (q ⁻¹ᵁ U).ι ''ᵁ ((q ∣_ U) ⁻¹ᵁ ⊤) by
      rw [TopologicalSpace.Opens.map_top, Scheme.Opens.ι_image_top]) P).symm

set_option backward.isDefEq.respectTransparency false in

theorem mk_subschemeObjIso_inclusion_appLE {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I ≤ J) (W : X.affineOpens) :
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) ≫ ((I.subschemeObjIso W).inv ≫
      ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ W.1) ≫
        J.subscheme.presheaf.map (eqToHom (by
          rw [← Scheme.IdealSheafData.inclusion_subschemeι h]; rfl :
            J.subschemeι ⁻¹ᵁ W.1 =
              Scheme.IdealSheafData.inclusion h ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ W.1))).op) ≫
      (J.subschemeObjIso W).hom) =
    CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal W)) := by
  have h1 := Scheme.Hom.congr_app (Scheme.IdealSheafData.inclusion_subschemeι h) W.1
  rw [Scheme.Hom.comp_app] at h1
  simp only [← Category.assoc]
  rw [← Scheme.IdealSheafData.subschemeι_app, h1]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
    op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Scheme.IdealSheafData.subschemeι_app, Iso.inv_hom_id]

theorem presheaf_map_injective_of_eq {X : Scheme.{u}} {U V : X.Opens} (hUV : U = V)
    (i : Opposite.op V ⟶ Opposite.op U) : Function.Injective (X.presheaf.map i).hom := by
  subst hUV
  obtain rfl : i = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [CategoryTheory.Functor.map_id]
  exact fun a b hab => hab

set_option backward.isDefEq.respectTransparency false in

theorem inclusion_app_mk_eq_zero_iff {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (W : X.affineOpens) (y : Γ(X, W.1)) :
    ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ W.1)).hom
        ((I.subschemeObjIso W).inv.hom (Ideal.Quotient.mk (I.ideal W) y)) = 0 ↔
      y ∈ J.ideal W := by
  have KB := mk_subschemeObjIso_inclusion_appLE h W

  obtain ⟨φ, hφ, hφinj⟩ : ∃ φ : Γ(J.subscheme, Scheme.IdealSheafData.inclusion h ⁻¹ᵁ
        (I.subschemeι ⁻¹ᵁ W.1)) →+* (Γ(X, W.1) ⧸ J.ideal W),
      (∀ y, φ (((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ W.1)).hom
        ((I.subschemeObjIso W).inv.hom (Ideal.Quotient.mk (I.ideal W) y))) =
          Ideal.Quotient.mk (J.ideal W) y) ∧ Function.Injective φ := by
    refine ⟨(J.subscheme.presheaf.map (eqToHom (by
        rw [← Scheme.IdealSheafData.inclusion_subschemeι h]; rfl :
          J.subschemeι ⁻¹ᵁ W.1 =
            Scheme.IdealSheafData.inclusion h ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ W.1))).op ≫
        (J.subschemeObjIso W).hom).hom, fun y => ?_, ?_⟩
    · have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom KB) y
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this
    · exact (ConcreteCategory.bijective_of_isIso _).1
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ y, map_eq_zero_iff φ hφinj]

theorem subschemeObjIso_inv_mk_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (W : X.affineOpens) :
    Function.Surjective fun y : Γ(X, W.1) =>
      (I.subschemeObjIso W).inv.hom (Ideal.Quotient.mk (I.ideal W) y) :=
  (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso W).inv).2.comp
    Ideal.Quotient.mk_surjective

theorem forall_finrank_eq_iff_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) [Flat g] [IsFinite g] (n : ℕ) :
    (∀ y : Y, g.finrank y = n) ↔
      ∀ x : PrimeSpectrum Γ(Y, ⊤), g.appTop.hom.finrank x = n := by
  have hfl : g.appTop.hom.Flat := g.flat_appTop
  have hfi : g.appTop.hom.Finite := g.finite_appTop
  haveI : Flat (Spec.map g.appTop) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hfl
  haveI : IsFinite (Spec.map g.appTop) := (IsFinite.SpecMap_iff _).mpr hfi
  have H : IsPullback X.isoSpec.hom g (Spec.map g.appTop) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g⟩
  have key : ∀ y, g.finrank y = g.appTop.hom.finrank (Y.isoSpec.hom y) := fun y => by
    rw [← Scheme.Hom.finrank_SpecMap_eq_finrank hfi hfl,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ H y]
  simp_rw [key]
  exact (Y.isoSpec.hom.homeomorph.surjective.forall
    (p := fun x => g.appTop.hom.finrank x = n)).symm

theorem forall_mem_finrank_eq_iff {Z Y : Scheme.{u}} (q : Z ⟶ Y) [Flat q] [IsFinite q]
    (U : Y.affineOpens) (n : ℕ) :
    (∀ s ∈ U.1, q.finrank s = n) ↔
      ∀ x : PrimeSpectrum Γ(Y, U.1), (q.appLE U.1 (q ⁻¹ᵁ U.1) le_rfl).hom.finrank x = n := by
  haveI : IsAffine (U.1 : Y.Opens) := U.2
  haveI : IsAffine (q ⁻¹ᵁ U.1) := U.2.preimage q
  haveI : Flat (q ∣_ U.1) := IsZariskiLocalAtTarget.restrict ‹Flat q› U.1
  haveI : IsFinite (q ∣_ U.1) := IsZariskiLocalAtTarget.restrict ‹IsFinite q› U.1
  have h1 : (∀ s ∈ U.1, q.finrank s = n) ↔ ∀ y : U.1, (q ∣_ U.1).finrank y = n := by
    rw [Subtype.forall]
    refine forall₂_congr fun s hs => ?_
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict q U.1).flip ⟨s, hs⟩]
    rfl
  exact h1.trans ((forall_finrank_eq_iff_of_isAffine (q ∣_ U.1) n).trans
    (hom_predicate_seam q U.1
      (fun {R S} φ => ∀ x : PrimeSpectrum R, (CommRingCat.Hom.hom φ).finrank x = n)))

theorem mul_le_fst {X : Scheme.{u}} (I J : X.IdealSheafData) : I * J ≤ I :=
  Scheme.IdealSheafData.le_def.mpr fun U => by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]; exact Ideal.mul_le_left

theorem mul_le_snd {X : Scheme.{u}} (I J : X.IdealSheafData) : I * J ≤ J :=
  Scheme.IdealSheafData.le_def.mpr fun U => by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]; exact Ideal.mul_le_right

theorem map_mem_nonZeroDivisors_basicOpen {X : Scheme.{u}} (V : X.affineOpens) (f : Γ(X, V.1))
    {g : Γ(X, V.1)} (hg : g ∈ nonZeroDivisors Γ(X, V.1)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom g ∈
      nonZeroDivisors Γ(X, X.basicOpen f) := by
  haveI := V.2.isLocalization_basicOpen f
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers f) (S := Γ(X, X.basicOpen f)) hg

end generic

section construction

p2m_open "AlgebraicGeometry.Scheme"

variable {C S₀ : Scheme.{u}} {c : C ⟶ S₀}
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]
  {T : Scheme.{u}} {t : T ⟶ S₀}

theorem exists_affineOpen_eq_span_nonZeroDivisor {r : ℕ} (D : RelEffCartierDiv c r t)
    (x : ↥(pullback c t)) :
    ∃ U : (pullback c t).affineOpens, x ∈ U.1 ∧
      ∃ g ∈ nonZeroDivisors Γ(pullback c t, U.1), D.I.ideal U = Ideal.span {g} := by
  obtain ⟨U, u, hxu, g, hg, hU⟩ := AlgebraicGeometry.RelEffCartierDiv.isInvertible_I D x
  exact ⟨(pullback c t).affineBasicOpen u, hxu, g, hg, hU⟩

theorem exists_affineOpen_le_span_nonZeroDivisor {r : ℕ} (D : RelEffCartierDiv c r t)
    {V₀ : TopologicalSpace.Opens ↥(pullback c t)} {x : ↥(pullback c t)} (hx : x ∈ V₀) :
    ∃ W : (pullback c t).affineOpens, x ∈ W.1 ∧ W.1 ≤ V₀ ∧
      ∃ g ∈ nonZeroDivisors Γ(pullback c t, W.1),
        D.I.ideal W = Ideal.span {g} := by
  obtain ⟨V, hxV, g, hgnzd, hg⟩ := exists_affineOpen_eq_span_nonZeroDivisor D x
  obtain ⟨f, hle, hxf⟩ := V.2.exists_basicOpen_le (V := V₀ ⊓ V.1) ⟨x, hx, hxV⟩ hxV
  letI := ((pullback c t).presheaf.map
    (homOfLE <| (pullback c t).basicOpen_le f).op).hom.toAlgebra
  haveI hloc : IsLocalization.Away f Γ(pullback c t, (pullback c t).basicOpen f) :=
    V.2.isLocalization_basicOpen f
  refine ⟨(pullback c t).affineBasicOpen f, hxf, hle.trans inf_le_left,
    algebraMap Γ(pullback c t, V.1) Γ(pullback c t, (pullback c t).basicOpen f) g, ?_, ?_⟩
  ·
    have hreg : IsSMulRegular Γ(pullback c t, V.1) g := fun a b hab => by
      have h0 : (a - b) * g = 0 := by
        rw [sub_mul, sub_eq_zero]
        simpa [smul_eq_mul, mul_comm] using hab
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hgnzd).2 _ h0)
    have hreg' := hreg.of_isLocalization
      Γ(pullback c t, (pullback c t).basicOpen f) (Submonoid.powers f)
    have hcancel : ∀ y,
        y * algebraMap Γ(pullback c t, V.1)
          Γ(pullback c t, (pullback c t).basicOpen f) g = 0 → y = 0 := fun y hy => by
      have h2 : algebraMap Γ(pullback c t, V.1)
            Γ(pullback c t, (pullback c t).basicOpen f) g • y =
          algebraMap Γ(pullback c t, V.1)
            Γ(pullback c t, (pullback c t).basicOpen f) g • (0 : Γ(pullback c t,
              (pullback c t).basicOpen f)) := by
        simpa [smul_eq_mul, mul_comm] using hy
      exact hreg' h2
    exact mem_nonZeroDivisors_iff.mpr
      ⟨fun y hy => hcancel y (by rwa [mul_comm] at hy), hcancel⟩
  ·
    rw [← D.I.map_ideal_basicOpen V f, hg, Ideal.map_span,
      Set.image_singleton]
    rfl

theorem isFinite_mul {r s : ℕ} (D : RelEffCartierDiv c r t) (E : RelEffCartierDiv c s t) :
    IsFinite ((D.I * E.I).subschemeι ≫ pullback.snd c t) := by
  haveI := D.isFinite
  haveI := E.isFinite
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : Smooth (pullback.snd c t) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := pullback.snd c t)
  haveI : LocallyOfFiniteType (pullback.snd c t) := inferInstance
  let pK := (D.I * E.I).subschemeι ≫ pullback.snd c t

  let cov : (D.I.subscheme ⨿ E.I.subscheme) ⟶ (D.I * E.I).subscheme :=
    coprod.desc (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I))
      (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I))
  have hcov : cov ≫ pK =
      coprod.desc (D.I.subschemeι ≫ pullback.snd c t) (E.I.subschemeι ≫ pullback.snd c t) := by
    ext1 <;> simp [cov, pK]
  haveI : IsFinite (cov ≫ pK) := by rw [hcov]; infer_instance
  haveI : Surjective cov := ⟨fun z => by
    have hz : (D.I * E.I).subschemeι z ∈ ((D.I * E.I).support : Set ↥(pullback c t)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, Set.mem_union] at hz
    rcases hz with hD | hE
    · obtain ⟨w, hw⟩ := (Scheme.IdealSheafData.range_subschemeι D.I).ge hD
      refine ⟨(coprod.inl : D.I.subscheme ⟶ D.I.subscheme ⨿ E.I.subscheme) w,
        (D.I * E.I).subschemeι.isClosedEmbedding.injective ?_⟩
      have h1 : coprod.inl ≫ cov = Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) :=
        coprod.inl_desc _ _
      have key : (coprod.inl ≫ cov) ≫ (D.I * E.I).subschemeι = D.I.subschemeι := by
        rw [h1, Scheme.IdealSheafData.inclusion_subschemeι]
      have key' := congrArg (fun φ : D.I.subscheme ⟶ pullback c t => φ w) key
      simp only [Scheme.Hom.comp_apply] at key'
      exact key'.trans hw
    · obtain ⟨w, hw⟩ := (Scheme.IdealSheafData.range_subschemeι E.I).ge hE
      refine ⟨(coprod.inr : E.I.subscheme ⟶ D.I.subscheme ⨿ E.I.subscheme) w,
        (D.I * E.I).subschemeι.isClosedEmbedding.injective ?_⟩
      have h1 : coprod.inr ≫ cov = Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) :=
        coprod.inr_desc _ _
      have key : (coprod.inr ≫ cov) ≫ (D.I * E.I).subschemeι = E.I.subschemeι := by
        rw [h1, Scheme.IdealSheafData.inclusion_subschemeι]
      have key' := congrArg (fun φ : E.I.subscheme ⟶ pullback c t => φ w) key
      simp only [Scheme.Hom.comp_apply] at key'
      exact key'.trans hw⟩
  haveI : UniversallyClosed pK := UniversallyClosed.of_comp_surjective cov pK
  haveI : IsSeparated pK := inferInstance
  haveI : LocallyOfFiniteType pK := inferInstance
  haveI : IsProper pK := {}
  haveI : LocallyQuasiFinite pK := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro x
    refine (((cov ≫ pK).finite_preimage_singleton x).image cov).subset ?_
    intro z hz
    obtain ⟨w, rfl⟩ := cov.surjective z
    refine ⟨w, ?_, rfl⟩
    simpa [Scheme.Hom.comp_apply] using hz
  exact IsFinite.of_isProper_of_locallyQuasiFinite pK

section chartModules

variable {r s : ℕ} (D : RelEffCartierDiv c r t) (E : RelEffCartierDiv c s t) (U : T.affineOpens)

set_option quotPrecheck false in
local notation "Rᵤ" => Γ(T, U.1)
set_option quotPrecheck false in
local notation "Aᵤ" => Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
set_option quotPrecheck false in
local notation "AJᵤ" => Γ(E.I.subscheme,
  (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
    ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
set_option quotPrecheck false in
local notation "AIᵤ" => Γ(D.I.subscheme,
  (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)

noncomputable scoped instance algRA : Algebra Rᵤ Aᵤ :=
  (((D.I * E.I).subschemeι ≫ pullback.snd c t).appLE U.1
    (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra

noncomputable scoped instance algAJ : Algebra Aᵤ AJᵤ :=
  ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
    (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom.toAlgebra

noncomputable scoped instance algRJ : Algebra Rᵤ AJᵤ :=
  ((((D.I * E.I).subschemeι ≫ pullback.snd c t).app U.1) ≫
    (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
      (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom.toAlgebra

scoped instance towerRAJ : IsScalarTower Rᵤ Aᵤ AJᵤ :=
  IsScalarTower.of_algebraMap_eq' (by
    change ((((D.I * E.I).subschemeι ≫ pullback.snd c t).app U.1) ≫
        (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
          (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom =
      ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
          (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom.comp
        (((D.I * E.I).subschemeι ≫ pullback.snd c t).appLE U.1
          (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) le_rfl).hom
    rw [Scheme.Hom.app_eq_appLE]
    rfl)

scoped instance isFinite_subschemeι_comp_snd : IsFinite ((D.I * E.I).subschemeι ≫ pullback.snd c t) := isFinite_mul D E

noncomputable scoped instance algRI : Algebra Rᵤ AIᵤ :=
  ((Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫
    ((D.I * E.I).subschemeι ≫ pullback.snd c t)).app U.1).hom.toAlgebra

theorem finite_A : Module.Finite Rᵤ Aᵤ := by
  haveI : IsAffine (U.1 : T.Opens) := U.2
  haveI : IsAffine (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ (U.1 : T.Opens)) := U.2.preimage _
  exact (hom_predicate_seam ((D.I * E.I).subschemeι ≫ pullback.snd c t) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Finite)).mp
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp
      (IsZariskiLocalAtTarget.restrict (isFinite_mul D E) U.1)).2

theorem inclusion_comp_eq_subschemeι_J :
    Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t) =
      E.I.subschemeι ≫ pullback.snd c t := by
  rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

scoped instance isFinite_inclusion_comp_J :
    IsFinite (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t)) := by
  rw [inclusion_comp_eq_subschemeι_J]
  exact E.isFinite

scoped instance flat_inclusion_comp_J :
    Flat (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t)) := by
  rw [inclusion_comp_eq_subschemeι_J]
  exact E.flat

theorem finite_AJ : Module.Finite Rᵤ AJᵤ := by
  haveI : IsAffine (U.1 : T.Opens) := U.2
  haveI : IsAffine ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  have h := (hom_predicate_seam (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Finite)).mp
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp
      (IsZariskiLocalAtTarget.restrict (isFinite_inclusion_comp_J D E) U.1)).2
  rw [Scheme.Hom.comp_appLE] at h
  exact h

theorem flat_AJ : Module.Flat Rᵤ AJᵤ := by
  haveI : IsAffine (U.1 : T.Opens) := U.2
  haveI : IsAffine ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  have h := (hom_predicate_seam (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Flat)).mp
    ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp
      (IsZariskiLocalAtTarget.restrict (flat_inclusion_comp_J D E) U.1))
  rw [Scheme.Hom.comp_appLE] at h
  exact h

theorem rankAtStalk_AJ (x : PrimeSpectrum Rᵤ) : Module.rankAtStalk (R := Rᵤ) AJᵤ x = s := by
  have h := (forall_mem_finrank_eq_iff (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) U s).mp (fun y _ => by
    rw [inclusion_comp_eq_subschemeι_J]; exact E.finrank_eq y) x
  rw [Scheme.Hom.comp_appLE] at h
  exact h

theorem inclusion_comp_eq_subschemeι_I :
    Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t) =
      D.I.subschemeι ≫ pullback.snd c t := by
  rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

scoped instance isFinite_inclusion_comp_I :
    IsFinite (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t)) := by
  rw [inclusion_comp_eq_subschemeι_I]
  exact D.isFinite

scoped instance flat_inclusion_comp_I :
    Flat (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫ ((D.I * E.I).subschemeι ≫ pullback.snd c t)) := by
  rw [inclusion_comp_eq_subschemeι_I]
  exact D.flat

theorem finite_AI : Module.Finite Rᵤ AIᵤ := by
  haveI : IsAffine (U.1 : T.Opens) := U.2
  haveI : IsAffine ((Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  have h := (hom_predicate_seam (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Finite)).mp
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp
      (IsZariskiLocalAtTarget.restrict (isFinite_inclusion_comp_I D E) U.1)).2
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

theorem flat_AI : Module.Flat Rᵤ AIᵤ := by
  haveI : IsAffine (U.1 : T.Opens) := U.2
  haveI : IsAffine ((Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  have h := (hom_predicate_seam (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Flat)).mp
    ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp
      (IsZariskiLocalAtTarget.restrict (flat_inclusion_comp_I D E) U.1))
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

theorem rankAtStalk_AI (x : PrimeSpectrum Rᵤ) : Module.rankAtStalk (R := Rᵤ) AIᵤ x = r := by
  have h := (forall_mem_finrank_eq_iff (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I) ≫
      ((D.I * E.I).subschemeι ≫ pullback.snd c t)) U r).mp (fun y _ => by
    rw [inclusion_comp_eq_subschemeι_I]; exact D.finrank_eq y) x
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

theorem finitePresentation_AI : Module.FinitePresentation Rᵤ AIᵤ :=
  haveI := finite_AI D E U
  haveI := flat_AI D E U
  Module.finitePresentation_of_rankAtStalk_eq AIᵤ r (rankAtStalk_AI D E U)

theorem projective_AI : Module.Projective Rᵤ AIᵤ :=
  haveI := flat_AI D E U
  haveI := finitePresentation_AI D E U
  Module.Flat.projective_of_finitePresentation

theorem inclusion_app_comp_algebraMap :
    ((Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).app
        (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)).hom.comp (algebraMap Rᵤ Aᵤ) =
      algebraMap Rᵤ AIᵤ := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, Scheme.Hom.comp_app,
    ← Scheme.Hom.app_eq_appLE]
  rfl

noncomputable def πI : Aᵤ →ₐ[Rᵤ] AIᵤ :=
  AlgHom.mk' ((Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).app
      (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)).hom
    (fun cc x => by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def]
      exact congrArg (· * _) (DFunLike.congr_fun (inclusion_app_comp_algebraMap D E U) cc))

theorem πI_surjective : Function.Surjective (πI D E U) :=
  haveI : IsClosedImmersion (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)) :=
    isClosedImmersion_inclusion (mul_le_fst D.I E.I)
  (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).app_surjective _ (U.2.preimage _)

noncomputable def kerπIEquiv : (RingHom.ker (πI D E U).toRingHom) ≃ₗ[Rᵤ]
    ↥(LinearMap.ker (πI D E U).toLinearMap) :=
  { toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem finite_kerπI : Module.Finite Rᵤ (RingHom.ker (πI D E U).toRingHom) :=
  haveI := finite_A D E U
  haveI := projective_AI D E U
  haveI := finite_ker (πI D E U).toLinearMap (πI_surjective D E U)
  Module.Finite.equiv (kerπIEquiv D E U).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in

theorem exists_basicOpen_localizedModule_equiv (z : (D.I * E.I).subscheme)
    (hz : z ∈ ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) :
    ∃ h : Aᵤ, z ∈ (D.I * E.I).subscheme.basicOpen h ∧
      Nonempty (LocalizedModule (Submonoid.powers h) AJᵤ ≃ₗ[Aᵤ]
        LocalizedModule (Submonoid.powers h) (RingHom.ker (πI D E U).toRingHom)) := by
  haveI hCIE : IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)) :=
    isClosedImmersion_inclusion _
  haveI hCI𝔞 : IsClosedImmersion (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)) :=
    isClosedImmersion_inclusion (mul_le_fst D.I E.I)

  have hx : ((D.I * E.I).subschemeι.base z : ↥(pullback c t)) ∈
      (pullback.snd c t) ⁻¹ᵁ (U.1 : T.Opens) := hz
  obtain ⟨W, hxW, hWle, g, hgnzd, hgspan⟩ :=
    exists_affineOpen_le_span_nonZeroDivisor D (V₀ := (pullback.snd c t) ⁻¹ᵁ U.1) hx

  obtain ⟨h, hhle, hzh⟩ := (U.2.preimage ((D.I * E.I).subschemeι ≫ pullback.snd c t) :
      IsAffineOpen _).exists_basicOpen_le
    (V := (D.I * E.I).subschemeι ⁻¹ᵁ W.1) ⟨z, hxW⟩ hz
  have hgood : Nonempty (LocalizedModule (Submonoid.powers h)
      Γ(E.I.subscheme,
        (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
          ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) ≃ₗ[Γ((D.I * E.I).subscheme,
        ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
      LocalizedModule (Submonoid.powers h) (RingHom.ker (πI D E U).toRingHom)) := by

    letI : Algebra
        Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
      ((E.I.subscheme.presheaf.map (homOfLE
        (E.I.subscheme.basicOpen_le _)).op).hom).toAlgebra
    haveI hBloc : IsLocalization.Away
        (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
            (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
              ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)
        Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
      (U.2.preimage (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
        ((D.I * E.I).subschemeι ≫ pullback.snd c t))).isLocalization_basicOpen _

    letI : Algebra Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) :=
      (((D.I * E.I).subscheme.presheaf.map (homOfLE
        ((D.I * E.I).subscheme.basicOpen_le h)).op).hom).toAlgebra
    haveI hAloc : IsLocalization.Away h Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) :=
      (U.2.preimage ((D.I * E.I).subschemeι ≫ pullback.snd c t)).isLocalization_basicOpen h

    letI : Algebra Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
      ((algebraMap Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h))).comp
        (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1))).toAlgebra
    haveI htower2 : IsScalarTower Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI hBloc' : IsLocalization
        (Algebra.algebraMapSubmonoid Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
          (Submonoid.powers h))
        Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) := by
      have heq : Algebra.algebraMapSubmonoid Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
          (Submonoid.powers h) = Submonoid.powers (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h) :=
        Submonoid.map_powers _ _
      exact heq ▸ hBloc
    haveI hBmod : IsLocalizedModule (Submonoid.powers h)
        (IsScalarTower.toAlgHom Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h))).toLinearMap :=
      isLocalizedModule_iff_isLocalization.mpr hBloc'

    have middle : Nonempty (Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) ≃ₗ[Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
        ↥((RingHom.ker (πI D E U).toRingHom).localized'
          Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) (Submonoid.powers h)
          (Algebra.linearMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)))) := by

      have hopen : E.I.subscheme.basicOpen
          (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h) =
          Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ⁻¹ᵁ
            ((D.I * E.I).subscheme.basicOpen h) := by
        rw [Scheme.preimage_basicOpen, RingHom.algebraMap_toAlgebra,
          ← Scheme.Hom.app_eq_appLE]
        rfl
      have hsurjB' : Function.Surjective
          ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
            ((D.I * E.I).subscheme.basicOpen h)
            (E.I.subscheme.basicOpen
              (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
                Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) hopen.le) := by
        have hs := (Scheme.IdealSheafData.inclusion
          (mul_le_snd D.I E.I)).app_surjective ((D.I * E.I).subscheme.basicOpen h)
          ((U.2.preimage ((D.I * E.I).subschemeι ≫ pullback.snd c t)).basicOpen h)
        rw [Scheme.Hom.app_eq_appLE] at hs
        exact ((Scheme.IdealSheafData.inclusion
          (mul_le_snd D.I E.I)).appLE_congr _ rfl hopen.symm
          (fun f => Function.Surjective f)).mp hs

      have hsq : (D.I * E.I).subscheme.presheaf.map (homOfLE
            ((D.I * E.I).subscheme.basicOpen_le h)).op ≫
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
            ((D.I * E.I).subscheme.basicOpen h)
            (E.I.subscheme.basicOpen
              (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
                Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) hopen.le =
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
            (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
              ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) le_rfl ≫
          E.I.subscheme.presheaf.map (homOfLE (by
            rw [hopen]
            exact Scheme.Hom.preimage_mono _ ((D.I * E.I).subscheme.basicOpen_le h))).op := by
        rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

      set πB' : Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) →ₐ[Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
          Γ(E.I.subscheme,
            E.I.subscheme.basicOpen
              (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
                Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
        AlgHom.mk' ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE
            ((D.I * E.I).subscheme.basicOpen h)
            (E.I.subscheme.basicOpen
              (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
                Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) hopen.le).hom
          (fun a x => by
            rw [Algebra.smul_def, map_mul, Algebra.smul_def]
            exact congrArg (· * _)
              (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsq) a))
        with hπB'
      have eQuot := Ideal.quotientKerAlgEquivOfSurjective (f := πB') hsurjB'

      have hWD : (D.I * E.I).subschemeι ⁻¹ᵁ W.1 ≤
          ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1 :=
        Scheme.Hom.preimage_mono _ hWle
      obtain ⟨htil, hhtil⟩ := (D.I * E.I).subschemeι.app_surjective W.1 W.2
        (((D.I * E.I).subscheme.presheaf.map (homOfLE hWD).op).hom h)
      have hDh : (D.I * E.I).subschemeι ⁻¹ᵁ ((pullback c t).basicOpen htil) =
          (D.I * E.I).subscheme.basicOpen h := by
        rw [Scheme.preimage_basicOpen, hhtil, Scheme.basicOpen_res]
        exact inf_eq_right.mpr hhle

      have hkerWt : D.I.ideal ((pullback c t).affineBasicOpen htil) =
          Ideal.span {((pullback c t).presheaf.map (homOfLE
            ((pullback c t).basicOpen_le htil)).op).hom g} := by
        rw [← D.I.map_ideal_basicOpen W htil, hgspan, Ideal.map_span,
          Set.image_singleton]

      let Wt : (pullback c t).affineOpens := (pullback c t).affineBasicOpen htil
      let gt : Γ(pullback c t, Wt.1) :=
        ((pullback c t).presheaf.map (homOfLE ((pullback c t).basicOpen_le htil)).op).hom g
      have hgtnzd : gt ∈ nonZeroDivisors Γ(pullback c t, Wt.1) :=
        map_mem_nonZeroDivisors_basicOpen W htil hgnzd
      let VD : (D.I * E.I).subscheme.affineOpens :=
        ⟨((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1,
          U.2.preimage ((D.I * E.I).subschemeι ≫ pullback.snd c t)⟩

      let resh : Γ((D.I * E.I).subscheme, (D.I * E.I).subschemeι ⁻¹ᵁ Wt.1) ⟶
          Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) :=
        (D.I * E.I).subscheme.presheaf.map (eqToHom hDh.symm).op
      have hreshinj : Function.Injective resh.hom :=
        presheaf_map_injective_of_eq hDh.symm _
      have hreshsurj : Function.Surjective resh.hom :=
        (ConcreteCategory.bijective_of_isIso resh).2
      have hsurjI := subschemeObjIso_inv_mk_surjective (D.I * E.I) Wt
      have hisoIinj : Function.Injective ((D.I * E.I).subschemeObjIso Wt).inv.hom :=
        (ConcreteCategory.bijective_of_isIso ((D.I * E.I).subschemeObjIso Wt).inv).1
      let gq : Γ((D.I * E.I).subscheme, (D.I * E.I).subschemeι ⁻¹ᵁ Wt.1) :=
        ((D.I * E.I).subschemeObjIso Wt).inv.hom (Ideal.Quotient.mk ((D.I * E.I).ideal Wt) gt)
      let ghat : Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) := resh.hom gq

      have h𝔟 : (RingHom.ker (πI D E U).toRingHom).localized'
            Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) (Submonoid.powers h)
            (Algebra.linearMap
              Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)) =
          Ideal.span {ghat} := by
        have hkerC : RingHom.ker (πI D E U).toRingHom =
            (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).ker.ideal VD := by
          rw [Scheme.Hom.ker_apply]
          rfl

        have e1 : (RingHom.ker (πI D E U).toRingHom).localized'
              Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) (Submonoid.powers h)
              (Algebra.linearMap
                Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
                Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)) =
            (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).ker.ideal
              ((D.I * E.I).subscheme.affineBasicOpen (U := VD) h) := by
          rw [Submodule.localized'_eq_span,
            ← (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).ker.map_ideal_basicOpen VD h, hkerC]
          rfl

        have e2 : (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).ker.ideal
            ⟨(D.I * E.I).subschemeι ⁻¹ᵁ Wt.1, Wt.2.preimage (D.I * E.I).subschemeι⟩ = Ideal.span {gq} := by
          rw [Scheme.Hom.ker_apply]
          apply le_antisymm
          · intro x' hx'
            obtain ⟨y, rfl⟩ := hsurjI x'
            have hy := (inclusion_app_mk_eq_zero_iff (mul_le_fst D.I E.I) Wt y).mp hx'
            rw [hkerWt] at hy
            obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
            show ((D.I * E.I).subschemeObjIso Wt).inv.hom (Ideal.Quotient.mk _ (a * gt)) ∈ _
            rw [map_mul, map_mul]
            exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
          · rw [Ideal.span_singleton_le_iff_mem]
            refine (inclusion_app_mk_eq_zero_iff (mul_le_fst D.I E.I) Wt gt).mpr ?_
            rw [hkerWt]
            exact Ideal.mem_span_singleton_self _
        have e3 : (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).ker.ideal
            ((D.I * E.I).subscheme.affineBasicOpen (U := VD) h) = Ideal.span {ghat} := by
          rw [← (Scheme.IdealSheafData.inclusion (mul_le_fst D.I E.I)).ker.map_ideal'
              (U := (D.I * E.I).subscheme.affineBasicOpen (U := VD) h)
              (V := ⟨(D.I * E.I).subschemeι ⁻¹ᵁ Wt.1, Wt.2.preimage (D.I * E.I).subschemeι⟩)
              (eqToHom hDh.symm).op,
            e2, Ideal.map_span, Set.image_singleton]
          rfl
        exact e1.trans e3

      have hreshB : ∀ x' : Γ((D.I * E.I).subscheme, (D.I * E.I).subschemeι ⁻¹ᵁ Wt.1),
          πB' (resh.hom x') = 0 ↔
            ((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).app
              ((D.I * E.I).subschemeι ⁻¹ᵁ Wt.1)).hom x' = 0 := by
        intro x'
        have hcomp := (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).map_appLE
          hopen.le (eqToHom hDh.symm).op
        have HH := hopen.trans (congrArg (fun O => (Scheme.IdealSheafData.inclusion
          (mul_le_snd D.I E.I)) ⁻¹ᵁ O) hDh.symm)
        change ((D.I * E.I).subscheme.presheaf.map (eqToHom hDh.symm).op ≫
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).appLE _ _
            hopen.le).hom x' = 0 ↔ _
        rw [hcomp, Scheme.Hom.appLE]
        change (E.I.subscheme.presheaf.map (homOfLE _).op).hom
          (((Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I)).app _).hom x') = 0 ↔ _
        beta_reduce at HH
        exact map_eq_zero_iff _ (presheaf_map_injective_of_eq HH _)
      have hJiff : ∀ y : Γ(pullback c t, Wt.1),
          y ∈ E.I.ideal Wt ↔ y * gt ∈ (D.I * E.I).ideal Wt := by
        intro y
        rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hkerWt]
        exact (mul_mem_span_singleton_mul_iff hgtnzd (E.I.ideal Wt) y).symm
      have hleWt : (D.I * E.I).ideal Wt ≤ E.I.ideal Wt :=
        Scheme.IdealSheafData.le_def.mp (mul_le_snd D.I E.I) Wt
      have hK : (RingHom.ker πB'.toRingHom : Ideal Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)) =
          LinearMap.ker (LinearMap.toSpanSingleton Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)
            Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) ghat) := by
        ext x
        obtain ⟨x', rfl⟩ := hreshsurj x
        obtain ⟨y, rfl⟩ := hsurjI x'
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul, RingHom.mem_ker]
        change πB' (resh.hom _) = 0 ↔ _
        rw [hreshB, inclusion_app_mk_eq_zero_iff (mul_le_snd D.I E.I) Wt y, hJiff,
          show ghat = resh.hom (((D.I * E.I).subschemeObjIso Wt).inv.hom
            (Ideal.Quotient.mk ((D.I * E.I).ideal Wt) gt)) from rfl,
          ← map_mul, map_eq_zero_iff _ hreshinj, ← map_mul,
          map_eq_zero_iff _ hisoIinj, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

      exact ⟨eQuot.symm.toLinearEquiv ≪≫ₗ
        ((Submodule.quotEquivOfEq _ _ hK ≪≫ₗ
          (LinearMap.toSpanSingleton Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)
            Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) ghat).quotKerEquivRange ≪≫ₗ
          LinearEquiv.ofEq _ _ ((LinearMap.span_singleton_eq_range _ _ ghat).symm.trans
            h𝔟.symm)).restrictScalars
          Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1))⟩
    have eB : LocalizedModule (Submonoid.powers h)
        Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) ≃ₗ[Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
        Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
      IsLocalizedModule.iso (Submonoid.powers h)
        (IsScalarTower.toAlgHom Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
          (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
            ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
          Γ(E.I.subscheme,
          E.I.subscheme.basicOpen
            (algebraMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
              Γ(E.I.subscheme,
                (Scheme.IdealSheafData.inclusion (mul_le_snd D.I E.I) ≫
                  ((D.I * E.I).subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h))).toLinearMap
    have e𝔞 : LocalizedModule (Submonoid.powers h) (RingHom.ker (πI D E U).toRingHom) ≃ₗ[Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
        ↥((RingHom.ker (πI D E U).toRingHom).localized'
          Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) (Submonoid.powers h)
          (Algebra.linearMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h))) :=
      IsLocalizedModule.iso (Submonoid.powers h)
        ((RingHom.ker (πI D E U).toRingHom).toLocalized'
          Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h) (Submonoid.powers h)
          (Algebra.linearMap Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((D.I * E.I).subscheme, (D.I * E.I).subscheme.basicOpen h)))
    exact ⟨eB.trans ((Classical.choice middle).trans e𝔞.symm)⟩
  exact ⟨h, hzh, hgood⟩

theorem span_setOf_localizedModule_equiv_eq_top :
    Ideal.span {h : Aᵤ | Nonempty (LocalizedModule (Submonoid.powers h) AJᵤ ≃ₗ[Aᵤ]
      LocalizedModule (Submonoid.powers h) (RingHom.ker (πI D E U).toRingHom))} =
    ⊤ := by
  refine (U.2.preimage ((D.I * E.I).subschemeι ≫ pullback.snd c t)).self_le_iSup_basicOpen_iff.mp
    (fun z hz => ?_)
  obtain ⟨h, hzh, hgood⟩ := exists_basicOpen_localizedModule_equiv D E U z hz
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨h, hgood⟩, hzh⟩

theorem flat_kerπI : Module.Flat Rᵤ (RingHom.ker (πI D E U).toRingHom) :=
  haveI := flat_AJ D E U
  Module.flat_of_isLocalized_span (S := Aᵤ)
    (spn := span_setOf_localizedModule_equiv_eq_top D E U)
    (Mₛ := fun h => LocalizedModule (Submonoid.powers h.1) AJᵤ)
    (g := fun h => (Classical.choice h.2).symm.toLinearMap ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers h.1) _)
    (H := fun h => flat_localizedModule_of_flat (Submonoid.powers h.1))

theorem rankAtStalk_kerπI (x : PrimeSpectrum Rᵤ) :
    Module.rankAtStalk (R := Rᵤ) (RingHom.ker (πI D E U).toRingHom) x = s := by
  haveI := finite_A D E U
  haveI := finite_AJ D E U
  haveI := flat_AJ D E U
  haveI := flat_kerπI D E U
  haveI := finite_kerπI D E U
  rw [← Module.rankAtStalk_eq_of_forall_localizedModule_equiv (R := Rᵤ) (A := Aᵤ) AJᵤ
    (RingHom.ker (πI D E U).toRingHom) _
    (span_setOf_localizedModule_equiv_eq_top D E U) (fun h hh => hh)]
  exact rankAtStalk_AJ D E U x

theorem finitePresentation_kerπI :
    Module.FinitePresentation Rᵤ (RingHom.ker (πI D E U).toRingHom) :=
  haveI := flat_kerπI D E U
  haveI := finite_kerπI D E U
  Module.finitePresentation_of_rankAtStalk_eq _ s (rankAtStalk_kerπI D E U)

theorem projective_kerπI : Module.Projective Rᵤ (RingHom.ker (πI D E U).toRingHom) :=
  haveI := flat_kerπI D E U
  haveI := finitePresentation_kerπI D E U
  Module.Flat.projective_of_finitePresentation

theorem projective_A : Module.Projective Rᵤ Aᵤ := by
  haveI := projective_AI D E U
  haveI := projective_kerπI D E U
  haveI : Module.Projective Rᵤ ↥(LinearMap.ker (πI D E U).toLinearMap) :=
    Module.Projective.of_equiv (kerπIEquiv D E U)
  exact projective_of_projective_ker (πI D E U).toLinearMap (πI_surjective D E U)

theorem flat_A : Module.Flat Rᵤ Aᵤ :=
  haveI := projective_A D E U
  inferInstance

theorem rankAtStalk_A (x : PrimeSpectrum Rᵤ) : Module.rankAtStalk (R := Rᵤ) Aᵤ x = r + s := by
  haveI := finite_A D E U
  haveI := flat_A D E U
  haveI := projective_AI D E U
  haveI := finite_AI D E U
  have h := congrFun (rankAtStalk_eq_ker_add (πI D E U).toLinearMap (πI_surjective D E U)) x
  rw [Pi.add_apply, ← Module.rankAtStalk_eq_of_equiv (kerπIEquiv D E U), rankAtStalk_kerπI,
    rankAtStalk_AI] at h
  rw [h, add_comm]

theorem finitePresentation_A : Module.FinitePresentation Rᵤ Aᵤ :=
  haveI := finite_A D E U
  haveI := flat_A D E U
  Module.finitePresentation_of_rankAtStalk_eq Aᵤ (r + s) (rankAtStalk_A D E U)

end chartModules

theorem flat_mul {r s : ℕ} (D : RelEffCartierDiv c r t) (E : RelEffCartierDiv c s t) :
    Flat ((D.I * E.I).subschemeι ≫ pullback.snd c t) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat) _ (iSup_affineOpens_eq_top T)]
  intro U
  haveI hU : IsAffine (U.1 : T.Opens) := U.2
  haveI hV : IsAffine (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) := U.2.preimage _
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  refine (hom_predicate_seam _ _ (fun {R S} g => (CommRingCat.Hom.hom g).Flat)).mpr ?_
  exact flat_A D E U

theorem locallyOfFinitePresentation_mul {r s : ℕ} (D : RelEffCartierDiv c r t)
    (E : RelEffCartierDiv c s t) :
    LocallyOfFinitePresentation ((D.I * E.I).subschemeι ≫ pullback.snd c t) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_affineOpens_eq_top T)]
  intro U
  haveI hU : IsAffine (U.1 : T.Opens) := U.2
  haveI hV : IsAffine (((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) := U.2.preimage _
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  refine (hom_predicate_seam _ _
    (fun {R S} g => (CommRingCat.Hom.hom g).FinitePresentation)).mpr ?_
  haveI := finitePresentation_A D E U
  exact (Algebra.FinitePresentation.of_finitePresentation _ _ :
    Algebra.FinitePresentation Γ(T, U.1) Γ((D.I * E.I).subscheme, ((D.I * E.I).subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1))

theorem finrank_mul {r s : ℕ} (D : RelEffCartierDiv c r t) (E : RelEffCartierDiv c s t) (y : T) :
    ((D.I * E.I).subschemeι ≫ pullback.snd c t).finrank y = r + s := by
  haveI : Flat ((D.I * E.I).subschemeι ≫ pullback.snd c t) := flat_mul D E
  obtain ⟨U, hyU⟩ : ∃ U : T.affineOpens, y ∈ U.1 := by
    have hy : y ∈ (⊤ : T.Opens) := trivial
    rw [← iSup_affineOpens_eq_top T] at hy
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  exact (forall_mem_finrank_eq_iff _ U (r + s)).mpr (fun x => rankAtStalk_A D E U x) y hyU

end construction

end DivisorSum
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul.DivisorSum"

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r s : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) (E : RelEffCartierDiv f s g) :
    ∃ F : RelEffCartierDiv f (r + s) g, F.I = D.I * E.I :=
  ⟨{ I := D.I * E.I
     isFinite := DivisorSum.isFinite_mul D E
     flat := DivisorSum.flat_mul D E
     locallyOfFinitePresentation := DivisorSum.locallyOfFinitePresentation_mul D E
     finrank_eq := DivisorSum.finrank_mul D E }, rfl⟩

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul (solution)
