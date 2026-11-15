-- Prove2me | solution 1 for AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_of_one_lt_dimension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-14T20:28:36.351897+00:00
-- url     : https://prove2.me/submissions/2e3f4086-d4c3-4adb-8de2-9c658749ce6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util
import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Theorems.Thm_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_exists_normal_integral_projective_finite_cover
import Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_normal_projective_over_algClosed
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
import Theorems.Thm_AlgebraicGeometry_smooth_of_regular_stalks_over_perfect_field
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem

universe u v

section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveFieldDescent

lemma fieldMap_comp
    (k K : Type u) [Field k] [Field K] [Algebra k K] (E : IntermediateField k K) :
    Spec.map (CommRingCat.ofHom (algebraMap E K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A projective scheme and a morphism to a fixed finite-type ground-field scheme
descend together, retaining the specified projective embedding. -/
theorem exists_projective_relative_finite_model
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of k))
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFiniteType fY]
    (X : Scheme.{u}) (fX : X ⟶ Spec (.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX]
    (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π K n = fX)
    (φ : X ⟶ Y)
    (hφ : φ ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of E))
      (g : X ⟶ X₀) (φ₀ : X₀ ⟶ Y)
      (j₀ : X₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap E K))) ∧
      IsClosedImmersion j₀ ∧ j₀ ≫ ProjSpace.π E n = f₀ ∧
      φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      g ≫ φ₀ = φ := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Pk := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
  let Q := pullback fY (ProjSpace.π k n)
  let fQ : Q ⟶ Spec (.of k) := pullback.fst fY (ProjSpace.π k n) ≫ fY
  let pbK := ProjSpace.isPullback_map k K n
  let u : X ⟶ Pk := j ≫ ProjSpace.map k K n
  have hu : u ≫ ProjSpace.π k n = fX ≫ b := by
    dsimp only [u]
    rw [Category.assoc, pbK.w, ← Category.assoc, hj]
  let α : X ⟶ Q := pullback.lift φ u (hφ.trans hu.symm)
  have hα : α ≫ fQ = fX ≫ b := by
    dsimp only [fQ]
    rw [← Category.assoc, pullback.lift_fst]
    exact hφ
  letI : CompactSpace Q :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst fY (ProjSpace.π k n))
  letI : QuasiSeparatedSpace Q :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst fY (ProjSpace.π k n))
  obtain ⟨E, hE, X₀, f₀, _hqc, _hqs, _hft, g, β, hpb, hβ, hrec⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
      k K Q fQ X fX α hα
  let v : X₀ ⟶ Pk := β ≫ pullback.snd fY (ProjSpace.π k n)
  have hv : v ≫ ProjSpace.π k n =
      f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    dsimp only [v]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hβ
  let pbE := ProjSpace.isPullback_map k E n
  let j₀ := pbE.lift v f₀ hv
  have hj₀ : j₀ ≫ ProjSpace.π E n = f₀ := pbE.lift_snd v f₀ hv
  have hj₀map : j₀ ≫ ProjSpace.map k E n = v := pbE.lift_fst v f₀ hv
  have w : ProjSpace.map k K n ≫ ProjSpace.π k n =
      (ProjSpace.π K n ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    rw [Category.assoc, fieldMap_comp]
    exact pbK.w
  let c : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E) :=
    pbE.lift (ProjSpace.map k K n)
      (ProjSpace.π K n ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) w
  have hcmap : c ≫ ProjSpace.map k E n = ProjSpace.map k K n :=
    pbE.lift_fst _ _ _
  have hcbase : c ≫ ProjSpace.π E n =
      ProjSpace.π K n ≫ Spec.map (CommRingCat.ofHom (algebraMap E K)) :=
    pbE.lift_snd _ _ _
  have hc : IsPullback c (ProjSpace.π K n) (ProjSpace.π E n)
      (Spec.map (CommRingCat.ofHom (algebraMap E K))) := by
    refine IsPullback.of_right ?_ hcbase pbE
    rw [hcmap, fieldMap_comp]
    exact pbK
  have hgj : g ≫ j₀ = j ≫ c := by
    apply pbE.hom_ext
    · rw [Category.assoc, hj₀map, Category.assoc, hcmap]
      change g ≫ (β ≫ pullback.snd fY (ProjSpace.π k n)) = u
      rw [← Category.assoc, hrec, pullback.lift_snd]
    · rw [Category.assoc, hj₀, Category.assoc, hcbase, ← Category.assoc, hj]
      exact hpb.w
  have hpj : IsPullback g j j₀ c := by
    refine IsPullback.of_bot ?_ hgj hc
    rw [hj, hj₀]
    exact hpb
  have hclosed : IsClosedImmersion j₀ :=
    AlgebraicGeometry.isClosedImmersion_of_isPullback_of_faithfullyFlat K
      (ProjSpace.π E n) (ProjSpace.π K n) c hc j₀ j g hpj inferInstance
  let φ₀ : X₀ ⟶ Y := β ≫ pullback.fst fY (ProjSpace.π k n)
  have hover : φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    dsimp only [φ₀]
    rw [Category.assoc]
    exact hβ
  have hφrec : g ≫ φ₀ = φ := by
    dsimp only [φ₀]
    rw [← Category.assoc, hrec, pullback.lift_fst]
  exact ⟨E, hE, X₀, f₀, g, φ₀, j₀, hpb, hclosed, hj₀, hover, hφrec⟩

end PhilipponProjectiveFieldDescent

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFieldModelProperties

lemma fpqc_fieldMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := by
    constructor
    intro x
    exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩
  haveI : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

lemma smooth_of_isPullback_field
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K))
    (g : X' ⟶ X)
    (h : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hs : Smooth f') : Smooth f := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K) hs

lemma proper_of_isPullback_field
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (f' : X' ⟶ Spec (.of K)) (g : X' ⟶ X)
    (h : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hp : IsProper f') : IsProper f := by
  letI := hp
  letI : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact
  haveI : IsSeparated f := MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K)
      (inferInstance : IsSeparated f')
  haveI : UniversallyClosed f := MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K)
      (inferInstance : UniversallyClosed f')
  exact ⟨⟩

end PhilipponFieldModelProperties

end

section

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory

namespace PhilipponFieldModelIntegral

lemma isReduced_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced Y := by
  have hstalk (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj y
    algebraize [(f.stalkMap x).hom]
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    have hf : RingHom.FaithfullyFlat (f.stalkMap x).hom := by
      change Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      infer_instance
    exact isReduced_of_injective (f.stalkMap x).hom hf.injective
  letI := hstalk
  exact isReduced_of_isReduced_stalk Y

lemma isIntegral_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsIntegral X] : IsIntegral Y := by
  letI : AlgebraicGeometry.IsReduced Y := isReduced_of_flat_surjective f
  letI : IrreducibleSpace Y := (inferInstance : Surjective f).surj.irreducibleSpace f.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

lemma geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f := by
  constructor
  intro K _ y Z fst snd hpb
  letI : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral (f := f) y fst snd hpb
  infer_instance

end PhilipponFieldModelIntegral

end

section

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponIntegralDimension

lemma ring_dimension_le_of_integral {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h

lemma dimension_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [show topologicalKrullDim X = Order.krullDim X from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  simp_rw [Order.krullDim_eq_iSup_coheight, ringKrullDim_stalk_eq_coheight]

lemma stalk_dimension_le {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [dimension_eq_iSup_stalk]
  exact le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) x

lemma affine_dimension_eq (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq X.isoSpec.hom X.isoSpec.hom.homeomorph.isHomeomorph

/-- An integral morphism cannot increase Krull dimension, without a finite-type hypothesis. -/
theorem dimension_le_of_integral {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [dimension_eq_iSup_stalk]
  refine iSup_le fun x => ?_
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  let W := f ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage f
  letI : IsAffine (W : Scheme) := hW
  letI : IsAffine (V : Scheme) := hV
  let z : W := ⟨x, hx⟩
  have he : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim ((W : Scheme).presheaf.stalk z) :=
    ringKrullDim_eq_of_ringEquiv
      (asIso (W.ι.stalkMap z)).commRingCatIsoToRingEquiv
  have hsec : ringKrullDim Γ(X, W) ≤ ringKrullDim Γ(Y, V) :=
    ring_dimension_le_of_integral (f.app V).hom (f.isIntegral_app V hV)
  have hdimW : topologicalKrullDim (W : Scheme) = ringKrullDim Γ(X, W) := by
    rw [affine_dimension_eq]
    exact ringKrullDim_eq_of_ringEquiv W.topIso.commRingCatIsoToRingEquiv
  have hdimV : topologicalKrullDim (V : Scheme) = ringKrullDim Γ(Y, V) := by
    rw [affine_dimension_eq]
    exact ringKrullDim_eq_of_ringEquiv V.topIso.commRingCatIsoToRingEquiv
  calc
    ringKrullDim (X.presheaf.stalk x) =
        ringKrullDim ((W : Scheme).presheaf.stalk z) := he
    _ ≤ topologicalKrullDim (W : Scheme) := stalk_dimension_le (X := (W : Scheme)) z
    _ = ringKrullDim Γ(X, W) := hdimW
    _ ≤ ringKrullDim Γ(Y, V) := hsec
    _ = topologicalKrullDim (V : Scheme) := hdimV.symm
    _ ≤ topologicalKrullDim Y := topologicalKrullDim_subspace_le Y (V : Set Y)

/-- Base change by an arbitrary algebraic field extension does not increase dimension. -/
theorem dimension_le_algebraic_baseChange
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) :
    topologicalKrullDim (pullback π (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) ≤
      topologicalKrullDim X := by
  haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact dimension_le_of_integral (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap K L))))

lemma dimension_le_of_openCover {X : Scheme.{u}} (U : X.OpenCover) (d : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (U.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  rw [dimension_eq_iSup_stalk]
  refine iSup_le fun x => ?_
  obtain ⟨i, y, rfl⟩ := U.exists_eq x
  have he : ringKrullDim (X.presheaf.stalk (U.f i y)) =
      ringKrullDim ((U.X i).presheaf.stalk y) :=
    ringKrullDim_eq_of_ringEquiv (asIso ((U.f i).stalkMap y)).commRingCatIsoToRingEquiv
  exact (he.trans_le (stalk_dimension_le (X := U.X i) y)).trans (h i)

end PhilipponIntegralDimension

end

section

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponFaithfullyFlatDimension

lemma ring_dimension_le_of_faithfullyFlat
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : ringKrullDim R ≤ ringKrullDim S := by
  classical
  simp only [ringKrullDim, Order.krullDim]
  refine iSup_le fun l => ?_
  obtain ⟨P, hP, hlo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat
    (B := S) l.last.asIdeal
  letI := hP
  letI := hlo
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  rw [← hL]
  exact le_iSup (fun l : LTSeries (PrimeSpectrum S) => (l.length : WithBot ℕ∞)) L

/-- A flat surjection cannot lower the dimension of its target. -/
lemma dimension_le_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [PhilipponIntegralDimension.dimension_eq_iSup_stalk Y]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj y
  algebraize [(f.stalkMap x).hom]
  haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact (ring_dimension_le_of_faithfullyFlat _ _).trans
    (PhilipponIntegralDimension.stalk_dimension_le (X := X) x)

end PhilipponFaithfullyFlatDimension

end

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponGenericDominance

lemma genericPoint_eq_of_dominant
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] : q (genericPoint X) = genericPoint S := by
  have h := (genericPoint_spec X).image q.continuous
  have hg : IsGenericPoint (q (genericPoint X)) (Set.univ : Set S) := by
    simpa only [Set.image_univ, q.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec S)

lemma genericFiber_inclusion
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] (η : S) (hη : IsGenericPoint η Set.univ) :
    IsDominant (q.fiberι η) := by
  have hηeq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (q.fiberι (genericPoint S)) := by
    refine ⟨(q.fiberHomeo (genericPoint S)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant q⟩, ?_⟩
    exact q.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (q.fiberι (genericPoint S)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma of_recovered_generic_cover
    {C F Y X : Scheme.{u}} (e : C ⟶ Y) (f : Y ⟶ X) (a : C ⟶ F) (i : F ⟶ X)
    [Surjective a] [IsDominant i] (h : e ≫ f = a ≫ i) : IsDominant f := by
  haveI : IsDominant (e ≫ f) := by rw [h]; infer_instance
  exact IsDominant.of_comp e f

end PhilipponGenericDominance
end
end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponGenericDimensionFormula

abbrev residueAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma preimage_residue_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  apply ext_of_isAffine
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  have ht : (Spec.map (Scheme.ΓSpecIso (.of K)).inv).appTop =
      (Scheme.ΓSpecIso Γ(Spec (.of K), ⊤)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
    exact (Scheme.ΓSpecIso_inv_naturality (Scheme.ΓSpecIso (.of K)).inv).symm
  simp
  simp only [Scheme.Hom.appTop] at ht ⊢
  rw [ht]

lemma residue_tower {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X) :
    letI := residueAlgebra g (f x)
    letI := residueAlgebra (f ≫ g) x
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  letI := residueAlgebra g (f x)
  letI := residueAlgebra (f ≫ g) x
  letI := (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := congrArg Spec.preimage
    (congrArg (fun a => a ≫ g)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map,
    preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h


end PhilipponGenericDimensionFormula


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section

namespace PhilipponGenericDimensionFormula

lemma isDominant_genericFiberι
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsDominant (f.fiberι (genericPoint Y)) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)) := by
    refine ⟨(f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, PhilipponGenericDominance.genericPoint_eq_of_dominant f⟩, ?_⟩
    exact f.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (f.fiberι (genericPoint Y)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma residue_base_tower {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of F)) (x : X) :
    letI := residueAlgebra s x
    letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
    IsScalarTower K F (X.residueField x) := by
  letI := residueAlgebra s x
  letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := Spec.preimage_comp (X.fromSpecResidueField x ≫ s)
    (Spec.map (CommRingCat.ofHom (algebraMap K F)))
  rw [Spec.preimage_map] at h
  simp only [Category.assoc, preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h

lemma dimension_eq_trdeg_of_genericPoint {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (x : X) (hx : x = genericPoint X) :
    letI := residueAlgebra c x
    topologicalKrullDim X = (Cardinal.toENat (Algebra.trdeg K (X.residueField x)) : WithBot ℕ∞) := by
  letI := residueAlgebra c x
  have h := toENat_trdeg_residueField_eq_topologicalKrullDim_closure c x
  have hcl : closure ({x} : Set X) = Set.univ := by rw [hx]; exact genericPoint_spec X
  have hd : topologicalKrullDim X = topologicalKrullDim (closure ({x} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  exact hd.trans h.symm

/-- Dimensions add along the actual generic fibre, with the structure-field maps retained. -/
theorem dimension_eq_add_genericFiber
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : Y ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    topologicalKrullDim X = topologicalKrullDim Y +
      topologicalKrullDim (f.fiber (genericPoint Y)) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ c)
  let η := genericPoint Y
  let F := Y.residueField η
  let C := f.fiber η
  let s : C ⟶ Spec F := f.fiberToSpecResidueField η
  let t : C ⟶ X := f.fiberι η
  letI : IsIntegral C := AlgebraicGeometry.isIntegral_genericFiber_of_isDominant f
  letI : IsDominant t := isDominant_genericFiberι f
  let u := genericPoint C
  let z := t u
  let E := C.residueField u
  let L := X.residueField z
  letI : Algebra K F := residueAlgebra c η
  letI : Algebra F E := residueAlgebra s u
  letI : Algebra K E := residueAlgebra (t ≫ (f ≫ c)) u
  letI : Algebra K L := residueAlgebra (f ≫ c) z
  letI : Algebra L E := (t.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower t (f ≫ c) u
  have hbase : t ≫ (f ≫ c) = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    change f.fiberι η ≫ (f ≫ c) =
      f.fiberToSpecResidueField η ≫ Spec.map
        ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop ≫
          Y.presheaf.germ ⊤ η trivial ≫ Y.residue η)
    rw [← preimage_residue_comp, Spec.map_preimage, ← Category.assoc, f.fiber_fac]
    exact Category.assoc _ _ _
  letI : IsScalarTower K F E := by
    apply IsScalarTower.of_algebraMap_eq'
    have hmap : (algebraMap F E).comp (algebraMap K F) =
        (residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u).algebraMap := by
      letI : Algebra K E := residueAlgebra
        (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u
      letI : IsScalarTower K F E := residue_base_tower (K := K) (F := F) s u
      exact (IsScalarTower.algebraMap_eq K F E).symm
    exact (hmap.trans (congrArg (fun a => (residueAlgebra a u).algebraMap) hbase.symm)).symm
  letI : IsIso (t.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion t u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (t.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  letI : LocallyOfFiniteType s := MorphismProperty.pullback_snd f
    (Y.fromSpecResidueField η) (inferInstance : LocallyOfFiniteType f)
  have hX := dimension_eq_trdeg_of_genericPoint (f ≫ c) z (PhilipponGenericDominance.genericPoint_eq_of_dominant t)
  have hY := dimension_eq_trdeg_of_genericPoint c η rfl
  have hC := dimension_eq_trdeg_of_genericPoint (K := F) s u rfl
  rw [hX, hY, hC]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K F) : WithBot ℕ∞) +
      (Cardinal.toENat (Algebra.trdeg F E) : WithBot ℕ∞)
  rw [he, ← trdeg_add_eq K F (A := E)]
  simp only [map_add, WithBot.coe_add]

end PhilipponGenericDimensionFormula

end
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationDimensionControl

lemma finite_of_dimension_le_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hd : topologicalKrullDim X ≤ 0) : IsFinite π := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hd
  letI : Subsingleton X := Set.subsingleton_univ_iff.mp
    ((isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology X)).subsingleton_of_isPreirreducible
      PreirreducibleSpace.isPreirreducible_univ)
  exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := π)).mpr inferInstance

lemma dimension_nonneg (X : Scheme.{u}) [IsIntegral X] :
    0 ≤ topologicalKrullDim X := by
  change 0 ≤ Order.krullDim (IrreducibleCloseds X)
  letI : Nonempty (IrreducibleCloseds X) := ⟨{
    carrier := Set.univ
    isIrreducible' := IrreducibleSpace.isIrreducible_univ X
    isClosed' := isClosed_univ }⟩
  exact Order.krullDim_nonneg

lemma eq_one_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : ((r + 1 : ℕ) : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 1 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 1 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [Nat.cast_add, Nat.cast_one,
        WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_one] using h)
    have hd : d = 1 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

lemma eq_zero_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : (r : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 0 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 0 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [add_zero,
        WithBot.coe_add, WithBot.coe_natCast] using h)
    have hd : d = 0 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

/-- The controlled generic curve forces the covering model to preserve
dimension. Its map to the original variety has zero-dimensional generic fibre. -/
theorem dimension_eq_and_genericFiber_dimensions
    (K : Type u) [Field K] {G X N : Scheme.{u}}
    [IsIntegral G] [IsIntegral X] [IsIntegral N]
    (πX : X ⟶ Spec (.of K)) [LocallyOfFiniteType πX]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (a : G ⟶ X) [LocallyOfFiniteType a] [IsDominant a]
    (f : G ⟶ N) [LocallyOfFiniteType f] [IsDominant f]
    (r : ℕ) (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞))
    (hdN : topologicalKrullDim N = (r : WithBot ℕ∞))
    (hdF : topologicalKrullDim (f.fiber (genericPoint N)) ≤ 1) :
    topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim (f.fiber (genericPoint N)) = 1 ∧
      topologicalKrullDim (a.fiber (genericPoint X)) = 0 := by
  have ha := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πX a
  have hf := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πN f
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (a ≫ πX)
  haveI : IsIntegral (a.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant a
  have hza := dimension_nonneg (a.fiber (genericPoint X))
  have hlow : topologicalKrullDim X ≤ topologicalKrullDim G := by
    calc
      topologicalKrullDim X = topologicalKrullDim X + 0 := (add_zero _).symm
      _ ≤ topologicalKrullDim X + topologicalKrullDim (a.fiber (genericPoint X)) :=
        add_le_add (le_refl _) hza
      _ = topologicalKrullDim G := ha.symm
  have hhigh : topologicalKrullDim G ≤ topologicalKrullDim X := by
    calc
      topologicalKrullDim G = (r : WithBot ℕ∞) +
          topologicalKrullDim (f.fiber (genericPoint N)) := hf.trans (by rw [hdN])
      _ ≤ (r : WithBot ℕ∞) + 1 := add_le_add (le_refl _) hdF
      _ = topologicalKrullDim X := by rw [hdX]; simp
  have heq := le_antisymm hhigh hlow
  refine ⟨heq, eq_one_of_nat_add_eq r _ ?_, eq_zero_of_nat_add_eq (r + 1) _ ?_⟩
  · simpa only [heq, hdX, hdN] using hf
  · simpa only [heq, hdX] using ha

end PhilipponAlterationDimensionControl

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponProperGenericFiniteness

/-- The finite open in the alteration definition gives a finite generic
fiber. The argument retains the actual restriction map and point. -/
theorem finite_genericFiber_of_finite_open
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsProper p]
    (U : X.Opens) [Nonempty U] [IsFinite (p ∣_ U)] :
    IsFinite (p.fiberToSpecResidueField (genericPoint X)) := by
  let η := genericPoint X
  have hηU : η ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hfin := (p ∣_ U).finite_preimage_singleton ηU
  have hpre : (p ⁻¹' {η}).Finite := by
    apply (hfin.image (p ⁻¹ᵁ U).ι).subset
    intro y hy
    change p y = η at hy
    let yU : (p ⁻¹ᵁ U).toScheme := ⟨y, by change p y ∈ U; rw [hy]; exact hηU⟩
    refine ⟨yU, ?_, rfl⟩
    change (p ∣_ U) yU = ηU
    apply Subtype.ext
    exact (morphismRestrict_base_coe p U yU).trans hy
  haveI : Finite (p.fiber η) := (p.fiberHomeo η).finite_iff.mpr hpre
  haveI : IsProper (p.fiberToSpecResidueField η) :=
    MorphismProperty.pullback_snd p (X.fromSpecResidueField η) inferInstance
  haveI : LocallyQuasiFinite (p.fiberToSpecResidueField η) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (p.fiberToSpecResidueField η)
      (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- A proper morphism with finite generic fiber is finite on a nonempty
open of its integral target, in the exact form required by alterations. -/
theorem exists_finite_open_of_finite_genericFiber
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsProper p]
    [IsFinite (p.fiberToSpecResidueField (genericPoint X))] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite (p ∣_ W) := by
  let η := genericPoint X
  have hF : (Set.univ : Set (p.fiber η)).Finite := by
    simpa only [Set.preimage_univ] using
      (p.fiberToSpecResidueField η).finite_preimage
        (Set.finite_univ : (Set.univ : Set (Spec (X.residueField η))).Finite)
  have hpη : (p ⁻¹' {η}).Finite := by
    rw [← p.range_fiberι η]
    simpa only [Set.image_univ] using hF.image (p.fiberι η)
  obtain ⟨W, hηW, hfinite⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton p η hpη
  exact ⟨W, ⟨⟨η, hηW⟩⟩, hfinite⟩

/-- A proper dominant finite-type map between integral varieties whose
source has no larger dimension is finite over a nonempty target open.
The target dimension is explicitly finite; equality of infinite
dimensions is not used to cancel a generic-fiber dimension. -/
theorem exists_finite_open_of_dimension_le
    (K : Type u) [Field K] {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (p : Y ⟶ X) [IsProper p] [IsDominant p]
    (d : ℕ) (hdX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hle : topologicalKrullDim Y ≤ topologicalKrullDim X) :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite (p ∣_ W) := by
  have hdim := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K π p
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ π)
  letI : IsIntegral (p.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant p
  have hnonneg := PhilipponAlterationDimensionControl.dimension_nonneg
    (p.fiber (genericPoint X))
  have hge : topologicalKrullDim X ≤ topologicalKrullDim Y := by
    rw [hdim]
    simpa only [add_zero] using add_le_add (le_refl (topologicalKrullDim X)) hnonneg
  have heq : topologicalKrullDim Y = topologicalKrullDim X := le_antisymm hle hge
  have hzero : topologicalKrullDim (p.fiber (genericPoint X)) = 0 :=
    PhilipponAlterationDimensionControl.eq_zero_of_nat_add_eq d _ (by
      simpa only [heq, hdX] using hdim)
  haveI : LocallyOfFiniteType (p.fiberToSpecResidueField (genericPoint X)) :=
    MorphismProperty.pullback_snd p (X.fromSpecResidueField (genericPoint X)) inferInstance
  haveI : IsFinite (p.fiberToSpecResidueField (genericPoint X)) :=
    PhilipponAlterationDimensionControl.finite_of_dimension_le_zero
      (X.residueField (genericPoint X)) _ hzero.le
  exact exists_finite_open_of_finite_genericFiber p

/-- A proper generically finite map of integral varieties cannot
increase dimension. This supplies the dimension bound required by
algebraic-field descent of the regular projective alteration. -/
theorem dimension_le_of_finite_open
    (K : Type u) [Field K] {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (p : Y ⟶ X) [IsProper p] [IsDominant p]
    (U : X.Opens) [Nonempty U] [IsFinite (p ∣_ U)] :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  haveI : IsFinite (p.fiberToSpecResidueField (genericPoint X)) :=
    finite_genericFiber_of_finite_open p U
  haveI : IsLocallyArtinian (p.fiber (genericPoint X)) :=
    IsLocallyArtinian.of_locallyQuasiFinite (p.fiberToSpecResidueField (genericPoint X))
  have hzero := topologicalKrullDim_zero_of_discreteTopology (p.fiber (genericPoint X))
  calc
    topologicalKrullDim Y = topologicalKrullDim X +
        topologicalKrullDim (p.fiber (genericPoint X)) :=
      PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K π p
    _ ≤ topologicalKrullDim X + 0 := add_le_add (le_refl _) hzero
    _ = topologicalKrullDim X := add_zero _

end PhilipponProperGenericFiniteness

end
end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open IsLocalRing Localization

namespace ChildB

private theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.EssFiniteType R S] :
    IsNoetherianRing S := by
  haveI hN : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S hN

end ChildB

theorem etaleRegularAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hreg
  haveI hlo : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)) q

  haveI : Algebra.FormallyUnramified A B := inferInstance
  haveI hIU : Algebra.IsUnramifiedAt A q := by
    unfold Algebra.IsUnramifiedAt
    infer_instance
  haveI hEFTa : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
  haveI hEFT : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := Algebra.EssFiniteType.of_comp A _ _
  haveI hNoeth : IsNoetherianRing (Localization.AtPrime q) :=
    ChildB.isNoetherianRing_of_essFiniteType (Localization.AtPrime (q.comap (algebraMap A B))) _

  have hmap : (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).map
      (algebraMap _ (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal

  have h1 : (maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).spanFinrank := by
    rw [← hmap]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  haveI : Module.Flat A B := inferInstance
  haveI hflat : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := inferInstance

  haveI hlom2 : (maximalIdeal (Localization.AtPrime q)).LiesOver
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))) := by
    constructor
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_iff_not.mpr
      ⟨fun h => IsLocalHom.map_nonunit x h, fun h => h.map (algebraMap _ _)⟩ |>.symm

  have h2 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := Localization.AtPrime (q.comap (algebraMap A B))) (S := Localization.AtPrime q)
    (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B))))
    (maximalIdeal (Localization.AtPrime q))

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h1
    _ = ringKrullDim (Localization.AtPrime (q.comap (algebraMap A B))) :=
        hreg.spanFinrank_maximalIdeal
    _ = ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ((maximalIdeal (Localization.AtPrime q)).height : WithBot ℕ∞) := by
        rw [h2]
        exact_mod_cast le_self_add
    _ = ringKrullDim (Localization.AtPrime q) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end

end S_isRegularLocalRing_localization_atPrime_of_etale_of_comap
end P2MW
export P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap (etaleRegularAt)

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

/-- Standard smooth presentations are étale over a polynomial algebra, whose
prime localizations are regular. -/
theorem regularAt_of_standardSmooth (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.IsStandardSmooth K R] (q : Ideal R) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨n, f, hf, he⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap K R) (RingHom.isStandardSmooth_algebraMap.mpr inferInstance)
  algebraize [f]
  haveI : IsRegularRing K := inferInstance
  haveI : IsRegularRing (MvPolynomial (Fin n) K) :=
    MvPolynomial.isRegularRing_of_isRegularRing K
  exact P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.etaleRegularAt
    (MvPolynomial (Fin n) K) R q
    (IsRegularRing.isRegularLocalRing_localization _)

/-- Smoothness at a prime suffices: choose a standard smooth neighbourhood
and identify its localization with the original local ring. -/
theorem regularAt_of_smoothAt (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.FinitePresentation K R] (p : Ideal R) [hp : p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  letI := hstd
  have hdis : Disjoint (Submonoid.powers f : Set R) (p : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q := p.map (algebraMap R (Localization.Away f))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) p hp hdis
  have heq : q.comap (algebraMap R (Localization.Away f)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) hp hdis
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    regularAt_of_standardSmooth K (Localization.Away f) q
  haveI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    have heq' : (q.comap (algebraMap R (Localization.Away f))).primeCompl = p.primeCompl := by
      ext x
      change x ∉ q.comap (algebraMap R (Localization.Away f)) ↔ x ∉ p
      rw [heq]
    rw [← heq']
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).symm.toRingEquiv)

end PhilipponMultiplicity.AlgebraicGroupCM

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- Smooth schemes over any field have regular local rings. This uses
the previously checked standard-smooth/etale local calculation and
does not assume perfectness of the ground field. -/
theorem PhilipponSmoothSchemeRegular.stalk
    (K : Type u) [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [Smooth π] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let R := Γ(X, U)
  let φ : K →+* R :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom
  letI : Algebra K R := φ.toAlgebra
  have hφ : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv))
    (π.smooth_appLE (isAffineOpen_top _) hU (by simp))
  letI : Algebra.Smooth K R := hφ
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  haveI : p.IsPrime := inferInstance
  letI : IsRegularLocalRing (Localization.AtPrime p) :=
    PhilipponMultiplicity.AlgebraicGroupCM.regularAt_of_smoothAt K R p
  letI : Algebra R (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv

end
end

section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace PhilipponFiniteCocycle
variable {X : Scheme.{u}} {r : ℕ}

/-- A finite chart cocycle, without equating the index and scheme universes. -/
structure UnitCocycle (V : Fin r → X.Opens) where
  u : ∀ i j, Γ(X, V i ⊓ V j)
  refl : ∀ i, u i i = 1
  cocycle : ∀ i j k,
    rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V j) (u i j) *
    rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V j ⊓ V k) (u j k) =
    rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V k) (u i k)

variable {V : Fin r → X.Opens}

def UnitCocycle.lift (c : UnitCocycle V) :
    Scheme.Modules.UnitCocycle (fun i : ULift.{u} (Fin r) => V i.down) where
  u i j := c.u i.down j.down
  refl i := c.refl i.down
  cocycle i j k := c.cocycle i.down j.down k.down

noncomputable abbrev glueOfCocycle (c : UnitCocycle V) : X.Modules :=
  Scheme.Modules.glueOfCocycle c.lift

noncomputable abbrev glueComponent (c : UnitCocycle V) (T : X.Opens) (i : Fin r) :=
  Scheme.Modules.glueComponent c.lift T (ULift.up i)

lemma leij (T : X.Opens) (i j : Fin r) : T ⊓ (V i ⊓ V j) ≤ V i ⊓ V j := inf_le_right

noncomputable abbrev glueMk (c : UnitCocycle V) (T : X.Opens)
    (x : ∀ i, Γ(X, T ⊓ V i))
    (hx : ∀ i j,
      rO (inf_le_inf_left T inf_le_left : T ⊓ (V i ⊓ V j) ≤ T ⊓ V i) (x i) =
      rO (leij T i j) (c.u i j) *
      rO (inf_le_inf_left T inf_le_right : T ⊓ (V i ⊓ V j) ≤ T ⊓ V j) (x j)) :
    Γ(glueOfCocycle c, T) :=
  Scheme.Modules.glueMk c.lift T (fun i => x i.down) (fun i j => hx i.down j.down)

noncomputable abbrev glueFrame (c : UnitCocycle V) (i : Fin r) :=
  Scheme.Modules.glueFrame c.lift (ULift.up i)

lemma glue_ext (c : UnitCocycle V) {T : X.Opens} {p q : Γ(glueOfCocycle c, T)}
    (h : ∀ i, glueComponent c T i p = glueComponent c T i q) : p = q :=
  Scheme.Modules.glue_ext c.lift (fun i => h i.down)

lemma glueComponent_map (c : UnitCocycle V) {T T' : X.Opens} (h : T' ≤ T)
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T' i ((glueOfCocycle c).presheaf.map (homOfLE h).op p) =
      rO (inf_le_inf_right (V i) h) (glueComponent c T i p) := rfl

lemma glueComponent_smul (c : UnitCocycle V) {T : X.Opens} (g : Γ(X, T))
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i (g • p) = rO inf_le_left g * glueComponent c T i p := rfl

lemma glueComponent_glueFrame (c : UnitCocycle V) (i k : Fin r) :
    glueComponent c (V i) k (glueFrame c i) =
      rO (le_of_eq (inf_comm (V i) (V k))) (c.u k i) := rfl

lemma isFrameOn_glueFrame (c : UnitCocycle V) (i : Fin r) :
    Scheme.Modules.IsFrameOn (glueFrame c i) (V i) :=
  Scheme.Modules.isFrameOn_glueFrame c.lift (ULift.up i)

end PhilipponFiniteCocycle
end

section

-- Generalizes the accepted FLT chart constructions to arbitrary universes.
-- Original accepted sources and their hashes are archived in the work directory.
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj

set_option autoImplicit false


open CategoryTheory

namespace AlgebraicGeometry

namespace A1ChartFin

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem Proj.exists_basicOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ Proj.basicOpen 𝒜 f ≤ U ∧ ∀ x ∈ S, x ∈ Proj.basicOpen 𝒜 f := by
  classical
  set Z : Set (Proj 𝒜) := (U : Set (Proj 𝒜))ᶜ with hZdef
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  set J : HomogeneousIdeal 𝒜 := ProjectiveSpectrum.vanishingIdeal Z with hJdef
  have hZJ : ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) = Z := by
    rw [hJdef, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hZ.closure_eq
  have havoid : ∀ p ∈ S.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal),
      ¬ (J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ p) := by
    intro p hp hle
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    change (J ⊓ HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal at hle
    rw [HomogeneousIdeal.toIdeal_inf, x.isPrime.inf_le] at hle
    rcases hle with hle | hle
    · have hxZ : x ∈ Z := by
        rw [← hZJ]
        exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x _).mpr hle
      exact hxZ (hS x hxS)
    · exact x.not_irrelevant_le hle
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ :=
    (J ⊓ HomogeneousIdeal.irrelevant 𝒜).exists_homogeneous_pos_mem_forall_notMem inf_le_right
      (S.image fun x : Proj 𝒜 => x.asHomogeneousIdeal)
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
        exact x.isPrime)
      havoid
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := hyU
    rw [← hZJ] at hyZ
    have hfJ : f ∈ J := (inf_le_left : J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ J) hfI
    exact (Proj.mem_basicOpen 𝒜 f y).mp hy ((ProjectiveSpectrum.mem_zeroLocus 𝒜 y _).mp hyZ hfJ)
  · intro x hx
    rw [Proj.mem_basicOpen]
    exact hf _ (Finset.mem_image_of_mem _ hx)

end A1ChartFin

theorem A1ChartFin.isAffineOpen_ι_preimage_of_le {Y : Scheme.{u}} {U V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ U) :
    IsAffineOpen (U.ι ⁻¹ᵁ V) := by
  have himg : IsAffineOpen (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
    exact hV
  haveI : IsAffine (U.ι ''ᵁ U.ι ⁻¹ᵁ V) := himg
  exact IsAffine.of_isIso (U.ι.isoImage (U.ι ⁻¹ᵁ V)).hom

theorem A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsImmersion ι]
    (W : Y.Opens) (hW : W ≤ ι.coborderRange) : IsClosedImmersion (ι ∣_ W) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hsub : (Subtype.val : ↥W → ↥Y) ⁻¹' coborder (Set.range ι) = Set.univ :=
    Set.eq_univ_of_forall fun w => hW w.2
  have hcl : (Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι =
      (Subtype.val : ↥W → ↥Y) ⁻¹' closure (Set.range ι) := by
    conv_lhs => rw [← coborder_inter_closure (s := Set.range ι)]
    rw [Set.preimage_inter, hsub, Set.univ_inter]
  have key : IsClosed ((Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι) := by
    rw [hcl]; exact isClosed_closure.preimage continuous_subtype_val
  rw [morphismRestrict_base]
  erw [Set.range_restrictPreimage]
  exact key

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry in
theorem solution
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsImmersion ι] (S : Finset X) :
    ∃ (d : ℕ) (F : A) (_ : F ∈ 𝒜 d), 0 < d ∧ (∀ x ∈ S, x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧
      IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧ IsClosedImmersion (ι ∣_ Proj.basicOpen 𝒜 F) := by
  classical
  set U := ι.coborderRange with hU
  set g := ι.liftCoborder with hgdef
  have hg : g ≫ U.ι = ι := ι.liftCoborder_ι
  obtain ⟨n, F, hn, hFn, hle, hmem⟩ := A1ChartFin.Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 U (S.image ι.base) (by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hg]
    exact (g.base x).2)
  refine ⟨n, F, hFn, hn, ?_, ?_, ?_⟩
  · intro x hx
    exact hmem _ (Finset.mem_image_of_mem _ hx)
  · have H : IsAffineOpen ((g ≫ U.ι) ⁻¹ᵁ Proj.basicOpen 𝒜 F) :=
      (A1ChartFin.isAffineOpen_ι_preimage_of_le (Proj.isAffineOpen_basicOpen 𝒜 F hFn hn) hle).preimage g
    rwa [hg] at H
  · exact A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange ι _ hle

end S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
end P2MW


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization

theorem solution
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {d : ℕ} (hd : 0 < d) {r : ℕ} (F : Fin r → A) (hF : ∀ i : Fin r, F i ∈ 𝒜 d) :
    ∃ w : ∀ i j : Fin r, Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F i)),
      (∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i))) ∧
      (∀ i : Fin r, w i i = 1) ∧
      (∀ i j k : Fin r,
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i k) =
          (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i j) *
            (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F j))).op (w j k)) ∧
      (∀ i j : Fin r, (Proj 𝒜).basicOpen (w i j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j)) := by
  classical

  have res_res : ∀ {P : Scheme.{u}} {U₁ U₂ U₃ : P.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (x : Γ(P, U₃)),
      P.presheaf.map (homOfLE h₁).op (P.presheaf.map (homOfLE h₂).op x) =
        P.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro P U₁ U₂ U₃ h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have res_inj : ∀ {P : Scheme.{u}} {U₁ U₂ : P.Opens} (e : U₁ = U₂) (x y : Γ(P, U₂)),
      P.presheaf.map (homOfLE e.le).op x = P.presheaf.map (homOfLE e.le).op y → x = y := by
    intro P U₁ U₂ e x y h
    subst e
    have : (homOfLE (le_refl U₁)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [this] using h

  let q : ∀ i j : Fin r, Away 𝒜 (F i) := fun i j =>
    Away.mk 𝒜 (hF i) 1 (F j) (by simpa only [one_smul] using hF j)
  have hV : ∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i)) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (F i) (hF i) hd
  refine ⟨fun i j => Proj.awayToSection 𝒜 (F i) (q i j), hV, ?_, ?_, ?_⟩
  ·
    intro i
    have : q i i = 1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one]
      simp only [q, Away.val_mk]
      rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩
    show Proj.awayToSection 𝒜 (F i) (q i i) = 1
    rw [this, map_one]
  ·
    intro i j k
    have e : Proj.basicOpen 𝒜 (F i * F j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) :=
      Proj.basicOpen_mul 𝒜 (F i) (F j)
    apply res_inj e
    simp only [map_mul, res_res]

    have h1 := congrArg (fun φ => φ.hom (q i k))
      (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h2 := congrArg (fun φ => φ.hom (q i j))
      (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h3 := congrArg (fun φ => φ.hom (q j k))
      (Proj.awayMap_awayToSection 𝒜 (f := F j) (hF i) (x := F i * F j) (mul_comm _ _))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2 h3

    rw [show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_left)).op (Proj.awayToSection 𝒜 (F i) (q i k)) = _ from h1.symm,
      show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_left)).op (Proj.awayToSection 𝒜 (F i) (q i j)) = _ from h2.symm,
      show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_right)).op (Proj.awayToSection 𝒜 (F j) (q j k)) = _ from h3.symm,
      ← map_mul]
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [q, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
    ring
  ·
    intro i j

    have hfrom : (hV i).fromSpec = Spec.map (Proj.awayToSection 𝒜 (F i)) ≫ Proj.awayι 𝒜 (F i) (hF i) hd := by
      rw [← Proj.basicOpenIsoSpec_inv_ι, ← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc]
      congr 1
      rw [← cancel_epi (hV i).isoSpec.hom, Iso.hom_inv_id, IsAffineOpen.isoSpec_hom, ← Category.assoc]
      show 𝟙 _ = Proj.basicOpenToSpec 𝒜 (F i) ≫ _
      rw [← Proj.basicOpenIsoSpec_hom 𝒜 (F i) (hF i) hd, Iso.hom_inv_id]

    have hpre : (hV i).fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 (F j) =
        PrimeSpectrum.basicOpen (Proj.awayToSection 𝒜 (F i) (q i j)) := by
      rw [hfrom, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 (hF i) hd (hF j) hd]
      have hq : Away.isLocalizationElem (hF i) (hF j) = q i j ^ d := by
        apply HomogeneousLocalization.val_injective
        simp only [q, Away.isLocalizationElem, Away.val_mk, HomogeneousLocalization.val_pow, Localization.mk_pow]
        congr 1
        exact Subtype.ext (by simp [← pow_mul, pow_one])
      rw [hq]
      conv_rhs => rw [← PrimeSpectrum.basicOpen_pow _ d hd, ← map_pow]
      ext1
      rfl
    rw [← (hV i).fromSpec_image_basicOpen, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
      IsAffineOpen.opensRange_fromSpec]

end S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
end P2MW


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {X Z : Scheme.{u}} (f : X ⟶ Z) {r : ℕ} (V : Fin r → Z.Opens) (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j) :
    (∀ i : Fin r, f.app (V i) (w i i) = 1) ∧
    (∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i k)) =
        X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i j)) *
          X.presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V j)).op (f.app (V j) (w j k))) ∧
    (∀ i j : Fin r, X.basicOpen (f.app (V i) (w i j)) = f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j) := by

  have nat : ∀ {U U' : Z.Opens} {W : X.Opens} (h : U ≤ U') (h' : W ≤ f ⁻¹ᵁ U') (h'' : W ≤ f ⁻¹ᵁ U)
      (x : Γ(Z, U')),
      X.presheaf.map (homOfLE h').op (f.app U' x) =
        X.presheaf.map (homOfLE h'').op (f.app U (Z.presheaf.map (homOfLE h).op x)) := by
    intro U U' W h h' h'' x
    have e := congrArg (fun φ => (X.presheaf.map (homOfLE h'').op).hom (φ.hom x)) (f.naturality (homOfLE h).op)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e
    have hh : (homOfLE h').op = ((Opens.map f.base).map (homOfLE h).op.unop).op ≫ (homOfLE h'').op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [e]
    change _ = (X.presheaf.map ((Opens.map f.base).map (homOfLE h).op.unop).op ≫
      X.presheaf.map (homOfLE h'').op).hom (f.app U' x)
    rw [← Functor.map_comp, ← hh]
  have hpre : ∀ i j : Fin r, f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ (V i ⊓ V j) := fun i j x hx => hx
  refine ⟨fun i => by rw [hW1, map_one], fun i j k => ?_, fun i j => ?_⟩
  · rw [nat (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (hpre i j) (w i k),
      nat (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (hpre i j) (w i j),
      nat (inf_le_right : V i ⊓ V j ≤ V j) inf_le_right (hpre i j) (w j k), hW2, map_mul, map_mul]
  · rw [← Scheme.preimage_basicOpen, hW3]
    rfl

end S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {Z : Scheme.{u}} {r : ℕ} (V : Fin r → Z.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j)
    (i₀ : Fin r) (g : Γ(Z, V i₀)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : ∀ j : Fin r, Γ(Z, V j), t i₀ = g ∧
      ∀ j m : Fin r,
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (t j) =
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (t m) := by
  classical

  have res_res : ∀ {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : Γ(Z, C)),
      Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op x) =
        Z.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro A B C h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have stepA : ∀ j : Fin r, ∃ (a : Γ(Z, V j)) (n : ℕ),
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op a =
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n *
          Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    letI : Algebra Γ(Z, V j) Γ(Z, V j ⊓ V i₀) :=
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op).hom.toAlgebra
    haveI : IsLocalization.Away (w j i₀) Γ(Z, V j ⊓ V i₀) :=
      (hV j).isLocalization_of_eq_basicOpen (w j i₀) (homOfLE inf_le_left) (hW3 j i₀).symm
    obtain ⟨⟨a, ⟨s, ⟨n, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (w j i₀))
      (Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g)
    refine ⟨a, n, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    rw [← h, mul_comm]
  choose a₀ n₀ ha₀ using stepA

  let a : ∀ j : Fin r, Γ(Z, V j) := Function.update a₀ i₀ g
  let n : Fin r → ℕ := Function.update n₀ i₀ 0
  have ha : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (a j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n j *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simp only [a, n, Function.update_self, pow_zero, one_mul]
    · simp only [a, n, Function.update_of_ne hj]
      exact ha₀ j

  let k₁ : ℕ := Finset.univ.sup n
  have hn : ∀ j, n j ≤ k₁ := fun j => Finset.le_sup (f := n) (Finset.mem_univ j)
  let b : ∀ j : Fin r, Γ(Z, V j) := fun j => a j * w j i₀ ^ (k₁ - n j)
  have hb : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (b j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ k₁ *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    simp only [b, map_mul, map_pow, ha]
    rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (hn j)]
  have hbi₀ : b i₀ = g := by
    simp only [b, a, n, Function.update_self, hW1, one_pow, mul_one]

  have stepB : ∀ j m : Fin r, ∃ e : ℕ,
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀) ^ e *
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
    intro j m
    have hjm : IsAffineOpen (V j ⊓ V m) := by rw [← hW3 j m]; exact (hV j).basicOpen (w j m)

    have hT : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) =
        Z.basicOpen (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)) := by
      rw [Scheme.basicOpen_res, hW3]
    letI : Algebra Γ(Z, V j ⊓ V m) Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      (Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op).hom.toAlgebra
    haveI : IsLocalization.Away (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀))
        Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      hjm.isLocalization_of_eq_basicOpen _ (homOfLE inf_le_left) hT

    have hvan : Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
      have e1 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_right : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V i₀)).op) (hb j)
      have e2 := congrArg (Z.presheaf.map (homOfLE
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V m ⊓ V i₀)).op) (hb m)
      have e3 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op) (hW2 j m i₀)
      simp only [map_sub, map_mul, map_pow, res_res] at e1 e2 e3 ⊢
      rw [e1, e2, e3]
      ring
    obtain ⟨⟨_, ⟨e, rfl⟩⟩, he⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)))
      Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) _).mp hvan
    exact ⟨e, he⟩
  choose e he using stepB

  let E : ℕ := Finset.univ.sup (fun jm : Fin r × Fin r => e jm.1 jm.2)
  have hE : ∀ j m, e j m ≤ E := fun j m =>
    Finset.le_sup (f := fun jm : Fin r × Fin r => e jm.1 jm.2) (Finset.mem_univ (j, m))
  refine ⟨k₁ + E, fun k hk => ⟨fun j => b j * w j i₀ ^ (k - k₁), ?_, ?_⟩⟩
  ·
    simp only [hbi₀, hW1, one_pow, mul_one]
  · intro j m
    obtain ⟨E', hE'⟩ : ∃ E', k = k₁ + (e j m + E') := ⟨k - k₁ - e j m, by have := hE j m; omega⟩
    have hkk : k - k₁ = e j m + E' := by omega
    have c := hW2 j m i₀
    have d := he j m
    simp only [map_mul, map_pow, hkk]
    rw [hE']
    rw [c] at d ⊢
    linear_combination ((Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) *
      Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (w m i₀)) ^ E') * d

end S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace QPC2


theorem isImmersion_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf => by haveI := hi; haveI := hf; infer_instance⟩

theorem surjective_app_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : V = U)
    (hs : Function.Surjective (f.app U)) : Function.Surjective (f.app V) := by
  subst e; exact hs

theorem isClosedImmersion_morphismRestrict_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (hfU : IsAffineOpen (f ⁻¹ᵁ U))
    (hs : Function.Surjective (f.app U)) : IsClosedImmersion (f ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hfU
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
  refine ⟨hfU, ?_⟩
  rw [morphismRestrict_appTop]
  have e : U.ι ''ᵁ ⊤ = U := by simp [Scheme.Hom.image_top_eq_opensRange]
  have h1 : Function.Surjective (f.app (U.ι ''ᵁ ⊤)) := surjective_app_of_eq f U _ e hs
  have h2 : Function.Surjective
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨z, rfl⟩ := h2 y
  obtain ⟨x, rfl⟩ := h1 z
  exact ⟨x, ConcreteCategory.comp_apply _ _ _⟩

theorem isImmersion_of_affine_charts {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type*} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ := by
  haveI := isImmersion_respectsRight_isOpenImmersion
  have hrange : Set.range φ.base ⊆ ((⨆ j, W j : P.Opens) : Set P) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (⨆ j, φ ⁻¹ᵁ W j : Y.Opens) := by rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨j, hj⟩ := hy
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨j, hj⟩
  exact IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) W hrange
    (fun j => by
      haveI := isClosedImmersion_morphismRestrict_of_surjective φ (W j) (hWaff j) (hYaff j) (hsurj j)
      infer_instance)

end QPC2

theorem solution
    {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type v} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ :=
  QPC2.isImmersion_of_affine_charts φ W hWaff hYaff hcov hsurj

end S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GluedPres

variable {Y : Scheme.{u}} {r : ℕ} {V : Fin r → Y.Opens} (c : PhilipponFiniteCocycle.UnitCocycle V)

def Compat (x : ∀ j : Fin r, Γ(Y, V j)) : Prop :=
  ∀ i j, rO (inf_le_left : V i ⊓ V j ≤ V i) (x i) = c.u i j * rO (inf_le_right : V i ⊓ V j ≤ V j) (x j)

noncomputable def sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) :=
  PhilipponFiniteCocycle.glueMk c ⊤ (fun j => rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j)) fun i j => by
    rw [rO_rO, rO_rO]
    have h := congrArg (rO (PhilipponFiniteCocycle.leij ⊤ i j)) (hx i j)
    rw [map_mul, rO_rO, rO_rO] at h
    exact h

theorem glueComponent_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c ⊤ j (sec c x hx) = rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j) := rfl

theorem glueComponent_map_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) {W : Y.Opens} (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c W j ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (sec c x hx)) =
      rO (inf_le_right : W ⊓ V j ≤ V j) (x j) := by
  rw [PhilipponFiniteCocycle.glueComponent_map, glueComponent_sec, rO_rO]

theorem map_sec_eq_glueFrame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (i : Fin r)
    (hxi : ∀ j, rO (inf_le_left : V j ⊓ V i ≤ V j) (x j) = c.u j i) :
    (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (sec c x hx) = PhilipponFiniteCocycle.glueFrame c i := by
  apply PhilipponFiniteCocycle.glue_ext
  intro j
  rw [glueComponent_map_sec, PhilipponFiniteCocycle.glueComponent_glueFrame, ← hxi j, rO_rO]

theorem bijective_smul_of_map_eq_glueFrame (s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤)) (i : Fin r)
    (hs : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s = PhilipponFiniteCocycle.glueFrame c i)
    (W : Y.Opens) (hW : W ≤ V i) :
    Function.Bijective fun g : Γ(Y, W) => g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
  have key : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op (PhilipponFiniteCocycle.glueFrame c i) := by
    rw [← hs]
    change _ = ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op ≫
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op) s
    rw [← Functor.map_comp]; rfl
  rw [key]
  exact PhilipponFiniteCocycle.isFrameOn_glueFrame c i hW hW

theorem subsingleton_sections_bot (M : Y.Modules) : Subsingleton (M.val.obj (op (⊥ : Y.Opens))) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (M.val.presheaf.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover ⟨M.val.presheaf, M.isSheaf⟩ (⊥ : Y.Opens) hbot
  have h0 : (𝟙 (M.val.presheaf.obj (op (⊥ : Y.Opens))) : _ ⟶ _) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) a) h0
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) b) h0
    simp at this
    exact this
  rw [ha, hb]

theorem subsingleton_functions_bot : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (Y.sheaf.val.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover Y.sheaf (⊥ : Y.Opens) hbot
  let e := hT.uniqueUpToIso CommRingCat.punitIsTerminal
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ x : Γ(Y, (⊥ : Y.Opens)), e.inv.hom (e.hom.hom x) = x := fun x => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) x) e.hom_inv_id
    simpa using this
  rw [← h1 a, ← h1 b, Subsingleton.elim (e.hom.hom a) (e.hom.hom b)]

theorem bijective_smul_bot (M : Y.Modules) (s : Γ(M, ⊤)) (W : Y.Opens) (hW : W ≤ ⊥) :
    Function.Bijective fun g : Γ(Y, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(M, W)) := by
  have hW' : W = ⊥ := le_bot_iff.1 hW
  subst hW'
  haveI : Subsingleton (Γ(M, (⊥ : Y.Opens)) : Type _) := subsingleton_sections_bot M
  haveI : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := subsingleton_functions_bot
  exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, Subsingleton.elim _ _⟩⟩

theorem isUnit_of_frames {M : Y.Modules} {W : Y.Opens} (s t : Γ(M, W))
    (hs : Function.Bijective fun g : Γ(Y, W) => g • s) (ht : Function.Bijective fun g : Γ(Y, W) => g • t)
    (f : Γ(Y, W)) (h : s = f • t) : IsUnit f := by
  obtain ⟨f', hf'⟩ := hs.2 t
  have hf'' : f' • s = t := hf'
  have h1 : (f * f') • s = (1 : Γ(Y, W)) • s := by
    rw [one_smul, mul_smul, hf'', ← h]
  exact isUnit_iff_exists_inv.2 ⟨f', hs.1 h1⟩

theorem inf_le_basicOpen_of_frame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (W : Y.Opens)
    (hW : ∀ W' : Y.Opens, W' ≤ W → Function.Bijective fun g : Γ(Y, W') =>
      g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W')))
    (j : Fin r) : W ⊓ V j ≤ Y.basicOpen (x j) := by

  set W' : Y.Opens := W ⊓ V j with hW'
  let s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx)
  let t : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : W' ≤ V j)).op (PhilipponFiniteCocycle.glueFrame c j)
  have hs : Function.Bijective fun g : Γ(Y, W') => g • s := hW W' inf_le_left
  have ht : Function.Bijective fun g : Γ(Y, W') => g • t := PhilipponFiniteCocycle.isFrameOn_glueFrame c j (inf_le_right : W' ≤ V j) inf_le_right
  obtain ⟨f, hf⟩ := ht.2 s
  have hfu : IsUnit f := isUnit_of_frames s t hs ht f hf.symm

  have hcomp : rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = rO (inf_le_left : W' ⊓ V j ≤ W') f := by
    have h1 := congrArg (PhilipponFiniteCocycle.glueComponent c W' j) hf
    rw [PhilipponFiniteCocycle.glueComponent_smul, PhilipponFiniteCocycle.glueComponent_map, PhilipponFiniteCocycle.glueComponent_glueFrame, rO_rO,
      show rO ((inf_le_inf_right (V j) (inf_le_right : W' ≤ V j)).trans (le_of_eq (inf_comm (V j) (V j)))) (c.u j j) = 1 by
        rw [c.refl, map_one], mul_one] at h1
    rw [h1]
    exact (glueComponent_map_sec c x hx j).symm
  have hu : IsUnit (rO (inf_le_right : W' ⊓ V j ≤ V j) (x j)) := by rw [hcomp]; exact hfu.map _
  have hb := Y.basicOpen_of_isUnit hu
  rw [show rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = Y.presheaf.map (homOfLE (inf_le_right : W' ⊓ V j ≤ V j)).op (x j) from rfl,
    Scheme.basicOpen_res] at hb
  calc W ⊓ V j = W' ⊓ V j := by rw [hW', inf_assoc, inf_idem]
    _ = W' ⊓ V j ⊓ Y.basicOpen (x j) := hb.symm
    _ ≤ Y.basicOpen (x j) := inf_le_right

theorem eq_of_smul_sec_eq {x x' : ∀ j : Fin r, Γ(Y, V j)} (hx : Compat c x) (hx' : Compat c x') (i : Fin r)
    (hxi : x i = 1) {D : Y.Opens} (hD : V i ≤ D) (g : Γ(Y, D))
    (h : g • (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x hx) =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x' hx')) :
    rO hD g = x' i := by

  have h2 := congrArg (PhilipponFiniteCocycle.glueComponent c D i) h
  rw [PhilipponFiniteCocycle.glueComponent_smul, glueComponent_map_sec, glueComponent_map_sec, hxi, map_one, mul_one] at h2

  have hinj := (rO_bijective_of_le_le (inf_le_right : D ⊓ V i ≤ V i) (le_inf hD le_rfl)).1
  apply hinj
  rw [rO_rO]
  exact h2

end GluedPres

open GluedPres in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j)
    (k : ℕ) (hk : 0 < k) (c : PhilipponFiniteCocycle.UnitCocycle V)
    (hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k)
    (N : ℕ) (a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j))
    (ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m))
    (e : Fin r → Fin (N + 1)) (he : Function.Injective e) (hae : ∀ i j : Fin r, a (e i) j = w j i ^ k) :
    ∃ 𝔓 : (PhilipponFiniteCocycle.glueOfCocycle c).ProjPresentation πY N,
      (∀ (α : Fin (N + 1)) (j : Fin r), PhilipponFiniteCocycle.glueComponent c ⊤ j (𝔓.σ α) =
        Y.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V j ≤ V j)).op (a α j)) ∧
      ∃ hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)),
        (∀ i : Fin r, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) = V i) ∧
        (∀ (i : Fin r) (α : Fin (N + 1)),
          𝔓.toProj.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
              (V i) (hV i)
            (Proj.awayToSection _ (MvPolynomial.X (e i)) (ProjSpace.ratio B N (e i) α)) = a α i) := by
  classical

  have hx : ∀ α : Fin (N + 1), Compat c (a α) := by
    intro α i j
    show rO _ (a α i) = c.u i j * rO _ (a α j)
    rw [hc]
    exact ha α i j
  let σ : Fin (N + 1) → Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) := fun α => sec c (a α) (hx α)

  have hσe : ∀ i : Fin r,
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (σ (e i)) = PhilipponFiniteCocycle.glueFrame c i := by
    intro i
    refine map_sec_eq_glueFrame c (a (e i)) (hx _) i fun j => ?_
    show rO _ (a (e i) j) = c.u j i
    rw [hae, map_pow, hc]

  let U' : Fin (N + 1) → Y.Opens := fun α => if h : ∃ i, e i = α then V h.choose else ⊥
  have hU'e : ∀ i, U' (e i) = V i := by
    intro i
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [U', dif_pos h]
    rw [he h.choose_spec]
  have hU' : iSup U' = ⊤ := by
    apply top_le_iff.1
    rw [← hcov]
    exact iSup_le fun i => (hU'e i).symm.le.trans (le_iSup U' (e i))
  have hframe : ∀ (α : Fin (N + 1)) (W : Y.Opens), W ≤ U' α →
      Function.Bijective fun g : Γ(Y, W) =>
        g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (σ α) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
    intro α W hW
    by_cases h : ∃ i, e i = α
    · obtain ⟨i, rfl⟩ := h
      rw [hU'e] at hW
      exact bijective_smul_of_map_eq_glueFrame c (σ (e i)) i (hσe i) W hW
    · have hbot : U' α = ⊥ := dif_neg h
      rw [hbot] at hW
      exact bijective_smul_bot _ _ W hW
  obtain ⟨𝔓, h𝔓σ, h𝔓U⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top πY (PhilipponFiniteCocycle.glueOfCocycle c) N σ U' hU' hframe
  have hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) :=
    fun i => (hU'e i).symm.le.trans (h𝔓U (e i))
  refine ⟨𝔓, ?_, hV, ?_, ?_⟩
  ·
    intro α j
    rw [h𝔓σ]
    exact glueComponent_sec c (a α) (hx α) j
  ·
    intro i
    refine le_antisymm ?_ (hV i)
    intro y hy
    have hy' : y ∈ (⊤ : Y.Opens) := trivial
    rw [← hcov] at hy'
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy'
    have hle := inf_le_basicOpen_of_frame c (a (e i)) (hx (e i))
      (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
      (fun W' hW' => by have hf := 𝔓.frame (e i) W' hW'; rw [h𝔓σ] at hf; exact hf) j
    have hyj : y ∈ Y.basicOpen (a (e i) j) := hle ⟨hy, hj⟩
    rw [hae, Y.basicOpen_pow _ hk, hw3] at hyj
    exact hyj.2
  ·
    intro i α
    have hr := 𝔓.app_ratio_smul (e i) α
    rw [h𝔓σ] at hr
    have h1 := eq_of_smul_sec_eq c (hx (e i)) (hx α) i (by rw [hae, hw1, one_pow]) (hV i) _ hr
    exact h1

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace AmpleChartsAux

theorem exists_finset_forall_surjective {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C) (hf : f.FiniteType) :
    ∃ s : Finset C, ∀ (D : Type u) [CommRing D] (ψ : D →+* C) (θ : B →+* D), ψ.comp θ = f →
      (∀ x ∈ s, x ∈ Set.range ψ) → Function.Surjective ψ := by
  letI : Algebra B C := f.toAlgebra
  obtain ⟨s, hs⟩ := hf
  refine ⟨s, fun D _ ψ θ hcomp hsub => ?_⟩
  let S : Subalgebra B C :=
    { carrier := Set.range ψ
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul ψ a b⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add ψ a b⟩
      algebraMap_mem' := fun r => ⟨θ r, by rw [← RingHom.comp_apply, hcomp]; rfl⟩ }
  have hle : Algebra.adjoin B (s : Set C) ≤ S := Algebra.adjoin_le hsub
  intro c
  have hc : c ∈ Algebra.adjoin B (s : Set C) := by rw [hs]; trivial
  exact hle hc

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def φ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U.1) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 (by simp)

lemma fromSpec_comp (U : X.affineOpens) : U.2.fromSpec ≫ f = Spec.map (φ f U) := by
  rw [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)).symm

lemma finiteType_φ [LocallyOfFiniteType f] (U : X.affineOpens) : (φ f U).hom.FiniteType := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  rw [φ, CommRingCat.hom_comp]
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)

lemma SpecMap_awayToSection_comp_awayι {n : ℕ} (i : Fin (n + 1)) :
    Spec.map (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos =
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos).fromSpec := by
  have hU := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos
  haveI : IsAffine (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) := hU
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp, Proj.basicOpenIsoSpec_hom, IsAffineOpen.isoSpec_hom, Proj.basicOpenToSpec]

end AmpleChartsAux

open AmpleChartsAux in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType πY]
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY := by
  classical

  let Va : Fin r → Y.affineOpens := fun i => ⟨V i, hVaff i⟩

  have hgen := fun i => exists_finset_forall_surjective (φ πY (Va i)).hom (finiteType_φ πY (Va i))
  choose s hs using hgen

  let I : Type u := Σ i : Fin r, ↥(s i)
  haveI : Fintype I := inferInstance
  have hC1 := fun x : I => P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution
    V hVaff w hw1 hw2 hw3 x.1 (x.2 : Γ(Y, V x.1))
  choose k₀ hk₀ using hC1
  let k : ℕ := (Finset.univ.sup k₀) + 1
  have hk : 0 < k := Nat.succ_pos _
  have hkx : ∀ x : I, k₀ x ≤ k := fun x => (Finset.le_sup (Finset.mem_univ x)).trans (Nat.le_succ _)
  have ht := fun x : I => hk₀ x k (hkx x)
  choose t ht₁ ht₂ using ht

  let M : ℕ := Fintype.card I
  let eI : I ≃ Fin M := Fintype.equivFin I
  let N : ℕ := r + M
  let a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j) := fun α =>
    if h : α.val < r then (fun j => w j ⟨α.val, h⟩ ^ k)
    else if h' : α.val - r < M then t (eI.symm ⟨α.val - r, h'⟩) else fun _ => 0
  let e : Fin r → Fin (N + 1) := fun i => ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h; exact Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hae : ∀ i j : Fin r, a (e i) j = w j i ^ k := by
    intro i j; simp only [a, e, dif_pos i.isLt]
  have a_ext : ∀ (x : I) (j : Fin r), a ⟨r + (eI x).val, by omega⟩ j = t x j := by
    intro x j
    simp only [a]
    rw [dif_neg (by omega), dif_pos (by simp)]
    congr 1
    have : (⟨r + (eI x).val - r, by omega⟩ : Fin M) = eI x := Fin.ext (by simp)
    rw [this, Equiv.symm_apply_apply]
  have ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m) := by
    intro α j m
    by_cases h : α.val < r
    · simp only [a, dif_pos h, map_pow]
      rw [hw2 j m ⟨α.val, h⟩, mul_pow]
    · by_cases h' : α.val - r < M
      · simp only [a, dif_neg h, dif_pos h']
        exact ht₂ _ j m
      · simp only [a, dif_neg h, dif_neg h', map_zero, mul_zero]

  let c : PhilipponFiniteCocycle.UnitCocycle V :=
    { u := fun i j => rO (inf_le_left : V i ⊓ V j ≤ V i) (w i j) ^ k
      refl := fun i => by simp only [hw1, map_one, one_pow]
      cocycle := fun i j l => by
        simp only [map_pow, rO_rO, ← mul_pow]
        congr 1
        have h := congrArg (rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V i ⊓ V j ⊓ V l ≤ V i ⊓ V j)) (hw2 i j l)
        rw [map_mul, rO_rO, rO_rO, rO_rO] at h
        exact h.symm }
  have hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k :=
    fun _ _ => rfl

  obtain ⟨𝔓, -, hVle, hpre, happ⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution
      B Y πY r V hVaff hcov w hw1 hw3 k hk c hc N a ha e he hae

  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B
  let W : Fin r → (Proj 𝒜).Opens := fun i => Proj.basicOpen 𝒜 (MvPolynomial.X (e i))
  have hWaff : ∀ i, IsAffineOpen (W i) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos
  have hYaff : ∀ i, IsAffineOpen (𝔓.toProj ⁻¹ᵁ W i) := fun i => by rw [hpre i]; exact hVaff i
  have hcov' : (⨆ i, 𝔓.toProj ⁻¹ᵁ W i) = ⊤ := by
    have : (fun i => 𝔓.toProj ⁻¹ᵁ W i) = V := funext hpre
    rw [this]; exact hcov
  have hsurj : ∀ i, Function.Surjective (𝔓.toProj.app (W i)) := by
    intro i

    let ψ : HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)) →+* Γ(Y, V i) :=
      (𝔓.toProj.appLE (W i) (V i) (hVle i)).hom.comp (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))).hom

    have hψB : ψ.comp (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) = (φ πY (Va i)).hom := by
      have key : CommRingCat.ofHom (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) ≫
          Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) ≫ 𝔓.toProj.appLE (W i) (V i) (hVle i) = φ πY (Va i) := by
        apply Spec.map_injective
        have h' : ∀ (Z : Scheme.{u}) (g : Proj 𝒜 ⟶ Z),
            Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))) ≫
              Proj.awayι 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos ≫ g = (hWaff i).fromSpec ≫ g :=
          fun Z g => by rw [← Category.assoc, SpecMap_awayToSection_comp_awayι]
        rw [Spec.map_comp, Spec.map_comp, ← fromSpec_comp, ← ProjSpace.awayι_comp_π, Category.assoc, h',
          ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec 𝔓.toProj (hWaff i) (hVaff i) (hVle i), Category.assoc,
          𝔓.toProj_π]
      have := congrArg CommRingCat.Hom.hom key
      simp [CommRingCat.hom_comp, RingHom.comp_assoc] at this
      exact this

    have hgen : ∀ x ∈ s i, x ∈ Set.range ψ := by
      intro x hx
      refine ⟨ProjSpace.ratio B N (e i) ⟨r + (eI ⟨i, ⟨x, hx⟩⟩).val, by omega⟩, ?_⟩
      change (𝔓.toProj.appLE (W i) (V i) (hVle i)) (Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) _) = x
      rw [happ i, a_ext ⟨i, ⟨x, hx⟩⟩ i, ht₁]
    have hψ : Function.Surjective ψ := hs i _ ψ _ hψB hgen

    have h1 : Function.Surjective (𝔓.toProj.appLE (W i) (V i) (hVle i)) := Function.Surjective.of_comp hψ
    have h2 : 𝔓.toProj.appLE (W i) (V i) (hVle i) = 𝔓.toProj.app (W i) ≫ Y.presheaf.map (homOfLE (hVle i)).op := rfl
    rw [h2] at h1
    have hbij := rO_bijective_of_le_le (X := Y) (hVle i) (le_of_eq (hpre i))
    intro y
    obtain ⟨x, hx⟩ := h1 (rO (hVle i) y)
    exact ⟨x, hbij.1 hx⟩
  refine ⟨N, 𝔓.toProj, ?_, 𝔓.toProj_π⟩
  exact P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution
    𝔓.toProj W hWaff hYaff hcov' hsurj

end S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P5FQP

theorem compactSpace_of_isImmersion_proj_of_isNoetherianRing
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {M : Scheme.{u}} {n : ℕ}
    (ι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)) [IsImmersion ι] : CompactSpace M := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (ProjSpace.π 𝒪 n)
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (ProjSpace.π 𝒪 n)
  haveI : IsNoetherian P := {}
  have hc : IsCompact (Set.range ι) := TopologicalSpace.NoetherianSpace.isCompact _
  rw [← Set.image_univ, ← ι.isEmbedding.isCompact_iff] at hc
  exact ⟨hc⟩

theorem exists_fin_cover {X : Scheme.{u}} [CompactSpace X] (O : X → X.Opens) (hO : ∀ x, x ∈ O x) :
    ∃ (r : ℕ) (c : Fin r → X), (⨆ i, O (c i)) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (O x : Set X)) (fun x => (O x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hO x⟩)
  refine ⟨t.card, fun i => (t.equivFin.symm i).1, ?_⟩
  apply top_le_iff.mp
  intro y _
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
  obtain ⟨hxt, hyx⟩ := Set.mem_iUnion.mp hx
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, by simpa using hyx⟩

end P5FQP

namespace P12FQP
open P5FQP

theorem exists_affineCover_cocycle_of_isImmersion_proj
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {M : Scheme.{u}} {n : ℕ}
    (ι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)) [IsImmersion ι] :
    ∃ (r : ℕ) (U : Fin r → M.Opens) (w : ∀ i j : Fin r, Γ(M, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      (∀ i, w i i = 1) ∧
      (∀ i j k : Fin r,
        M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
          M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
            M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k)) ∧
      (∀ i j : Fin r, M.basicOpen (w i j) = U i ⊓ U j) := by
  classical
  haveI : CompactSpace M := compactSpace_of_isImmersion_proj_of_isNoetherianRing ι
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪

  have hA1 : ∀ x : M, ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) 𝒪), F ∈ 𝒜 d ∧ 0 < d ∧
      x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F ∧ IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) := by
    intro x
    obtain ⟨d, F, hFd, hd, hS, haff, -⟩ :=
      P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution 𝒜 ι {x}
    exact ⟨d, F, hFd, hd, hS x (Finset.mem_singleton_self x), haff⟩
  choose d F hFd hd hmem haff using hA1
  obtain ⟨r, c, hcov⟩ := exists_fin_cover (fun x => ι ⁻¹ᵁ Proj.basicOpen 𝒜 (F x)) hmem

  let D : ℕ := ∏ i : Fin r, d (c i)
  have hDpos : 0 < D := Finset.prod_pos fun i _ => hd (c i)
  have hdvd : ∀ i : Fin r, d (c i) ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let e : Fin r → ℕ := fun i => D / d (c i)
  have he : ∀ i, e i * d (c i) = D := fun i => Nat.div_mul_cancel (hdvd i)
  have hepos : ∀ i, 0 < e i := fun i => Nat.div_pos (Nat.le_of_dvd hDpos (hdvd i)) (hd (c i))
  let G : Fin r → MvPolynomial (Fin (n + 1)) 𝒪 := fun i => F (c i) ^ e i
  have hG : ∀ i, G i ∈ 𝒜 D := by
    intro i
    have := SetLike.pow_mem_graded (e i) (hFd (c i))
    rwa [smul_eq_mul, he i] at this
  have hGF : ∀ i, Proj.basicOpen 𝒜 (G i) = Proj.basicOpen 𝒜 (F (c i)) := fun i =>
    Proj.basicOpen_pow 𝒜 _ _ (hepos i)

  obtain ⟨v, -, hv1, hv2, hv3⟩ :=
    P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution 𝒜 hDpos G hG
  obtain ⟨hu1, hu2, hu3⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution ι
      (fun i => Proj.basicOpen 𝒜 (G i)) v hv1 hv2 hv3
  refine ⟨r, fun i => ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i), fun i j => ι.app _ (v i j), ?_, ?_, hu1, hu2, hu3⟩
  · intro i
    show IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i))
    rw [hGF i]
    exact haff (c i)
  · show (⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i)) = ⊤
    rw [show (⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i)) = ⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (F (c i)) from
      iSup_congr fun i => by rw [hGF i]]
    exact hcov

end P12FQP

open P12FQP in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {Z M : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ζ : Z ⟶ M) [IsFinite ζ]
    (hM : ∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM) :
    ∃ (qpn : ℕ) (qpι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = ζ ≫ πM := by
  classical
  obtain ⟨n, ι, hι, hιπ⟩ := hM
  haveI : IsImmersion ι := hι

  obtain ⟨r, U, w, hUaff, hUcov, hw1, hw2, hw3⟩ := P12FQP.exists_affineCover_cocycle_of_isImmersion_proj ι
  obtain ⟨hw1', hw2', hw3'⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution ζ U w hw1 hw2 hw3

  haveI : LocallyOfFiniteType ι := by
    rw [← ι.liftCoborder_ι]; infer_instance
  haveI : LocallyOfFiniteType πM := by
    rw [← hιπ]; infer_instance
  haveI : LocallyOfFiniteType (ζ ≫ πM) := inferInstance

  have hVaff : ∀ i : Fin r, IsAffineOpen (ζ ⁻¹ᵁ U i) := fun i => (hUaff i).preimage ζ
  have hVcov : (⨆ i, ζ ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hUcov, Scheme.Hom.preimage_top]
  exact P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution
    𝒪 Z (ζ ≫ πM) r (fun i => ζ ⁻¹ᵁ U i) hVaff hVcov (fun i j => ζ.app (U i) (w i j)) hw1' hw2' hw3'

end S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing
end P2MW
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveNormalization

lemma topological_dimension_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [show topologicalKrullDim X = Order.krullDim X from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  simp_rw [Order.krullDim_eq_iSup_coheight, ringKrullDim_stalk_eq_coheight]

lemma topological_dimension_eq_of_surjective_of_stalk_dimension
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Surjective f.base)
    (hd : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) =
      ringKrullDim (X.presheaf.stalk (f y))) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  rw [topological_dimension_eq_iSup_stalk, topological_dimension_eq_iSup_stalk]
  simp_rw [hd]
  exact hf.iSup_comp (fun x : X => ringKrullDim (X.presheaf.stalk x))

lemma exists_closed_embedding_of_finite_over_projective
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (ν : Y ⟶ X) [IsFinite ν]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (m : ℕ)
      (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by
  obtain ⟨m, j, hj, hπ⟩ :=
    P2MW.S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing.solution
      π ν ⟨n, i, inferInstance, hi⟩
  letI := hj
  haveI : IsProper (j ≫ ProjSpace.π K m) := by rw [hπ]; infer_instance
  haveI : IsProper j := IsProper.of_comp j (ProjSpace.π K m)
  exact ⟨m, j, IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range, hπ⟩

theorem exists_normal_integral_projective_finite_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X),
      IsIntegral Y ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsFinite ν ∧ Surjective ν ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by
  obtain ⟨Y, ν, hY, hnormal, hν, hsurj, hdim, _⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral K π
  letI := hY
  letI := hν
  exact ⟨Y, ν, hY, hnormal, hν, ⟨hsurj⟩,
    topological_dimension_eq_of_surjective_of_stalk_dimension ν hsurj hdim,
    exists_closed_embedding_of_finite_over_projective K π ν n i hi⟩

end PhilipponProjectiveNormalization
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A projective embedding over a finite extension gives a projective
embedding over the original field with exactly the composite structure map. -/
theorem PhilipponFiniteFieldProjectiveEmbedding.exists_embedding
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of E))
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π E n = π) :
    ∃ (m : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k)),
      IsClosedImmersion i ∧ i ≫ ProjSpace.π k m =
        π ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E))
  haveI : IsFinite b :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let pb := ProjSpace.isPullback_map k E n
  haveI : IsFinite (ProjSpace.map k E n) :=
    MorphismProperty.of_isPullback pb.flip (inferInstance : IsFinite b)
  let ν := j ≫ ProjSpace.map k E n
  obtain ⟨m, i, hi, hbase⟩ :=
    PhilipponProjectiveNormalization.exists_closed_embedding_of_finite_over_projective
      k (ProjSpace.π k n) ν n (𝟙 _) (by simp)
  refine ⟨m, i, hi, ?_⟩
  calc
    i ≫ ProjSpace.π k m = (j ≫ ProjSpace.map k E n) ≫ ProjSpace.π k n := hbase
    _ = j ≫ (ProjSpace.π E n ≫ b) := by rw [Category.assoc, pb.w]
    _ = π ≫ b := by rw [← Category.assoc, hj]

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A smooth integral projective cover over an algebraic extension,
surjecting to the original target and not increasing dimension, descends
to a regular projective alteration over the original field. The cover
and dimension bound are inputs; their geometric construction is not
assumed to follow from an unproved alteration theorem. -/
theorem PhilipponAlgebraicAlterationDescent.exists_alteration
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Spec (.of k)) [IsProper π]
    (d : ℕ) (hdX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (σ : Y ⟶ Spec (.of L)) [Smooth σ]
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) L))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π L n = σ)
    (φ : Y ⟶ X) [Surjective φ]
    (hφ : φ ≫ π = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hdY : topologicalKrullDim Y ≤ topologicalKrullDim X) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ Surjective a ∧
      (∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) ∧
      (∃ W : X.Opens, Nonempty W ∧ IsFinite (a ∣_ W)) ∧
      ∃ (m : ℕ) (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π k m = a ≫ π := by
  haveI : IsProper σ := by rw [← hj]; infer_instance
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace σ
  letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated σ
  obtain ⟨E, hE, Z, τ, g, a, jE, hpb, hjE, hjEbase, hover, hrec⟩ :=
    PhilipponProjectiveFieldDescent.exists_projective_relative_finite_model
      k L X π Y σ n j hj φ hφ
  letI := hE
  letI := hjE
  haveI : IsProper τ := by rw [← hjEbase]; infer_instance
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    MorphismProperty.of_isPullback hpb.flip (PhilipponFieldModelProperties.fpqc_fieldMap E L)
  letI : Surjective g := hfpqc.1.1
  letI : Flat g := hfpqc.1.2
  letI : IsIntegral Z := PhilipponFieldModelIntegral.isIntegral_of_flat_surjective g
  letI : Smooth τ := PhilipponFieldModelProperties.smooth_of_isPullback_field
    E L τ σ g hpb inferInstance
  let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  haveI : IsFinite bE :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsProper (a ≫ π) := by rw [hover]; infer_instance
  haveI : IsProper a := IsProper.of_comp a π
  haveI : Surjective a := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := φ.surjective x
    refine ⟨g y, ?_⟩
    change (g ≫ a) y = x
    rw [hrec]
    exact hy
  have hdZ : topologicalKrullDim Z ≤ topologicalKrullDim X :=
    (PhilipponFaithfullyFlatDimension.dimension_le_of_flat_surjective g).trans hdY
  obtain ⟨m, i, hi, hibase⟩ :=
    PhilipponFiniteFieldProjectiveEmbedding.exists_embedding k E τ n jE hjEbase
  refine ⟨Z, a, inferInstance, inferInstance, inferInstance,
    (fun z => PhilipponSmoothSchemeRegular.stalk E τ z),
    PhilipponProperGenericFiniteness.exists_finite_open_of_dimension_le k π a d hdX hdZ,
    m, i, hi, ?_⟩
  exact hibase.trans hover.symm

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponReducedClosedSubscheme

theorem radical_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  apply (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mpr
  exact isReduced_of_injective (I.subschemeObjIso U).inv.hom
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.radical = I) : IsReduced I.subscheme := by
  have hU (U : X.affineOpens) : (I.ideal U).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    exact congrArg (fun J : X.IdealSheafData => J.ideal U) h
  haveI (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hU U)
  haveI (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem isReduced_iff_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsReduced I.subscheme ↔ I.radical = I :=
  ⟨fun h => @radical_eq_of_isReduced X I h, isReduced_of_radical_eq I⟩

theorem integral_of_prime_top {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)
    [(I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime] : IsIntegral I.subscheme := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  haveI : (I.ideal U).IsPrime :=
    (inferInstance : (I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime)
  haveI : IsDomain (Γ(X, U) ⧸ I.ideal U) := inferInstance
  let f := I.subschemeCover.f U
  haveI : Surjective f := by
    constructor
    intro x
    have hx : x ∈ f.opensRange := by
      change x ∈ (I.subschemeCover.f U).opensRange
      rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
      trivial
    exact hx
  haveI : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : IsIntegral (Spec (I.subschemeCover.X U)) := by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsIntegral.of_isIso f

theorem radical_comap_open {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : (I.comap f).radical = I.radical.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((I.comap f).ideal U).radical = (I.radical.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Ideal.comap_radical _ _).symm

theorem eq_of_reduced_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : I.radical = I) (hJ : J.radical = J) (hs : I.support = J.support) : I = J := by
  rw [← hI, ← Scheme.IdealSheafData.vanishingIdeal_support, hs,
    Scheme.IdealSheafData.vanishingIdeal_support, hJ]

end PhilipponReducedClosedSubscheme

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponSchemeImageIntegral

/-- The scheme-theoretic image of a reduced source is reduced. -/
theorem ker_radical {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (f.ker.ideal U).radical = f.ker.ideal U
  rw [f.ker_apply U]
  change (Ideal.comap (f.app U).hom ⊥).radical = Ideal.comap (f.app U).hom ⊥
  rw [← Ideal.comap_radical,
    Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot : (⊥ : Ideal Γ(X, f ⁻¹ᵁ U)).IsRadical)]

instance image_isReduced {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : IsReduced f.image :=
  PhilipponReducedClosedSubscheme.isReduced_of_radical_eq f.ker (ker_radical f)

/-- No immersion hypothesis is needed for integrality of the actual
scheme-theoretic image of a quasi-compact map from an integral scheme. -/
theorem image_isIntegral {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) [QuasiCompact f] : IsIntegral f.image := by
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image
        f.toImage f.toImage.continuous.continuousOn
  letI : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PhilipponSchemeImageIntegral

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponIntegralAlgebraicBaseChange

/-- A universally closed surjection onto an integral scheme has an
integral closed subscheme still surjecting onto the original target.
No finite-type hypothesis on the original surjection is required. -/
theorem exists_integral_closed_dominating {X Z : Scheme.{u}} [IsIntegral X]
    (p : Z ⟶ X) [UniversallyClosed p] [Surjective p] :
    ∃ (C : Scheme.{u}) (i : C ⟶ Z),
      IsIntegral C ∧ IsClosedImmersion i ∧ Surjective (i ≫ p) := by
  obtain ⟨z, hz⟩ := p.surjective (genericPoint X)
  let s := Z.fromSpecResidueField z
  haveI : QuasiCompact s := inferInstance
  haveI : IsIntegral s.image := PhilipponSchemeImageIntegral.image_isIntegral s
  have hzS : z ∈ Set.range s := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.mem_singleton z
  obtain ⟨t, ht⟩ := hzS
  let g := s.imageι ≫ p
  have hgen : genericPoint X ∈ Set.range g := by
    refine ⟨s.toImage t, ?_⟩
    change (s.toImage ≫ s.imageι ≫ p) t = genericPoint X
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact (congrArg p ht).trans hz
  haveI : Surjective g := by
    constructor
    have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    have hall : Set.univ ⊆ Set.range g := by
      rw [← genericPoint_spec X]
      exact closure_minimal (Set.singleton_subset_iff.mpr hgen) hc
    exact fun x => hall (Set.mem_univ x)
  exact ⟨s.image, s.imageι, inferInstance, inferInstance, inferInstance⟩

/-- After an arbitrary algebraic field extension, a projective integral
target has an integral closed subscheme of the actual base change that
surjects to the original target and does not increase dimension. The
actual projective structure map over the extension field is retained. -/
theorem exists_integral_projective_dominating
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of k))
    (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π k n = π) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
    ∃ (C : Scheme.{u}) (i : C ⟶ pullback π b) (σ : C ⟶ Spec (.of L)),
      IsIntegral C ∧ IsClosedImmersion i ∧ Surjective (i ≫ pullback.fst π b) ∧
      topologicalKrullDim C ≤ topologicalKrullDim X ∧ i ≫ pullback.snd π b = σ ∧
      ∃ e : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) L),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π L n = σ := by
  dsimp only
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  haveI : IsIntegralHom b :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  haveI : Surjective b := (PhilipponFieldModelProperties.fpqc_fieldMap k L).1.1
  let p := pullback.fst π b
  obtain ⟨C, i, hC, hi, hsurj⟩ := exists_integral_closed_dominating p
  letI := hi
  obtain ⟨P, jP, hjP, eP, H, _⟩ :=
    ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map j L
  rw [hj] at H
  letI := hjP
  let jL := H.isoPullback.inv ≫ jP
  have hjL : jL ≫ ProjSpace.π L n = pullback.snd π b := by
    dsimp only [jL]
    rw [Category.assoc, H.isoPullback_inv_snd]
  refine ⟨C, i, i ≫ pullback.snd π b, hC, hi, hsurj, ?_, rfl,
    i ≫ jL, inferInstance, ?_⟩
  · exact i.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans
      (PhilipponIntegralDimension.dimension_le_algebraic_baseChange k L π)
  · rw [Category.assoc, hjL]

end PhilipponIntegralAlgebraicBaseChange

end
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

theorem PhilipponProperOpenCompactification.isIso
    {Z Y S : Scheme.{u}} (j : Z ⟶ Y) (π : Y ⟶ S)
    [IsOpenImmersion j] [IsDominant j] [IsSeparated π]
    [IsProper (j ≫ π)] : IsIso j := by
  have : IsProper j := IsProper.of_comp j π
  have : Surjective j := inferInstance
  have : Epi j.base := (TopCat.epi_iff_surjective j.base).mpr j.surjective
  exact IsOpenImmersion.isIso j

end

section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationOpenRestriction

lemma finite_restrict_pullback {Z Y X C : Scheme.{u}}
    (a : Z ⟶ X) (c : Z ⟶ Y) (j : X ⟶ C) (f : Y ⟶ C)
    (H : IsPullback a c j f) (W : C.Opens) [IsFinite (f ∣_ W)] :
    IsFinite (a ∣_ (j ⁻¹ᵁ W)) := by
  have H' := Scheme.Hom.isPullback_resLE H (US := W) (UT := f ⁻¹ᵁ W)
    (UX := j ⁻¹ᵁ W) le_rfl le_rfl (UY := a ⁻¹ᵁ (j ⁻¹ᵁ W)) (by
      rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, inf_idem])
  have hf : IsFinite (f.resLE W (f ⁻¹ᵁ W) le_rfl) := by
    simpa [Scheme.Hom.resLE] using (inferInstance : IsFinite (f ∣_ W))
  have h := MorphismProperty.of_isPullback H'.flip (P := @IsFinite) hf
  simpa [Scheme.Hom.resLE] using h

/-- Restricting one regular projective alteration of an integral proper
compactification gives an alteration with the same regular projective compactification. -/
theorem exists_of_compactification
    (K : Type u) [Field K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (π : X ⟶ Spec (.of K)) (πC : C ⟶ Spec (.of K))
    (j : X ⟶ C) [IsOpenImmersion j] [IsDominant j] (hj : j ≫ πC = π)
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ C) [IsProper f] [IsDominant f]
    (hfinite : ∃ W : C.Opens, Nonempty W ∧ IsFinite (f ∣_ W))
    (πY : Y ⟶ Spec (.of K)) [IsProper πY]
    (hf : f ≫ πC = πY) (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (m : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K m = πY) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ IsDominant a ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of K)),
        IsIntegral Y ∧ IsProper πY ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        ∃ c : Z ⟶ Y, IsOpenImmersion c ∧ IsDominant c ∧ c ≫ πY = a ≫ π ∧
        ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = πY := by
  let Z := pullback j f
  let a : Z ⟶ X := pullback.fst j f
  let c : Z ⟶ Y := pullback.snd j f
  haveI : Surjective f := inferInstance
  haveI : Surjective a := inferInstanceAs (Surjective (pullback.fst j f))
  haveI : Nonempty Z := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, -⟩ := a.surjective x
    exact ⟨z⟩
  haveI : IsOpenImmersion c := inferInstanceAs (IsOpenImmersion (pullback.snd j f))
  haveI : IsIntegral Z := isIntegral_of_isOpenImmersion c
  haveI : IsDominant c := ⟨c.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have H : IsPullback a c j f := IsPullback.of_hasPullback j f
  obtain ⟨W, hW, hfin⟩ := hfinite
  letI := hfin
  have hV : Nonempty (j ⁻¹ᵁ W) := by
    obtain ⟨x, hx⟩ := j.denseRange.exists_mem_open W.isOpen (by
      obtain ⟨w⟩ := hW
      exact ⟨w.val, w.property⟩)
    exact ⟨⟨x, hx⟩⟩
  refine ⟨Z, a, inferInstance, inferInstance, inferInstance,
    ⟨j ⁻¹ᵁ W, hV, finite_restrict_pullback a c j f H W⟩,
    Y, πY, inferInstance, inferInstance, hreg, c, inferInstance, inferInstance, ?_,
    m, i, inferInstance, hi⟩
  rw [← hf, ← Category.assoc, ← H.w, Category.assoc, hj]

end PhilipponAlterationOpenRestriction

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponBirationalAlterationComposition

/-- A proper map from an integral scheme with an open section is an
isomorphism over the section's original nonempty open. -/
theorem isIso_restrict_of_open_section {X Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ X) [IsProper p] (U : X.Opens) [Nonempty U]
    (s : U.toScheme ⟶ Y) [IsOpenImmersion s] (hs : s ≫ p = U.ι) :
    IsIso (p ∣_ U) := by
  let L := p ⁻¹ᵁ U
  have hr : Set.range s ⊆ Set.range L.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨s x, ?_⟩, rfl⟩
    change (s ≫ p) x ∈ U
    rw [hs]
    exact x.property
  let t := IsOpenImmersion.lift L.ι s hr
  have ht : t ≫ L.ι = s := IsOpenImmersion.lift_fac ..
  have htp : t ≫ (p ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, ht, hs, Category.id_comp]
  haveI : IsOpenImmersion (t ≫ L.ι) := ht.symm ▸ inferInstance
  haveI : IsOpenImmersion t := IsOpenImmersion.of_comp t L.ι
  haveI : Nonempty L.toScheme := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨t x⟩
  haveI : IsIntegral L.toScheme := isIntegral_of_isOpenImmersion L.ι
  haveI : IsDominant t :=
    ⟨t.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : IsProper (t ≫ (p ∣_ U)) := htp.symm ▸ inferInstance
  haveI : IsIso t := PhilipponProperOpenCompactification.isIso t (p ∣_ U)
  have h : p ∣_ U = inv t := by
    rw [← cancel_epi t, htp, IsIso.hom_inv_id]
  rw [h]
  infer_instance

/-- Finiteness on a local cartesian model descends to its open image. -/
theorem finite_restrict_image {L Z U X : Scheme.{u}}
    (p : L ⟶ U) (i : L ⟶ Z) (j : U ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion j] (H : IsPullback p i j q)
    (W : U.Opens) [IsFinite (p ∣_ W)] :
    IsFinite (q ∣_ (W.ι ≫ j).opensRange) := by
  have h := (isPullback_morphismRestrict p W).paste_vert H
  haveI : IsFinite (pullback.snd q (W.ι ≫ j)) :=
    h.flip.isoPullback_inv_snd ▸
      (inferInstance : IsFinite (h.flip.isoPullback.inv ≫ (p ∣_ W)))
  exact ((MorphismProperty.arrow_mk_iso_iff @IsFinite)
    (morphismRestrictOpensRange q (W.ι ≫ j))).mpr inferInstance

/-- A map finite over a nonempty open remains generically finite after
composition with a map that is an isomorphism over a nonempty open. -/
theorem finite_open_comp {Z Y X : Scheme.{u}} [IsIntegral Y]
    (q : Z ⟶ Y) (p : Y ⟶ X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)]
    (V : Y.Opens) [Nonempty V] [IsFinite (q ∣_ V)] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite ((q ≫ p) ∣_ W) := by
  let L := p ⁻¹ᵁ U
  let b : L.toScheme ⟶ X := L.ι ≫ p
  have hb : b = (p ∣_ U) ≫ U.ι := (morphismRestrict_ι p U).symm
  haveI : IsOpenImmersion b := hb.symm ▸ inferInstance
  have hbr : b.opensRange = U := by
    ext x
    change x ∈ Set.range b ↔ x ∈ U
    rw [hb, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (p ∣_ U).surjective.range_eq, Set.image_univ, Scheme.Opens.range_ι]
    rfl
  haveI : Nonempty L.toScheme := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨inv (p ∣_ U) x⟩
  let W : L.toScheme.Opens := L.ι ⁻¹ᵁ V
  haveI : Nonempty W := by
    have hL : (L : Set Y).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty L.toScheme)
      exact ⟨x.val, x.property⟩
    have hV : (V : Set Y).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty V)
      exact ⟨x.val, x.property⟩
    obtain ⟨y, hyL, hyV⟩ :=
      nonempty_preirreducible_inter L.isOpen V.isOpen hL hV
    exact ⟨⟨⟨y, hyL⟩, hyV⟩⟩
  have H : IsPullback (q ∣_ L) (q ⁻¹ᵁ L).ι b (q ≫ p) := by
    apply IsOpenImmersion.isPullback
    · dsimp only [b]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ p) (morphismRestrict_ι q L).symm
    · rw [hbr, Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage]
  haveI : IsFinite ((q ∣_ L) ∣_ W) :=
    PhilipponAlterationOpenRestriction.finite_restrict_pullback
      (q ∣_ L) (q ⁻¹ᵁ L).ι L.ι q (isPullback_morphismRestrict q L) V
  refine ⟨(W.ι ≫ b).opensRange, ?_,
    finite_restrict_image (q ∣_ L) (q ⁻¹ᵁ L).ι b (q ≫ p) H W⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  exact ⟨⟨(W.ι ≫ b) w, ⟨w, rfl⟩⟩⟩

end PhilipponBirationalAlterationComposition

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponFiniteAlterationComposition

/-- An integral source has only its generic point over the generic point
of an integral target under a dominant locally quasi-finite map. -/
theorem preimage_genericPoint {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] [LocallyQuasiFinite p] :
    p ⁻¹' {genericPoint X} = {genericPoint Y} := by
  have hpη := PhilipponGenericDominance.genericPoint_eq_of_dominant p
  ext y
  change p y = genericPoint X ↔ y = genericPoint Y
  constructor
  · intro hy
    exact ((p.isDiscrete_preimage_singleton (genericPoint X)).eq_of_specializes
      (genericPoint_specializes y) hpη hy).symm
  · rintro rfl
    exact hpη

/-- A finite dominant map admits a nonempty target open whose entire
inverse image lies in any prescribed nonempty open of its integral source. -/
theorem exists_open_preimage_le {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsFinite p] [IsDominant p]
    (V : Y.Opens) [Nonempty V] :
    ∃ W : X.Opens, Nonempty W ∧ p ⁻¹ᵁ W ≤ V := by
  let W : X.Opens := ⟨(p '' (V : Set Y)ᶜ)ᶜ,
    (p.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))
  have hηW : genericPoint X ∈ W := by
    rintro ⟨y, hy, hpy⟩
    have hyη : y = genericPoint Y := by
      have hy' : y ∈ p ⁻¹' {genericPoint X} := hpy
      rw [preimage_genericPoint p] at hy'
      exact hy'
    exact hy (hyη.symm ▸ hηV)
  refine ⟨W, ⟨⟨genericPoint X, hηW⟩⟩, ?_⟩
  intro y hy
  change p y ∉ p '' (V : Set Y)ᶜ at hy
  by_contra hyV
  exact hy ⟨y, hyV, rfl⟩

/-- Finiteness over an open restricts to every smaller target open. -/
theorem finite_restrict_of_le {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (D V : Y.Opens) (hDV : D ≤ V) [IsFinite (q ∣_ V)] :
    IsFinite (q ∣_ D) := by
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ D
  have h := PhilipponBirationalAlterationComposition.finite_restrict_image
    (q ∣_ V) (q ⁻¹ᵁ V).ι V.ι q (isPullback_morphismRestrict q V) W
  have he : (W.ι ≫ V.ι).opensRange = D := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ D) = D
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hDV]
  exact (congrArg (fun E : Y.Opens => IsFinite (q ∣_ E)) he).mp h

/-- Generic finiteness survives composition with a finite dominant map.
This applies in particular to finite normalization, without first
assuming an isomorphism locus for the normalization map. -/
theorem finite_open_comp {Z Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (q : Z ⟶ Y) (p : Y ⟶ X) [IsFinite p] [IsDominant p]
    (V : Y.Opens) [Nonempty V] [IsFinite (q ∣_ V)] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite ((q ≫ p) ∣_ W) := by
  obtain ⟨W, hW, hWV⟩ := exists_open_preimage_le p V
  haveI : IsFinite (q ∣_ (p ⁻¹ᵁ W)) := finite_restrict_of_le q _ V hWV
  refine ⟨W, hW, ?_⟩
  rw [morphismRestrict_comp]
  infer_instance

end PhilipponFiniteAlterationComposition

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite normalization reduces the higher-dimensional regular alteration
problem to normal projective targets over the same arbitrary field. The
normal-target construction is an explicit hypothesis; its conclusion
includes generic finiteness, which is proved to survive composition. -/
theorem PhilipponRegularAlterationNormalization.exists_of_normal_case
    (K : Type u) [Field K]
    (H : ∀ {T : Scheme.{u}} [IsIntegral T] (σ : T ⟶ Spec (.of K))
      (m : ℕ) (j : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K))
      [IsClosedImmersion j], j ≫ ProjSpace.π K m = σ →
      (∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) →
      1 < topologicalKrullDim T →
      ∃ (Y : Scheme.{u}) (a : Y ⟶ T),
        IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        (∃ V : T.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
        ∃ (r : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)),
          IsClosedImmersion i ∧ i ≫ ProjSpace.π K r = a ≫ σ)
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  haveI : IsProper π := by rw [← hι]; infer_instance
  obtain ⟨N, p, hN, hnormal, hfinite, hsurj, hdimN, m, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_normal_integral_projective_finite_cover K π n ι hι
  letI := hN
  letI := hfinite
  letI := hsurj
  letI := hj
  obtain ⟨Y, q, hY, hproperq, hsurjq, hreg, ⟨V, hV, hVfinite⟩,
    r, i, hi, hibase⟩ := H (p ≫ π) m j hjbase hnormal (by rw [hdimN]; exact hdim)
  letI := hproperq
  letI := hsurjq
  letI := hV
  letI := hVfinite
  refine ⟨Y, q ≫ p, hY, inferInstance, inferInstance, hreg,
    PhilipponFiniteAlterationComposition.finite_open_comp q p V,
    r, i, hi, ?_⟩
  simpa only [Category.assoc] using hibase

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponRegularProjectiveCurveAlteration

-- These two proofs reuse PhilipponCurveAlteration's local argument,
-- without importing its algebraically closed smooth-cover theorem.
lemma regularLocalRing_of_integrallyClosed_of_dimension_le_one
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] (hdim : ringKrullDim R ≤ 1) :
    IsRegularLocalRing R := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  have hprime : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R := by
    intro P hP hp
    exact IsLocalRing.eq_maximalIdeal (hp.isMaximal_of_ne_bot hP)
  have hT : IsPrincipalIdealRing R ↔
      (IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R) :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 0 3
  letI : IsPrincipalIdealRing R := hT.mpr ⟨inferInstance, hprime⟩
  infer_instance

lemma stalk_dimension_le_topological {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact (Order.coheight_le_krullDim x).trans_eq
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm

/-- Normalization proves the full regular projective alteration conclusion
in dimension at most one over an arbitrary field. The map is finite everywhere. -/
theorem exists_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsFinite a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  haveI : IsProper π := by rw [← hι]; infer_instance
  obtain ⟨Y, a, hY, hnormal, hfinite, hsurj, hdimY, m, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_normal_integral_projective_finite_cover K π n ι hι
  letI := hY
  letI := hfinite
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (a ≫ π)
  have hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
    intro y
    letI := hnormal y
    apply regularLocalRing_of_integrallyClosed_of_dimension_le_one
    exact (stalk_dimension_le_topological y).trans (hdimY.trans_le hdim)
  exact ⟨Y, a, hY, hfinite, hsurj, hreg, hdimY, m, j, hj, hjbase⟩

/-- The finite normalization supplies every clause of the frontier
alteration statement, including its explicit nonempty finite locus. -/
theorem exists_alteration
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  obtain ⟨Y, a, hY, hfinite, hsurj, hreg, _, m, j, hj, hjbase⟩ :=
    exists_cover K π n ι hι hdim
  letI := hfinite
  refine ⟨Y, a, hY, inferInstance, hsurj, hreg,
    ⟨⊤, ?_, inferInstance⟩, m, j, hj, hjbase⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  exact ⟨⟨x, trivial⟩⟩

end PhilipponRegularProjectiveCurveAlteration

end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

noncomputable abbrev functionFieldAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra

noncomputable abbrev chartAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom.toAlgebra

lemma chart_functionField_tower {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    letI := functionFieldAlgebra π
    letI := chartAlgebra π U
    IsScalarTower K Γ(X, U) X.functionField := by
  letI := functionFieldAlgebra π
  letI := chartAlgebra π U
  apply IsScalarTower.of_algebraMap_eq'
  symm
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp) ≫
    X.germToFunctionField U).hom =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom
  have h : π.appLE ⊤ U (by simp) ≫ X.germToFunctionField U =
      π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
      X.presheaf.germ_res]
    rfl
  exact congrArg CommRingCat.Hom.hom
    (congrArg (fun q => (Scheme.ΓSpecIso (.of K)).inv ≫ q) h)

lemma chart_finiteType {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := chartAlgebra π U
    Algebra.FiniteType K Γ(X, U) := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)

lemma functionField_essFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    Algebra.EssFiniteType K X.functionField := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  letI := chartAlgebra π U
  letI := chart_functionField_tower π U
  letI := chart_finiteType π U hU
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp K Γ(X, U) X.functionField

/-- A finite separating transcendence basis of the actual function field. -/
theorem exists_separating_function_field_parameters
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
  letI := functionFieldAlgebra π
  letI := functionField_essFiniteType π
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K X.functionField
  have hr : Set.range ((↑) : s → X.functionField) = (s : Set X.functionField) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
    have h := hs.isAlgebraic_field
    rw [hr] at h
    exact h
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField :=
    Algebra.EssFiniteType.of_comp K _ _
  exact ⟨s, hs, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩

end PhilipponAlterationProjection

end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponAlterationProjection

abbrev residueAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma preimage_residue_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  apply ext_of_isAffine
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  have ht : (Spec.map (Scheme.ΓSpecIso (.of K)).inv).appTop =
      (Scheme.ΓSpecIso Γ(Spec (.of K), ⊤)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
    exact (Scheme.ΓSpecIso_inv_naturality (Scheme.ΓSpecIso (.of K)).inv).symm
  simp
  simp only [Scheme.Hom.appTop] at ht ⊢
  rw [ht]

lemma residue_tower {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X) :
    letI := residueAlgebra g (f x)
    letI := residueAlgebra (f ≫ g) x
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  letI := residueAlgebra g (f x)
  letI := residueAlgebra (f ≫ g) x
  letI := (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := congrArg Spec.preimage
    (congrArg (fun a => a ≫ g)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map,
    preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h


lemma dimension_eq_of_open_immersion {K : Type u} [Field K]
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (f : U ⟶ W) [IsOpenImmersion f]
    (d : W ⟶ Spec (.of K)) [LocallyOfFiniteType d] :
    topologicalKrullDim U = topologicalKrullDim W := by
  let u := genericPoint U
  let L := W.residueField (f u)
  let E := U.residueField u
  letI : Algebra K L := residueAlgebra d (f u)
  letI : Algebra K E := residueAlgebra (f ≫ d) u
  letI : Algebra L E := (f.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower f d u
  letI : IsIso (f.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion f u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  have hW := toENat_trdeg_residueField_eq_topologicalKrullDim_closure d (f u)
  have hU := toENat_trdeg_residueField_eq_topologicalKrullDim_closure (f ≫ d) u
  have hgen : f u = genericPoint W := genericPoint_eq_of_isOpenImmersion f
  have hclW : closure ({f u} : Set W) = Set.univ := by rw [hgen]; exact genericPoint_spec W
  have hclU : closure ({u} : Set U) = Set.univ := genericPoint_spec U
  have hdW : topologicalKrullDim W = topologicalKrullDim (closure ({f u} : Set W)) := by
    rw [hclW]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ W)
      (Homeomorph.Set.univ W).isHomeomorph).symm
  have hdU : topologicalKrullDim U = topologicalKrullDim (closure ({u} : Set U)) := by
    rw [hclU]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ U)
      (Homeomorph.Set.univ U).isHomeomorph).symm
  rw [hdU, hdW, ← hU, ← hW]
  change (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞)
  rw [he]

lemma dimension_eq_card_of_function_field_basis {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] (S : Finset X.functionField)
    (hS : letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
      IsTranscendenceBasis K ((↑) : S → X.functionField)) :
    topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) := by
  letI : Algebra K X.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let L := X.residueField (genericPoint X)
  letI : Algebra K L := residueAlgebra π (genericPoint X)
  letI : Algebra X.functionField L := (X.residue (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower K X.functionField L := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  have hbij : Function.Bijective (X.residue (genericPoint X)) :=
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩
  let e : X.functionField ≃ₐ[K] L :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom K X.functionField L) hbij
  have he : Algebra.trdeg K X.functionField = Algebra.trdeg K L := e.trdeg_eq
  have hd := toENat_trdeg_residueField_eq_topologicalKrullDim_closure π (genericPoint X)
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hdim : topologicalKrullDim X = topologicalKrullDim (closure ({genericPoint X} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  rw [hdim, ← hd]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) = _
  rw [← he, ← hS.cardinalMk_eq_trdeg]
  simp

end PhilipponAlterationProjection

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponFieldModelDimension
open PhilipponAlterationProjection

lemma affine_dimension_eq_fraction_trdeg
    (k A F : Type u) [Field k] [CommRing A] [IsDomain A] [Field F]
    [Algebra k A] [Algebra A F] [Algebra k F] [IsScalarTower k A F]
    [Algebra.FiniteType k A] [IsFractionRing A F] :
    topologicalKrullDim (Spec (.of A)) =
      (Cardinal.toENat (Algebra.trdeg k F) : WithBot ℕ∞) := by
  haveI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr (IsFractionRing.injective A F)
  letI : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have h := trdeg_add_eq k A (A := F)
  rw [trdeg_eq_zero (R := A) (A := F), add_zero] at h
  change topologicalKrullDim (PrimeSpectrum A) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A, h]

lemma dimension_eq_functionField_trdeg
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    topologicalKrullDim S =
      (Cardinal.toENat (Algebra.trdeg k S.functionField) : WithBot ℕ∞) := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint S ∈ (⊤ : S.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint S, hη⟩⟩
  letI := chartAlgebra π U
  letI := chart_finiteType π U hU
  letI := chart_functionField_tower π U
  letI := functionField_isFractionRing_of_isAffineOpen S U hU
  have hdim := PhilipponAlterationProjection.dimension_eq_of_open_immersion hU.fromSpec π
  exact hdim.symm.trans (affine_dimension_eq_fraction_trdeg k Γ(S, U) S.functionField)

end PhilipponFieldModelDimension

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- An integral scheme locally of finite type over any field has a
finite natural-number dimension. No perfectness assumption is needed. -/
theorem PhilipponFiniteTypeDimension.exists_nat
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    ∃ d : ℕ, topologicalKrullDim X = (d : WithBot ℕ∞) := by
  letI := PhilipponAlterationProjection.functionFieldAlgebra π
  letI := PhilipponAlterationProjection.functionField_essFiniteType π
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 k X.functionField)
  refine ⟨d, (PhilipponFieldModelDimension.dimension_eq_functionField_trdeg k π).trans ?_⟩
  rw [hd]
  simp

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlgebraicallyClosedAlterationReduction

/-- The unresolved normal, higher-dimensional projective construction
over one field. This is a property, not a proof of that construction. -/
abbrev NormalCase (L : Type u) [Field L] : Prop :=
  ∀ {T : Scheme.{u}} [IsIntegral T] (σ : T ⟶ Spec (.of L))
    (m : ℕ) (j : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) L))
    [IsClosedImmersion j], j ≫ ProjSpace.π L m = σ →
    (∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) →
    1 < topologicalKrullDim T →
    ∃ (Y : Scheme.{u}) (a : Y ⟶ T),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : T.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (r : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) L)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π L r = a ≫ σ

/-- The supplied normal-target construction over an algebraically closed
extension gives an actual smooth integral projective cover dominating
the original target, with the dimension bound needed for finite descent. -/
theorem exists_geometric_cover
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    [IsAlgClosed L] (H : NormalCase L)
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of k))
    (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π k n = π) :
    ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (.of L)) (φ : Y ⟶ X),
      IsIntegral Y ∧ Smooth σ ∧ Surjective φ ∧
      φ ≫ π = σ ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
      topologicalKrullDim Y ≤ topologicalKrullDim X ∧
      ∃ (m : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) L)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π L m = σ := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  obtain ⟨C, c, σC, hC, hc, hsurjC, hdC, hcbase, e, he, hebase⟩ :=
    PhilipponIntegralAlgebraicBaseChange.exists_integral_projective_dominating k L π n j hj
  letI := hC
  letI := he
  haveI : IsProper σC := by rw [← hebase]; infer_instance
  let fC := c ≫ pullback.fst π b
  letI : Surjective fC := hsurjC
  have hoverC : fC ≫ π = σC ≫ b := by
    dsimp only [fC]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hcbase]
  have hA : ∃ (Y : Scheme.{u}) (q : Y ⟶ C),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : C.Opens, Nonempty V ∧ IsFinite (q ∣_ V)) ∧
      ∃ (m : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) L)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π L m = q ≫ σC := by
    by_cases hdim : topologicalKrullDim C ≤ 1
    · exact PhilipponRegularProjectiveCurveAlteration.exists_alteration L σC n e hebase hdim
    · exact PhilipponRegularAlterationNormalization.exists_of_normal_case L H
        σC n e hebase (lt_of_not_ge hdim)
  obtain ⟨Y, q, hY, hproperq, hsurjq, hreg, ⟨V, hV, hVfinite⟩,
    m, i, hi, hibase⟩ := hA
  letI := hY
  letI := hproperq
  letI := hsurjq
  letI := hV
  letI := hVfinite
  letI := hi
  let σ := q ≫ σC
  haveI : Smooth σ := AlgebraicGeometry.smooth_of_regular_stalks_over_perfect_field L σ hreg
  refine ⟨Y, σ, q ≫ fC, hY, inferInstance, inferInstance, ?_, ?_,
    m, i, hi, hibase⟩
  · rw [Category.assoc, hoverC, ← Category.assoc]
  · exact (PhilipponProperGenericFiniteness.dimension_le_of_finite_open L σC q V).trans hdC

/-- Algebraically closed normal projective higher-dimensional targets
suffice for the full projective alteration theorem over arbitrary fields.
The construction hypothesis is explicit and remains unresolved. -/
theorem exists_arbitrary_field_of_normal_cases
    (H : ∀ (L : Type u) [Field L] [IsAlgClosed L], NormalCase L)
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of k))
    (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π k n = π) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ Surjective a ∧
      (∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) ∧
      (∃ W : X.Opens, Nonempty W ∧ IsFinite (a ∣_ W)) ∧
      ∃ (m : ℕ) (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π k m = a ≫ π := by
  haveI : IsProper π := by rw [← hj]; infer_instance
  obtain ⟨d, hdX⟩ := PhilipponFiniteTypeDimension.exists_nat k π
  obtain ⟨Y, σ, φ, hY, hsmooth, hsurj, hover, hdY, m, i, hi, hibase⟩ :=
    exists_geometric_cover k (AlgebraicClosure k) (H (AlgebraicClosure k)) π n j hj
  letI := hY
  letI := hsmooth
  letI := hsurj
  letI := hi
  exact PhilipponAlgebraicAlterationDescent.exists_alteration k (AlgebraicClosure k)
    π d hdX σ m i hibase φ hover hdY

end PhilipponAlgebraicallyClosedAlterationReduction

end
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  apply PhilipponAlgebraicallyClosedAlterationReduction.exists_arbitrary_field_of_normal_cases
    ?_ K π n ι hι
  intro L hL hAlgClosed
  intro T hT σ m j hj hjbase hnormalT hdimT
  exact AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_over_algClosed
    L σ m j hjbase hnormalT hdimT

end
end

#print axioms PhilipponProjectiveFieldDescent.fieldMap_comp
#print axioms PhilipponProjectiveFieldDescent.exists_projective_relative_finite_model
#print axioms PhilipponFieldModelProperties.fpqc_fieldMap
#print axioms PhilipponFieldModelProperties.smooth_of_isPullback_field
#print axioms PhilipponFieldModelProperties.proper_of_isPullback_field
#print axioms PhilipponFieldModelIntegral.isReduced_of_flat_surjective
#print axioms PhilipponFieldModelIntegral.isIntegral_of_flat_surjective
#print axioms PhilipponFieldModelIntegral.geometricallyConnected_of_geometricallyIntegral
#print axioms PhilipponIntegralDimension.dimension_le_of_integral
#print axioms PhilipponIntegralDimension.dimension_le_algebraic_baseChange
#print axioms PhilipponFaithfullyFlatDimension.ring_dimension_le_of_faithfullyFlat
#print axioms PhilipponFaithfullyFlatDimension.dimension_le_of_flat_surjective
#print axioms PhilipponGenericDominance.genericFiber_inclusion
#print axioms PhilipponGenericDominance.of_recovered_generic_cover
#print axioms PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber
#print axioms PhilipponAlterationDimensionControl.finite_of_dimension_le_zero
#print axioms PhilipponAlterationDimensionControl.dimension_nonneg
#print axioms PhilipponAlterationDimensionControl.eq_one_of_nat_add_eq
#print axioms PhilipponAlterationDimensionControl.eq_zero_of_nat_add_eq
#print axioms PhilipponAlterationDimensionControl.dimension_eq_and_genericFiber_dimensions
#print axioms PhilipponProperGenericFiniteness.finite_genericFiber_of_finite_open
#print axioms PhilipponProperGenericFiniteness.exists_finite_open_of_finite_genericFiber
#print axioms PhilipponProperGenericFiniteness.exists_finite_open_of_dimension_le
#print axioms PhilipponProperGenericFiniteness.dimension_le_of_finite_open
#print axioms P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.etaleRegularAt
#print axioms PhilipponMultiplicity.AlgebraicGroupCM.regularAt_of_standardSmooth
#print axioms PhilipponMultiplicity.AlgebraicGroupCM.regularAt_of_smoothAt
#print axioms PhilipponSmoothSchemeRegular.stalk
#print axioms PhilipponFiniteFieldProjectiveEmbedding.exists_embedding
#print axioms PhilipponAlgebraicAlterationDescent.exists_alteration
#print axioms PhilipponReducedClosedSubscheme.isReduced_iff_radical_eq
#print axioms PhilipponReducedClosedSubscheme.integral_of_prime_top
#print axioms PhilipponReducedClosedSubscheme.radical_comap_open
#print axioms PhilipponReducedClosedSubscheme.eq_of_reduced_support
#print axioms PhilipponSchemeImageIntegral.ker_radical
#print axioms PhilipponSchemeImageIntegral.image_isReduced
#print axioms PhilipponSchemeImageIntegral.image_isIntegral
#print axioms PhilipponIntegralAlgebraicBaseChange.exists_integral_closed_dominating
#print axioms PhilipponIntegralAlgebraicBaseChange.exists_integral_projective_dominating
#print axioms PhilipponProperOpenCompactification.isIso
#print axioms PhilipponAlterationOpenRestriction.finite_restrict_pullback
#print axioms PhilipponAlterationOpenRestriction.exists_of_compactification
#print axioms PhilipponBirationalAlterationComposition.isIso_restrict_of_open_section
#print axioms PhilipponBirationalAlterationComposition.finite_restrict_image
#print axioms PhilipponBirationalAlterationComposition.finite_open_comp
#print axioms PhilipponFiniteAlterationComposition.preimage_genericPoint
#print axioms PhilipponFiniteAlterationComposition.exists_open_preimage_le
#print axioms PhilipponFiniteAlterationComposition.finite_restrict_of_le
#print axioms PhilipponFiniteAlterationComposition.finite_open_comp
#print axioms PhilipponRegularAlterationNormalization.exists_of_normal_case
#print axioms PhilipponRegularProjectiveCurveAlteration.regularLocalRing_of_integrallyClosed_of_dimension_le_one
#print axioms PhilipponRegularProjectiveCurveAlteration.stalk_dimension_le_topological
#print axioms PhilipponRegularProjectiveCurveAlteration.exists_cover
#print axioms PhilipponRegularProjectiveCurveAlteration.exists_alteration
#print axioms PhilipponAlterationProjection.functionField_essFiniteType
#print axioms PhilipponAlterationProjection.exists_separating_function_field_parameters
#print axioms PhilipponAlterationProjection.residue_tower
#print axioms PhilipponFieldModelDimension.affine_dimension_eq_fraction_trdeg
#print axioms PhilipponFieldModelDimension.dimension_eq_functionField_trdeg
#print axioms PhilipponFiniteTypeDimension.exists_nat
#print axioms PhilipponAlgebraicallyClosedAlterationReduction.exists_geometric_cover
#print axioms PhilipponAlgebraicallyClosedAlterationReduction.exists_arbitrary_field_of_normal_cases
#print axioms solution
