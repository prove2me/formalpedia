-- Prove2me | solution 1 for AlgebraicGeometry.exists_finite_extension_smooth_projective_cover_of_scalarExtension_of_proper_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T19:15:51.129324+00:00
-- url     : https://prove2.me/submissions/90ca08af-d6c9-48fe-922b-1b93adccd248

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat

universe u
set_option linter.style.haveILetI false


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


end PhilipponFieldModelProperties


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericMorphismSpread

/-- Canonical comparison of two pullbacks with compatible base maps. -/
def changeBase {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    pullback f a ⟶ pullback f b :=
  pullback.lift (pullback.fst f a) (pullback.snd f a ≫ c)
    (by rw [Category.assoc, hc]; exact pullback.condition)

@[reassoc (attr := simp)] lemma changeBase_fst {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.fst f b = pullback.fst f a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma changeBase_snd {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.snd f b = pullback.snd f a ≫ c :=
  pullback.lift_snd _ _ _


end PhilipponGenericMorphismSpread

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponProperCoverSpread

lemma changeBase_isPullback {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    IsPullback (changeBase f a b c hc) (pullback.snd f a) (pullback.snd f b) c := by
  refine IsPullback.of_right ?_ (changeBase_snd _ _ _ _ _) (IsPullback.of_hasPullback f b)
  rw [changeBase_fst, hc]
  exact IsPullback.of_hasPullback f a


end PhilipponProperCoverSpread


set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open PhilipponGenericMorphismSpread

namespace PhilipponFiniteScalarCurveCover

/-- Smooth projective covers of proper curves descend to finite intermediate fields,
with their actual morphism, embedding and dimension bound retained. -/
theorem exists_finite_smooth_projective_scalar_cover
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p ∧
          ∃ a : Y ⟶ pullback π (Spec.map (CommRingCat.ofHom (algebraMap k E))),
            a ≫ pullback.fst π _ = f ∧ a ≫ pullback.snd π _ = p ∧
            IsProper a ∧ Surjective a := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := (PhilipponFieldModelProperties.fpqc_fieldMap k K).1.1
  obtain ⟨Z, a, ha, hsurj, hsmooth, hdZ, n, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
      k K π hdim
  letI := ha
  letI := hsurj
  letI := hj
  let pZ : Z ⟶ Spec (.of K) := a ≫ pullback.snd π b
  haveI : IsProper pZ := inferInstance
  letI : Smooth pZ := hsmooth
  letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace π
  letI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated π
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace pZ
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated pZ
  let φ : Z ⟶ C := a ≫ pullback.fst π b
  have hφ : φ ≫ π = pZ ≫ b := by
    simp only [φ, pZ, Category.assoc, pullback.condition]
  haveI : Surjective φ := inferInstance
  obtain ⟨E, hE, Y, p, g, f, j₀, hpb, hj₀, hj₀base, hover, hrec⟩ :=
    PhilipponProjectiveFieldDescent.exists_projective_relative_finite_model
      k K C π Z pZ n j hjbase φ hφ
  letI := hE
  letI := hj₀
  have hp : IsProper p := by rw [← hj₀base]; infer_instance
  letI := hp
  have hs : Smooth p := PhilipponFieldModelProperties.smooth_of_isPullback_field
    E K p pZ g hpb hsmooth
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    MorphismProperty.of_isPullback hpb.flip (PhilipponFieldModelProperties.fpqc_fieldMap E K)
  letI : Surjective g := hfpqc.1.1
  letI : Flat g := hfpqc.1.2
  have hdY : topologicalKrullDim Y ≤ 1 :=
    (PhilipponFaithfullyFlatDimension.dimension_le_of_flat_surjective g).trans hdZ
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsProper (f ≫ π) := by rw [hover]; infer_instance
  have hf : IsProper f := IsProper.of_comp f π
  have hsf : Surjective f := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := (inferInstance : Surjective φ).surj x
    refine ⟨g z, ?_⟩
    change (g ≫ f) z = x
    rw [hrec]
    exact hz
  let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let d := Spec.map (CommRingCat.ofHom (algebraMap E K))
  have hd : d ≫ bE = b := PhilipponProjectiveFieldDescent.fieldMap_comp k K E
  let v := changeBase π b bE d hd
  have hpv := PhilipponProperCoverSpread.changeBase_isPullback π b bE d hd
  haveI : Surjective d := (PhilipponFieldModelProperties.fpqc_fieldMap E K).1.1
  haveI : Surjective v := MorphismProperty.of_isPullback hpv.flip inferInstance
  let α := pullback.lift f p hover
  have hαf : α ≫ pullback.fst π bE = f := pullback.lift_fst _ _ _
  have hαp : α ≫ pullback.snd π bE = p := pullback.lift_snd _ _ _
  have hga : g ≫ α = a ≫ v := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαf, Category.assoc, changeBase_fst]
      exact hrec
    · rw [Category.assoc, hαp, Category.assoc, changeBase_snd, ← Category.assoc]
      exact hpb.w
  have hsurα : Surjective α := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := (inferInstance : Surjective (a ≫ v)).surj x
    refine ⟨g z, ?_⟩
    change (g ≫ α) z = x
    rw [hga]
    exact hz
  haveI : IsProper (α ≫ pullback.snd π bE) := by rw [hαp]; exact hp
  have hproperα : IsProper α := IsProper.of_comp α (pullback.snd π bE)
  exact ⟨E, hE, Y, f, p, hf, hsf, hs, hp, hdY, hover, n, j₀, hj₀, hj₀base,
    α, hαf, hαp, hproperα, hsurα⟩

end PhilipponFiniteScalarCurveCover


theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p ∧
          ∃ a : Y ⟶ pullback π (Spec.map (CommRingCat.ofHom (algebraMap k E))),
            a ≫ pullback.fst π _ = f ∧ a ≫ pullback.snd π _ = p ∧
            IsProper a ∧ Surjective a := by
  exact PhilipponFiniteScalarCurveCover.exists_finite_smooth_projective_scalar_cover k K π hdim
