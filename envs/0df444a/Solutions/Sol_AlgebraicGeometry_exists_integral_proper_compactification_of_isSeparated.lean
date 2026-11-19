-- Prove2me | solution 1 for AlgebraicGeometry.exists_integral_proper_compactification_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T14:29:33.491823+00:00
-- url     : https://prove2.me/submissions/b9c62383-356c-4f73-a1e3-fc2de5739bb2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_proper_compactification_sup_of_isAffineOpen

universe u

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PhilipponCompactification

/-- A compactification retains the actual source and its original map. -/
structure Data {X S : Scheme.{u}} (π : X ⟶ S) where
  C : Scheme.{u}
  πC : C ⟶ S
  proper : IsProper πC
  i : X ⟶ C
  openImmersion : IsOpenImmersion i
  fac : i ≫ πC = π

attribute [instance] Data.proper Data.openImmersion

def Compactifiable {X S : Scheme.{u}} (π : X ⟶ S) : Prop := Nonempty (Data π)

/-- An open subscheme retains the same proper ambient scheme. -/
def Data.restrict {X U S : Scheme.{u}} {π : X ⟶ S} (d : Data π)
    (j : U ⟶ X) [IsOpenImmersion j] : Data (j ≫ π) where
  C := d.C
  πC := d.πC
  proper := inferInstance
  i := j ≫ d.i
  openImmersion := inferInstance
  fac := by rw [Category.assoc, d.fac]

theorem Compactifiable.restrict {X U S : Scheme.{u}} {π : X ⟶ S}
    (h : Compactifiable π) (j : U ⟶ X) [IsOpenImmersion j] : Compactifiable (j ≫ π) := by
  obtain ⟨d⟩ := h
  exact ⟨d.restrict j⟩

/-- A proper source itself supplies its compactification. -/
def Data.ofProper {X S : Scheme.{u}} (π : X ⟶ S) [IsProper π] : Data π where
  C := X
  πC := π
  proper := inferInstance
  i := 𝟙 X
  openImmersion := inferInstance
  fac := Category.id_comp π

end PhilipponCompactification

end
end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection.ProjectiveAffineChart
variable (R : Type u) [CommRing R] (n : ℕ)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
abbrev chartRing := Away (grading R n) (MvPolynomial.X (0 : Fin (n + 1)))

noncomputable def specialize :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

lemma specialize_X_zero : specialize R n (MvPolynomial.X (0 : Fin (n + 1))) = 1 := by
  simp [specialize]

lemma specialize_unit : IsUnit (specialize R n (MvPolynomial.X (0 : Fin (n + 1)))) :=
  isUnit_iff_exists_inv.mpr ⟨1, by rw [specialize_X_zero]; simp⟩

noncomputable def fromAway : chartRing R n →+* MvPolynomial (Fin n) R :=
  (Localization.awayLift (specialize R n) (MvPolynomial.X (0 : Fin (n + 1)))
    (specialize_unit R n)).comp
    (algebraMap (chartRing R n) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) :
      MvPolynomial (Fin (n + 1)) R)))

lemma fromAway_coeff (r : R) :
    fromAway R n (algebraMap R (chartRing R n) r) = MvPolynomial.C r := by
  change Localization.awayLift (specialize R n) _ (specialize_unit R n)
    ((algebraMap R (chartRing R n) r).val) = _
  rw [ProjSpace.val_algebraMap]
  simp only [Localization.awayLift, IsLocalization.Away.lift_eq]
  simp [specialize]

lemma fromAway_ratio (j : Fin (n + 1)) :
    fromAway R n (ProjSpace.ratio R n 0 j) = specialize R n (MvPolynomial.X j) := by
  change Localization.awayLift (specialize R n) _ (specialize_unit R n) (ProjSpace.ratio R n 0 j).val = _
  rw [ProjSpace.ratio, Away.val_mk]
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (specialize R n) (MvPolynomial.X (0 : Fin (n + 1)))
      (MvPolynomial.X j) 1 (by rw [specialize_X_zero]; simp) 1

noncomputable def fromAwayAlg : chartRing R n →ₐ[R] MvPolynomial (Fin n) R where
  __ := fromAway R n
  commutes' := fromAway_coeff R n

lemma fromAwayAlg_apply (x : chartRing R n) : fromAwayAlg R n x = fromAway R n x := rfl

noncomputable def toAwayAlg : MvPolynomial (Fin n) R →ₐ[R] chartRing R n :=
  MvPolynomial.aeval (fun j : Fin n => ProjSpace.ratio R n 0 j.succ)

lemma toAwayAlg_X (j : Fin n) : toAwayAlg R n (MvPolynomial.X j) = ProjSpace.ratio R n 0 j.succ :=
  MvPolynomial.aeval_X _ _

lemma from_to : (fromAwayAlg R n).comp (toAwayAlg R n) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, toAwayAlg_X, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  simp [specialize]

lemma to_from : (toAwayAlg R n).comp (fromAwayAlg R n) = AlgHom.id R _ := by
  apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R n 0)
  rintro _ ⟨j, rfl⟩
  simp only [AlgHom.comp_apply, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [specialize, ProjSpace.ratio_self]
  · simp [specialize, toAwayAlg]

noncomputable def equiv : chartRing R n ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (fromAwayAlg R n) (toAwayAlg R n) (from_to R n) (to_from R n)

/-- The standard affine-space chart in projective space. -/
noncomputable def embedding : Spec (.of (MvPolynomial (Fin n) R)) ⟶ Proj (grading R n) :=
  Spec.map (CommRingCat.ofHom (equiv R n).toRingEquiv.toRingHom) ≫
    Proj.awayι (grading R n) (MvPolynomial.X (0 : Fin (n + 1)))
      (ProjSpace.X_mem_one R n 0) one_pos

instance embedding_isOpenImmersion : IsOpenImmersion (embedding R n) := by
  haveI : IsIso (CommRingCat.ofHom (equiv R n).toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (equiv R n).bijective
  unfold embedding
  infer_instance

lemma embedding_over : embedding R n ≫ ProjSpace.π R n =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) := by
  rw [embedding, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (equiv R n).commutes r

end PhilipponAlterationProjection.ProjectiveAffineChart

end

section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAffineProjectiveCompactification

lemma exists_affine_immersion
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (j : Spec (.of A) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)),
      IsImmersion j ∧ j ≫ ProjSpace.π k n =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  haveI : IsClosedImmersion f := IsClosedImmersion.spec_of_surjective _ hφ
  let j := f ≫ PhilipponAlterationProjection.ProjectiveAffineChart.embedding k n
  refine ⟨n, j, inferInstance, ?_⟩
  dsimp only [j]
  rw [Category.assoc, PhilipponAlterationProjection.ProjectiveAffineChart.embedding_over]
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact φ.commutes r

end PhilipponAffineProjectiveCompactification
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite


namespace PhilipponCoefficientIdeal

variable {A : CommRingCat.{u}} {X Y : Scheme.{u}}

def coefficient (g : X ⟶ Spec A) : A ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso A).inv ≫ g.appTop

theorem coefficient_factor (g : X ⟶ Spec A) :
    X.toSpecΓ ≫ Spec.map (coefficient g) = g := by
  rw [coefficient, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem coefficient_germ (g : X ⟶ Spec A) (x : X) :
    coefficient g ≫ X.presheaf.germ ⊤ x trivial = Spec.preimage (X.fromSpecStalk x ≫ g) := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, ← Scheme.fromSpecStalk_toSpecΓ,
    Category.assoc, coefficient_factor]

theorem coefficient_comp (f : Y ⟶ X) (g : X ⟶ Spec A) :
    coefficient g ≫ f.appTop = coefficient (f ≫ g) := by
  simp only [coefficient, Scheme.Hom.comp_appTop, Category.assoc]

def ideal (g : X ⟶ Spec A) (J : Ideal A) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (coefficient g).hom)

theorem ideal_stalk (g : X ⟶ Spec A) (J : Ideal A)
    (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ U x hx).hom ((ideal g J).ideal U) =
      Ideal.map (Spec.preimage (X.fromSpecStalk x ≫ g)).hom J := by
  rw [ideal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, Ideal.map_map]
  change Ideal.map ((coefficient g ≫ X.presheaf.map (homOfLE le_top).op ≫
    X.presheaf.germ U x hx).hom) J = _
  rw [X.presheaf.germ_res', coefficient_germ]

end PhilipponCoefficientIdeal

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

namespace PhilipponCompactification

/-- Every actual finite-type affine scheme over a field admits a
projective immersion with exactly its original structure map. -/
theorem affine_immersion (K : Type u) [Field K] {X : Scheme.{u}} [IsAffine X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    ∃ (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K)),
      IsImmersion j ∧ j ≫ ProjSpace.π K n = π := by
  let φ := PhilipponCoefficientIdeal.coefficient π
  letI : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have hπ : π.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (@LocallyOfFiniteType) π inferInstance
  have hφ : φ.hom.FiniteType := hπ.comp
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of K)).inv).2)
  letI : Algebra.FiniteType K Γ(X, ⊤) := hφ
  obtain ⟨n, f, hf, hfbase⟩ :=
    PhilipponAffineProjectiveCompactification.exists_affine_immersion K Γ(X, ⊤)
  letI := hf
  refine ⟨n, X.isoSpec.hom ≫ f, inferInstance, ?_⟩
  rw [Category.assoc, hfbase]
  exact PhilipponCoefficientIdeal.coefficient_factor π

/-- Taking the actual scheme-theoretic image in projective space
compactifies every finite-type affine scheme. Nilpotents and empty
schemes are allowed; neither reducedness nor integrality is assumed. -/
theorem affine (K : Type u) [Field K] {X : Scheme.{u}} [IsAffine X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] : Compactifiable π := by
  obtain ⟨n, j, hj, hjbase⟩ := affine_immersion K π
  letI := hj
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  haveI : QuasiCompact j := inferInstance
  exact ⟨{
    C := j.image
    πC := j.imageι ≫ ProjSpace.π K n
    proper := inferInstance
    i := j.toImage
    openImmersion := inferInstance
    fac := by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hjbase] }⟩

end PhilipponCompactification

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
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponCompactification

/-- Taking the scheme-theoretic image retains the actual source open
and makes a compactification integral whenever its source is integral. -/
def Data.integralReduction {X S : Scheme.{u}} [IsIntegral X] {π : X ⟶ S}
    (d : Data π) [QuasiCompact d.i] : Data π where
  C := d.i.image
  πC := d.i.imageι ≫ d.πC
  proper := inferInstance
  i := d.i.toImage
  openImmersion := inferInstance
  fac := by rw [← Category.assoc, Scheme.Hom.toImage_imageι, d.fac]

instance Data.integralReduction_isIntegral {X S : Scheme.{u}} [IsIntegral X] {π : X ⟶ S}
    (d : Data π) [QuasiCompact d.i] : IsIntegral d.integralReduction.C :=
  PhilipponSchemeImageIntegral.image_isIntegral d.i

instance Data.integralReduction_isDominant {X S : Scheme.{u}} [IsIntegral X] {π : X ⟶ S}
    (d : Data π) [QuasiCompact d.i] : IsDominant d.integralReduction.i :=
  inferInstanceAs (IsDominant d.i.toImage)

/-- This is exactly the integral conclusion of the current Nagata leaf,
once compactifiability of the original finite-type map is established. -/
theorem exists_integral_of_compactifiable
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π]
    (h : Compactifiable π) :
    ∃ (C : Scheme.{u}) (πC : C ⟶ Spec (.of K)),
      IsIntegral C ∧ IsProper πC ∧
      ∃ j : X ⟶ C, IsOpenImmersion j ∧ IsDominant j ∧ j ≫ πC = π := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨d⟩ := h
  haveI : QuasiCompact d.i := inferInstance
  let e := d.integralReduction
  exact ⟨e.C, e.πC, inferInstance, inferInstance,
    e.i, inferInstance, inferInstance, e.fac⟩

end PhilipponCompactification

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponCompactification

/-- In the finite-cover induction the new open can always be taken affine.
Only a nonempty previously compactified union needs a gluing step. -/
theorem of_affine_step (K : Type u) [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π]
    (step : ∀ U V : X.Opens, Nonempty U → Nonempty V → IsAffineOpen V →
      Compactifiable (U.ι ≫ π) → Compactifiable ((U ⊔ V).ι ≫ π)) :
    Compactifiable π := by
  classical
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  let 𝒰 := X.affineCover.finiteSubcover
  let A : 𝒰.I₀ → X.Opens := fun i => (𝒰.f i).opensRange
  let P : X.Opens → Prop := fun U => Compactifiable (U.ι ≫ π)
  have hA (i : 𝒰.I₀) : IsAffineOpen (A i) := by
    letI : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (X.affineCover.X _))
    exact isAffineOpen_opensRange (𝒰.f i)
  have ha (V : X.Opens) (hV : IsAffineOpen V) : P V := by
    letI : IsAffine V.toScheme := hV
    exact affine K (V.ι ≫ π)
  have he : P ⊥ := ha ⊥ (isAffineOpen_bot X)
  have empty_eq_bot (V : X.Opens) (h : IsEmpty V) : V = ⊥ := by
    ext x
    exact iff_false_intro (fun hx => h.false (⟨x, hx⟩ : V))
  have add (U V : X.Opens) (hV : IsAffineOpen V) (hU : P U) : P (U ⊔ V) := by
    rcases isEmpty_or_nonempty U with h | h
    · rw [empty_eq_bot U h, bot_sup_eq]
      exact ha V hV
    rcases isEmpty_or_nonempty V with h' | h'
    · rwa [empty_eq_bot V h', sup_bot_eq]
    exact step U V h h' hV hU
  have hfin (s : Finset 𝒰.I₀) : P (s.sup A) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using he
    | @insert i s his ih =>
      simpa only [Finset.sup_insert, sup_comm] using add (s.sup A) (A i) (hA i) ih
  have htop : (Finset.univ : Finset 𝒰.I₀).sup A = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    rw [Finset.sup_eq_iSup]
    exact Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨Finset.mem_univ i, ⟨y, hy⟩⟩⟩
  have ht : P ⊤ := (congrArg P htop).mp (hfin Finset.univ)
  have hh := (show Compactifiable ((⊤ : X.Opens).ι ≫ π) from ht).restrict X.topIso.inv
  change Compactifiable ((X.topIso.inv ≫ X.topIso.hom) ≫ π) at hh
  simpa only [Iso.inv_hom_id, Category.id_comp] using hh

end PhilipponCompactification

end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem PhilipponCompactification.integral_of_affine_attachment
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π]
    (step : ∀ U V : X.Opens, Nonempty U → Nonempty V → IsAffineOpen V →
      ∀ (C : Scheme.{u}) (q : C ⟶ Spec (.of K)) (_ : IsProper q)
        (j : U.toScheme ⟶ C) (_ : IsOpenImmersion j), j ≫ q = U.ι ≫ π →
        ∃ (D : Scheme.{u}) (p : D ⟶ Spec (.of K)) (i : (U ⊔ V).toScheme ⟶ D),
          IsProper p ∧ IsOpenImmersion i ∧ i ≫ p = (U ⊔ V).ι ≫ π) :
    ∃ (C : Scheme.{u}) (πC : C ⟶ Spec (.of K)),
      IsIntegral C ∧ IsProper πC ∧
      ∃ j : X ⟶ C, IsOpenImmersion j ∧ IsDominant j ∧ j ≫ πC = π := by
  apply PhilipponCompactification.exists_integral_of_compactifiable K π
  apply PhilipponCompactification.of_affine_step K π
  intro U V hU hV hAff h
  obtain ⟨c⟩ := h
  obtain ⟨D, p, i, hp, hi, hpi⟩ := step U V hU hV hAff c.C c.πC c.proper c.i c.openImmersion c.fac
  exact ⟨⟨D, p, hp, i, hi, hpi⟩⟩

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π] :
    ∃ (C : Scheme.{u}) (πC : C ⟶ Spec (.of K)),
      IsIntegral C ∧ IsProper πC ∧
      ∃ j : X ⟶ C, IsOpenImmersion j ∧ IsDominant j ∧ j ≫ πC = π := by
  apply PhilipponCompactification.integral_of_affine_attachment K π
  intro U V hU hV hAff C q hq j hj hjq
  letI := hq
  letI := hj
  exact AlgebraicGeometry.exists_proper_compactification_sup_of_isAffineOpen K π U V hU hV hAff C q j hjq

#print axioms PhilipponCompactification.Data.restrict
#print axioms PhilipponCompactification.Compactifiable.restrict
#print axioms PhilipponAlterationProjection.ProjectiveAffineChart.equiv
#print axioms PhilipponAlterationProjection.ProjectiveAffineChart.embedding_isOpenImmersion
#print axioms PhilipponAlterationProjection.ProjectiveAffineChart.embedding_over
#print axioms PhilipponAffineProjectiveCompactification.exists_affine_immersion
#print axioms PhilipponCoefficientIdeal.coefficient_germ
#print axioms PhilipponCoefficientIdeal.coefficient_comp
#print axioms PhilipponCoefficientIdeal.ideal_stalk
#print axioms PhilipponCompactification.affine_immersion
#print axioms PhilipponCompactification.affine
#print axioms PhilipponReducedClosedSubscheme.isReduced_iff_radical_eq
#print axioms PhilipponReducedClosedSubscheme.integral_of_prime_top
#print axioms PhilipponReducedClosedSubscheme.radical_comap_open
#print axioms PhilipponReducedClosedSubscheme.eq_of_reduced_support
#print axioms PhilipponSchemeImageIntegral.ker_radical
#print axioms PhilipponSchemeImageIntegral.image_isReduced
#print axioms PhilipponSchemeImageIntegral.image_isIntegral
#print axioms PhilipponCompactification.Data.integralReduction
#print axioms PhilipponCompactification.Data.integralReduction_isIntegral
#print axioms PhilipponCompactification.exists_integral_of_compactifiable
#print axioms PhilipponCompactification.of_affine_step
#print axioms PhilipponCompactification.integral_of_affine_attachment
#print axioms solution
