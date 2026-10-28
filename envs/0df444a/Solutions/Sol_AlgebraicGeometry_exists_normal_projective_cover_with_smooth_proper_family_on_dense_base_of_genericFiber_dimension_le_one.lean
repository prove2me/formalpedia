-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_cover_with_smooth_proper_family_on_dense_base_of_genericFiber_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T23:20:51.598379+00:00
-- url     : https://prove2.me/submissions/95dc0063-fbbc-4fb7-b056-42d5c26f7083

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_PhilipponMultiplicity_GenericCurveCoverFamily
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
import Theorems.Thm_AlgebraicGeometry_hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber

universe u
noncomputable section


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

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponAbsoluteSmoothOpen

/-- A smooth proper family over a reduced finite-type base over a perfect
field has dense base and source opens smooth over that field. -/
lemma exists_dense_absolute_smooth_open
    (k : Type u) [Field k] [PerfectField k]
    {S Y : Scheme.{u}} [IsReduced S]
    (c : S ⟶ Spec (.of k)) [LocallyOfFinitePresentation c]
    (p : Y ⟶ S) [Smooth p] [IsProper p] :
    ∃ V : S.Opens, Dense (V : Set S) ∧ Dense ((p ⁻¹ᵁ V) : Set Y) ∧
      Smooth (V.ι ≫ c) ∧ Smooth ((p ⁻¹ᵁ V).ι ≫ p ≫ c) ∧
      Smooth (p ∣_ V) ∧ IsProper (p ∣_ V) := by
  let V := c.smoothLocus
  have hV : Dense (V : Set S) := c.dense_smoothLocus_of_perfectField
  have hpre : Dense ((p ⁻¹ᵁ V) : Set Y) := hV.preimage p.isOpenMap
  have hsmV : Smooth (V.ι ≫ c) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact x.property
  haveI : Smooth (V.ι ≫ c) := hsmV
  have H : Smooth ((p ∣_ V) ≫ (V.ι ≫ c)) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at H
  exact ⟨V, hV, hpre, hsmV, H, inferInstance, inferInstance⟩

end PhilipponAbsoluteSmoothOpen

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponRelativeProjectiveImmersion

/-- An immersion into relative projective space over an affine finite-type
algebra has an absolute projective immersion with the same structure map. -/
lemma exists_absolute_projective_immersion
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    [IsImmersion j] :
    ∃ (d : ℕ) (ι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
      IsImmersion ι ∧ ι ≫ ProjSpace.π k d =
        j ≫ ProjSpace.π A n ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨m, a, ha, hbase⟩ := PhilipponAffineProjectiveCompactification.exists_affine_immersion k A
  haveI : IsImmersion a := ha
  let pb := ProjSpace.isPullback_map k A n
  have hw : ProjSpace.map k A n ≫ ProjSpace.π k n =
      (ProjSpace.π A n ≫ a) ≫ ProjSpace.π k m := by
    rw [Category.assoc, hbase]
    exact pb.w
  let v := pullback.lift (ProjSpace.map k A n) (ProjSpace.π A n ≫ a) hw
  have hpv : IsPullback v (ProjSpace.π A n)
      (pullback.snd (ProjSpace.π k n) (ProjSpace.π k m)) a := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, hbase]
    exact pb
  haveI : IsImmersion v := MorphismProperty.of_isPullback hpv.flip ha
  obtain ⟨d, l, _hd, hl, hlbase⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      (ProjSpace.π k n) (ProjSpace.π k m)
      n (𝟙 _) inferInstance (Category.id_comp _)
      m (𝟙 _) inferInstance (Category.id_comp _)
  haveI : IsClosedImmersion l := hl
  refine ⟨d, j ≫ v ≫ l, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, hlbase,
    ← Category.assoc v, pullback.lift_fst, pb.w]

end PhilipponRelativeProjectiveImmersion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponGlobalFamilyModel

/-- Complete a relative projective family without carrying the generic-field
presentation through the geometric construction. -/
lemma exists_model_of_relative_projective_family
    (k A : Type u) [Field k] [PerfectField k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {S X N U Y M : Scheme.{u}} [IsIntegral S] [IsIntegral X] [IsIntegral N] [IsIntegral U]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) (hqπ : q ≫ πS = πX)
    (qN : N ⟶ S) [IsProper qN] [Surjective qN]
    (hnN : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x))
    (hdN : topologicalKrullDim N = topologicalKrullDim S)
    (nN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nN + 1)) k))
    [IsClosedImmersion iN] (hbaseN : iN ≫ ProjSpace.π k nN = qN ≫ πS)
    (u : U ⟶ N) [IsOpenImmersion u] [IsDominant u]
    (pY : Y ⟶ U) [Smooth pY] [IsProper pY]
    (nM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) A))
    [IsClosedImmersion iM] (tY : Y ⟶ M) [IsOpenImmersion tY]
    (j : U ⟶ Spec (.of A))
    (hpYeq : tY ≫ iM ≫ ProjSpace.π A nM = pY ≫ j)
    (hjbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = u ≫ qN ≫ πS)
    (aY : Y ⟶ X) [IsDominant aY] (hqa : aY ≫ q = pY ≫ u ≫ qN) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  let πN := qN ≫ πS
  have hN : IsIntegral N := inferInstance
  have hqN : IsProper qN := inferInstance
  have hsqN : Surjective qN := inferInstance
  have hiN : IsClosedImmersion iN := inferInstance
  haveI : IsProper πN := inferInstance
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian πN
  haveI : CompactSpace N := (quasiCompact_iff_compactSpace πN).mp inferInstance
  haveI : IsNoetherian N := ⟨⟩
  haveI : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion u
  haveI : NoetherianSpace U := u.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  haveI : CompactSpace Y := (quasiCompact_iff_compactSpace pY).mp inferInstance
  haveI : IsNoetherian Y := ⟨⟩
  let cU := u ≫ πN
  obtain ⟨V, hdV, hdYV, hsmV, hsmYV, _hsp, _hpp⟩ :=
    PhilipponAbsoluteSmoothOpen.exists_dense_absolute_smooth_open k cU pY
  let Y₁ : Y.Opens := pY ⁻¹ᵁ V
  let p₁ : (Y₁ : Scheme.{u}) ⟶ (V : Scheme.{u}) := pY ∣_ V
  let u₁ : (V : Scheme.{u}) ⟶ N := V.ι ≫ u
  let a₁ : (Y₁ : Scheme.{u}) ⟶ X := Y₁.ι ≫ aY
  haveI : IsDominant V.ι := ⟨by simpa only [DenseRange, Scheme.Opens.range_ι] using hdV⟩
  haveI : Nonempty (V : Scheme.{u}) := by
    obtain ⟨v, hv⟩ := hdV.nonempty
    exact ⟨⟨v, hv⟩⟩
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion V.ι
  haveI : IsDominant Y₁.ι := ⟨by simpa only [DenseRange, Scheme.Opens.range_ι] using hdYV⟩
  haveI : NoetherianSpace (Y₁ : Scheme.{u}) :=
    Y₁.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : Smooth p₁ := inferInstance
  haveI : IsProper p₁ := inferInstance
  have hrestr : p₁ ≫ V.ι = Y₁.ι ≫ pY := morphismRestrict_ι pY V
  have hπ₁ : p₁ ≫ u₁ ≫ πN = Y₁.ι ≫ pY ≫ cU := by
    simpa only [p₁, u₁, cU, Category.assoc] using
      congrArg (fun f => f ≫ u ≫ πN) hrestr
  haveI : Smooth (p₁ ≫ u₁ ≫ πN) := by rw [hπ₁]; exact hsmYV
  haveI : Smooth (u₁ ≫ πN) := by simpa only [u₁, cU, Category.assoc] using hsmV
  have hbaseY : aY ≫ πX = pY ≫ u ≫ πN := by
    calc
      aY ≫ πX = (aY ≫ q) ≫ πS := by simp only [Category.assoc, hqπ]
      _ = (pY ≫ u ≫ qN) ≫ πS := congrArg (fun f => f ≫ πS) hqa
      _ = pY ≫ u ≫ πN := by simp only [πN, Category.assoc]
  have hqa₁ : a₁ ≫ q = p₁ ≫ u₁ ≫ qN := by
    calc
      a₁ ≫ q = Y₁.ι ≫ pY ≫ u ≫ qN := by
        simpa only [a₁, Category.assoc] using congrArg (fun f => Y₁.ι ≫ f) hqa
      _ = p₁ ≫ u₁ ≫ qN := by
        symm
        simpa only [u₁, Category.assoc] using congrArg (fun f => f ≫ u ≫ qN) hrestr
  have ha₁ : a₁ ≫ πX = p₁ ≫ u₁ ≫ πN := by
    rw [hπ₁]
    simpa only [a₁, cU, Category.assoc] using congrArg (fun f => Y₁.ι ≫ f) hbaseY
  obtain ⟨n₁, j₁, hj₁, hbasej₁⟩ :=
    PhilipponRelativeProjectiveImmersion.exists_absolute_projective_immersion k A nM (Y₁.ι ≫ tY ≫ iM)
  haveI : IsImmersion j₁ := hj₁
  have hrelk : tY ≫ iM ≫ ProjSpace.π A nM ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      pY ≫ u ≫ πN := by
    simpa only [Category.assoc, hjbase] using
      congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))) hpYeq
  have hj₁base : j₁ ≫ ProjSpace.π k n₁ = p₁ ≫ u₁ ≫ πN := by
    calc
      j₁ ≫ ProjSpace.π k n₁ = Y₁.ι ≫ (tY ≫ iM ≫ ProjSpace.π A nM ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
        simpa only [Category.assoc] using hbasej₁
      _ = Y₁.ι ≫ pY ≫ cU := by
        simpa only [cU, Category.assoc] using congrArg (fun f => Y₁.ι ≫ f) hrelk
      _ = p₁ ≫ u₁ ≫ πN := hπ₁.symm
  obtain ⟨W, G, fX, fN, tW, hW, _hcW, hsmW, hprW, hsurW, habsW, _hdomW,
    hG, hnG, hfX, hsfX, hfN, hsfN, htW, hdtW, htX, hpull, hcomp, hdG,
    dG, jG, hjG, hjGbase⟩ :=
    AlgebraicGeometry.exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
      k u₁ p₁ πX mX iX hiX πN nN iN hbaseN n₁ j₁ hj₁base a₁ ha₁
  haveI : IsIntegral G := hG
  haveI : IsDominant tW := hdtW
  have hcomm : fX ≫ q = fN ≫ qN := by
    apply ext_of_isDominant_of_isSeparated πS ?_ tW ?_
    · simpa only [πN, Category.assoc, hqπ] using hcomp
    · calc
        tW ≫ (fX ≫ q) = (W.ι ≫ a₁) ≫ q := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ q) htX
        _ = W.ι ≫ p₁ ≫ u₁ ≫ qN := by simp only [Category.assoc, hqa₁]
        _ = tW ≫ (fN ≫ qN) := by
          simpa only [Category.assoc] using (congrArg (fun f => f ≫ qN) hpull.w).symm
  exact ⟨N, qN, V, u₁, W, W.ι ≫ p₁, G, fX, fN, tW,
    hN, hnN, hqN, hsqN, hdN, inferInstance, inferInstance, inferInstance,
    inferInstance, hW, hsmW, hprW, hsurW, habsW, hG, hnG, hfX, hsfX, hfN, hsfN,
    htW, hdtW, hpull, hcomm, hcomp, hdG, ⟨nN, iN, hiN, hbaseN⟩,
    dG, jG, hjG, hjGbase⟩


/-- Globalize the actual finite-base covering-family preparation into a
normal projective model over the same normal projective base, with a
cartesian smooth proper family on a dense smooth base open. -/
theorem exists_model_of_covering_family_data
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) (hqπ : q ≫ πS = πX) (η : S)
    (hP : HasNormalProjectiveBaseSmoothCurveCoverFamily k πS q η) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  letI : Algebra k (S.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
  obtain ⟨E, _hE, hrest⟩ := hP
  letI : Algebra k E := ((algebraMap (S.residueField η) E).comp (algebraMap k (S.residueField η))).toAlgebra
  obtain ⟨B, hBft, _hBn, _hBE, N, qN, tN, hN, hnN, hqN, hsqN, htN, hdtN, hdN,
    htbase, _hgen, ⟨nN, iN, hiN, hbaseN⟩, a, _ha, nM, M, iM, hiM,
    U, j, hj, _hdj, hu, hdu, Y, Z, pY, pZ, tY, tZ, h,
    hpY, hpZ, _hflatZ, _hprZ, hover, _hprh, _hsurh, hsmY, hprY, hdomY,
    C₀, p₀, a₀, _hsm₀, _hpr₀, _hdim₀, _hpra₀, _hsura₀, _hbase₀, _hproj₀,
    b, _eC, _hbu, _hpc, _hrec⟩ := hrest
  let A := Localization.Away a
  let u : U ⟶ N := (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B A))) ≫ tN
  let πN := qN ≫ πS
  haveI : Algebra.FiniteType k B := hBft
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (R := k) (S := B) (A := A) inferInstance inferInstance
  haveI : IsIntegral N := hN
  haveI : IsProper qN := hqN
  haveI : Surjective qN := hsqN
  haveI : IsClosedImmersion iN := hiN
  haveI : IsClosedImmersion iM := hiM
  haveI : IsOpenImmersion j := hj
  haveI : IsOpenImmersion u := hu
  haveI : IsDominant u := hdu
  haveI : Nonempty U := ⟨b (genericPoint (Spec (.of E)))⟩
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion u
  haveI : Smooth pY := hsmY
  haveI : IsProper pY := hprY
  haveI : IsDominant (h ≫ tZ) := hdomY
  have hYq : (h ≫ tZ) ≫ q = pY ≫ u ≫ qN := by
    calc
      (h ≫ tZ) ≫ q = h ≫ (pZ ≫ u ≫ qN) := by rw [Category.assoc, hpZ.w]
      _ = pY ≫ u ≫ qN := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ u ≫ qN) hover
  haveI : IsOpenImmersion tY := MorphismProperty.of_isPullback hpY.flip (inferInstance : IsOpenImmersion j)
  have hmaps : Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Spec.map_comp]
    congr 1
  have hjbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = u ≫ πN := by
    simp only [u, πN, Category.assoc, htbase, hmaps]
  exact exists_model_of_relative_projective_family k A πS πX mX iX hiX q hqπ
    qN hnN hdN nN iN hbaseN u pY nM iM tY j hpY.w hjbase (h ≫ tZ) hYq

end PhilipponGlobalFamilyModel

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponGlobalFamilyApplication

/-- Apply the accepted finite-generic-field covering data and its global
normal projective completion to the original projective fibration. -/
theorem exists_global_family_model
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  apply PhilipponGlobalFamilyModel.exists_model_of_covering_family_data
    k πS πX mX iX hiX q hqπ η
  exact AlgebraicGeometry.hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
    k πS mS iS hiS q η hη hdim

end PhilipponGlobalFamilyApplication

theorem solution
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  exact PhilipponGlobalFamilyApplication.exists_global_family_model k πS mS iS hiS πX mX iX hiX q hqπ η hη hdim
