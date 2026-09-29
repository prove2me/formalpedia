-- Prove2me | solution 1 for AlgebraicGeometry.ChowDatum.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7495b4ff-148d-5b4d-b20d-14a441fa3ef1

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.RationalMap
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ChowDatum_nonempty

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsLocallyNoetherian Scheme.IdealSheafData.ideal_bot IsOpenImmersion.lift Surjective Scheme.IdealSheafData.radical_ideal Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom IsSchemeTheoreticallyDominant.isReduced QuasiCompact Scheme.Pullback.range_fst IsAffine Scheme.topIso Scheme.Hom.support_ker LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme ext_of_isDominant Proj.fromOfGlobalSections_toSpecZero QuasiCompact.compactSpace_of_compactSpace ext_of_isDominant_of_isSeparated IsOpenImmersion Scheme.Hom.comp_base Proj IsSchemeTheoreticallyDominant IsClosedImmersion.iff_isProper_and_mono IsClosedImmersion.spec_of_surjective Scheme.IdealSheafData.ext_of_iSup_eq_top IsClosedImmersion IsReduced IsSeparated Proj.fromOfGlobalSections_preimage_basicOpen IsClosedImmersion.lift ext_to_Spec isAffineOpen_top toSpecΓ_SpecMap_ΓSpecIso_inv IsClosedImmersion.lift_fac IsProper.of_comp Scheme.pullback_map_isOpenImmersion Proj.basicOpen Proj.fromOfGlobalSections_resLE Scheme.isBasis_affineOpens IsDominant IsAffineOpen Scheme.Hom.toImage IsNoetherian Scheme.Hom.preimage_iSup Scheme.Hom.ker_apply Scheme.Opens Scheme.homOfLE_ι Scheme.basicOpen_one isIso_of_isClosedImmersion_of_surjective Scheme.Hom.toImage_app_injective Scheme.Hom.comp_preimage Proj.fromOfGlobalSections isReduced_of_isOpenImmersion Scheme.Hom.toImage_imageι Scheme.IdealSheafData.vanishingIdeal_support IsOpenImmersion.lift_fac toSpecΓ IsAffine.affine range_eq_univ Proj.toBasicOpenOfGlobalSections Scheme.IdealSheafData Scheme.ΓSpecIso isIntegral_of_irreducibleSpace_of_isReduced ProjSpace.grad0Equiv ProjSpace.π ProjSpace.prodOver ProjSpace.prodOverπ ProjSpace.isProper_prodOverπ ProjSpace.prodPr ProjSpace.prodPr_comp_π ProjSpace.prodLift ProjSpace.prodLift_comp_prodOverπ ProjSpace.prodLift_comp_prodPr ChowDatum"
p2m_open "AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ChowLemma

structure FinAffCover (V : Scheme.{u}) where

  ι : Type u
  [fι : Fintype ι]
  [linι : LinearOrder ι]

  U : ι → V.Opens

  hU : ∀ i, IsAffineOpen (U i)

  hcov : ⨆ i, U i = ⊤

attribute [scoped instance] FinAffCover.fι FinAffCover.linι

theorem FinAffCover.exists_of_isProper {R : Type u} [CommRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of R)) [IsProper π] :
    Nonempty (FinAffCover V) := by
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π

  have hcov_all : (⊤ : Set V) ⊆ ⋃ W : V.affineOpens, (W.1 : Set V) := fun x _ => by
    obtain ⟨W, hWaff, hxW, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens
        (show x ∈ (⊤ : V.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨W, hWaff⟩, hxW⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun W : V.affineOpens => (W.1 : Set V))
    (fun W => W.1.2) hcov_all

  let _lo : LinearOrder V.affineOpens := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨{ ι := S, U := fun i => i.1.1, hU := fun i => i.1.2, hcov := ?_ }⟩
  refine le_antisymm le_top (fun x _ => ?_)
  rcases Set.mem_iUnion₂.mp (hS (Set.mem_univ x)) with ⟨W, hWS, hxW⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWS⟩, hxW⟩

section CanonicalAlg

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))

@[reducible] def canonicalAlg (W : V.Opens) : Algebra R Γ(V, W) :=
  ((V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra

theorem canonicalAlg_compat (W : V.Opens) :
    ∀ c, letI := canonicalAlg π W
      algebraMap R Γ(V, W) c = (V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
  fun _ => rfl

end CanonicalAlg

section PerChart

open AlgebraicGeometry.Proj

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
variable (W : V.Opens) (hW : IsAffineOpen W)
include hW

theorem gammaFiniteType :
    letI := canonicalAlg π W
    Algebra.FiniteType R Γ(V, W) := by
  letI := canonicalAlg π W
  have happ : (π.appLE ⊤ W le_top).hom.FiniteType :=
    π.finiteType_appLE (isAffineOpen_top _) hW le_top
  have hcomp : ((π.appLE ⊤ W le_top).hom.comp
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.toRingHom).FiniteType :=
    RingHom.finiteType_respectsIso.2 _ _ happ
  refine RingHom.finiteType_algebraMap.mp ?_
  convert hcomp using 2
  exact RingHom.ext fun _ => rfl

def chartN : ℕ :=
  letI := canonicalAlg π W
  (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (gammaFiniteType π W hW)).choose

local notation "𝒜W" =>
  MvPolynomial.homogeneousSubmodule (Fin (chartN π W hW + 1)) R

def chartφ :
    MvPolynomial (Fin (chartN π W hW + 1)) R →+* Γ(W.toScheme, ⊤) :=
  letI := canonicalAlg π W
  let hft := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (gammaFiniteType π W hW)
  let f₀ : MvPolynomial (Fin hft.choose) R →ₐ[R] Γ(V, W) := hft.choose_spec.choose
  W.topIso.inv.hom.comp
    (MvPolynomial.eval₂Hom (algebraMap R _) (Fin.cons 1 (fun k => f₀ (MvPolynomial.X k))))

theorem chartφ_surj : Function.Surjective (chartφ π W hW) := by
  letI := canonicalAlg π W
  refine (W.topIso.symm.commRingCatIsoToRingEquiv.surjective).comp ?_
  set hft := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (gammaFiniteType π W hW) with hft_def
  set f₀ : MvPolynomial (Fin hft.choose) R →ₐ[R] Γ(V, W) := hft.choose_spec.choose with f₀_def
  have hf₀surj : Function.Surjective f₀ := hft.choose_spec.choose_spec
  intro x
  obtain ⟨p, rfl⟩ := hf₀surj x
  refine ⟨MvPolynomial.rename Fin.succ p, ?_⟩
  show MvPolynomial.eval₂Hom (algebraMap R _)
      (Fin.cons 1 (fun k => f₀ (MvPolynomial.X k))) (MvPolynomial.rename Fin.succ p) = f₀ p
  induction p using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.eval₂Hom_X', hp, Fin.cons_succ]

theorem chartφ_X0 : chartφ π W hW (MvPolynomial.X 0) = 1 := by
  unfold chartφ
  simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval₂Hom_X', Fin.cons_zero,
    map_one]

theorem chartφ_irr :
    (HomogeneousIdeal.irrelevant 𝒜W).toIdeal.map (chartφ π W hW) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← chartφ_X0 π W hW]
  refine Ideal.mem_map_of_mem _ ?_
  show (MvPolynomial.X 0 : MvPolynomial _ R) ∈ HomogeneousIdeal.irrelevant 𝒜W
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R _))
      one_ne_zero]

def chartJ : W.toScheme ⟶ Proj 𝒜W :=
  Proj.fromOfGlobalSections _ (chartφ π W hW) (chartφ_irr π W hW)

theorem chartJ_over :
    chartJ π W hW ≫ ProjSpace.π R (chartN π W hW)
      = W.ι ≫ π := by
  letI := canonicalAlg π W

  rw [chartJ, ProjSpace.π, ← Category.assoc,
    Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have hg : CommRingCat.ofHom (((chartφ π W hW).comp (algebraMap _ _)).comp
        (ProjSpace.grad0Equiv R (chartN π W hW)).toRingHom)
      = (Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ π).appTop := by
    ext r

    show chartφ π W hW
        ((algebraMap (𝒜W 0) (MvPolynomial (Fin (chartN π W hW + 1)) R))
          ((ProjSpace.grad0Equiv R (chartN π W hW)) r))
      = ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ π).appTop) r
    have hCr : (algebraMap (𝒜W 0) (MvPolynomial (Fin (chartN π W hW + 1)) R))
        ((ProjSpace.grad0Equiv R (chartN π W hW)) r) = MvPolynomial.C r := rfl
    rw [hCr]
    show W.topIso.inv.hom (MvPolynomial.eval₂Hom (algebraMap R Γ(V, W)) _ (MvPolynomial.C r))
      = ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ π).appTop) r
    rw [MvPolynomial.eval₂Hom_C, canonicalAlg_compat π W r]

    change (V.presheaf.map _)
        ((V.presheaf.map _) (π.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
      = (V.presheaf.map _) (π.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    exact congrFun (congrArg (fun h => ⇑(V.presheaf.map h)) (Subsingleton.elim _ _)) _
  rw [hg, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem chartJ_preimage_D0 :
    chartJ π W hW ⁻¹ᵁ Proj.basicOpen 𝒜W (MvPolynomial.X 0) = ⊤ := by
  rw [chartJ, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R _)),
    chartφ_X0, Scheme.basicOpen_one]

def chartJD :
    W.toScheme ⟶ (Proj.basicOpen 𝒜W (MvPolynomial.X 0)).toScheme :=
  (Scheme.topIso W.toScheme).inv ≫
    (chartJ π W hW).resLE _ ⊤ (chartJ_preimage_D0 π W hW).ge

theorem chartJD_ι :
    chartJD π W hW ≫ (Proj.basicOpen 𝒜W (MvPolynomial.X 0)).ι
      = chartJ π W hW := by
  rw [chartJD, Category.assoc, Scheme.Hom.resLE_comp_ι]
  simp

theorem chartJD_closed : IsClosedImmersion (chartJD π W hW) := by
  haveI : IsAffine W.toScheme := hW
  have hX0_deg : (MvPolynomial.X 0 : MvPolynomial _ R) ∈ 𝒜W 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R _)

  haveI hbOι_iso : IsIso (W.toScheme.basicOpen (chartφ π W hW (X 0))).ι := by
    rw [chartφ_X0 π W hW, Scheme.basicOpen_one]
    exact inferInstanceAs (IsIso (Scheme.topIso W.toScheme).hom)
  have hfac : chartJD π W hW
      = inv (W.toScheme.basicOpen (chartφ π W hW (X 0))).ι
        ≫ Proj.toBasicOpenOfGlobalSections 𝒜W (chartφ π W hW) rfl one_pos
          hX0_deg := by
    rw [← cancel_mono (Proj.basicOpen 𝒜W (MvPolynomial.X 0)).ι, Category.assoc,
      chartJD_ι π W hW,
      ← Proj.fromOfGlobalSections_resLE 𝒜W (chartφ π W hW)
        (chartφ_irr π W hW) one_pos hX0_deg,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp,
      chartJ]
  rw [hfac]

  haveI : IsIso W.toScheme.toSpecΓ := IsAffine.affine
  show (@IsClosedImmersion) _
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  unfold Proj.toBasicOpenOfGlobalSections
  simp only [Category.assoc]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]

  refine IsClosedImmersion.spec_of_surjective _ ?_

  intro z
  obtain ⟨y, hy⟩ : ∃ y, algebraMap Γ(W.toScheme, ⊤) _ y = z := by
    obtain ⟨⟨y, s⟩, hz⟩ := IsLocalization.surj (M := Submonoid.powers
      (chartφ π W hW (X 0))) z
    have hs1 : (s : Γ(W.toScheme, ⊤)) = 1 := by
      obtain ⟨n, hn⟩ := s.2
      simp only [← hn, chartφ_X0, one_pow]
    exact ⟨y, by rw [← hz, hs1, map_one, mul_one]⟩
  obtain ⟨p, rfl⟩ := chartφ_surj π W hW y
  refine ⟨∑ d ∈ Finset.range (p.totalDegree + 1),
    HomogeneousLocalization.mk ⟨d, ⟨MvPolynomial.homogeneousComponent d p,
        (MvPolynomial.mem_homogeneousSubmodule d _).mpr
          (MvPolynomial.homogeneousComponent_mem d p)⟩,
      ⟨(MvPolynomial.X 0)^d, by simpa using SetLike.pow_mem_graded d hX0_deg⟩, d, rfl⟩, ?_⟩
  rw [← hy, map_sum]
  trans ∑ d ∈ Finset.range (p.totalDegree + 1),
    algebraMap Γ(W.toScheme, ⊤) _
      (chartφ π W hW (MvPolynomial.homogeneousComponent d p))
  ·
    refine Finset.sum_congr rfl fun d _ => ?_
    show ((IsLocalization.map _ (chartφ π W hW) _).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜W (X 0)) (Localization.Away (X 0))))
        (HomogeneousLocalization.mk _) = _
    rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
    refine Eq.trans ?_ (IsLocalization.mk'_one
      (M := Submonoid.powers (chartφ π W hW (X 0)))
      (Localization.Away (chartφ π W hW (X 0)))
      (chartφ π W hW (MvPolynomial.homogeneousComponent d p)))
    congr 1
    exact Subtype.ext (by simp [chartφ_X0])
  · rw [← map_sum, ← map_sum, MvPolynomial.sum_homogeneousComponent]

end PerChart

section Headline

open AlgebraicGeometry.Proj

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π] [IsIntegral V]

set_option maxHeartbeats 32000000 in

theorem chowDatum_nonempty : Nonempty (ChowDatum π) := by
  classical

  obtain ⟨K⟩ := FinAffCover.exists_of_isProper π

  let ι' : Type u := {i : K.ι // (K.U i).1.Nonempty}
  haveI : Fintype ι' := Subtype.fintype _
  let m := Fintype.card ι'
  let σ : Fin m ≃ ι' := (Fintype.equivFin ι').symm

  have hcov' : ⨆ k : Fin m, K.U (σ k).1 = ⊤ := by
    refine le_antisymm le_top (K.hcov ▸ iSup_le fun i => ?_)
    rcases (K.U i).1.eq_empty_or_nonempty with hemp | hne
    · exact fun x hx => absurd (show x ∈ (K.U i).1 from hx) (hemp ▸ Set.notMem_empty x)
    · exact (le_iSup (fun k : Fin m => K.U (σ k).1) (σ.symm ⟨i, hne⟩)).trans'
        (le_of_eq (by simp))

  let e : Fin m → ℕ := fun k => chartN π (K.U (σ k).1) (K.hU (σ k).1)

  let U : V.Opens := ⨅ k : Fin m, K.U (σ k).1
  have hU_le : ∀ k, U ≤ K.U (σ k).1 := fun k => iInf_le _ k

  have hU_ne : (U : Set V).Nonempty := by
    have hirr := isIrreducible_iff_sInter.mp (IrreducibleSpace.isIrreducible_univ (X := V))
      (Finset.univ.image (fun k : Fin m => (K.U (σ k).1 : Set V)))
      (by simp only [Finset.forall_mem_image, Finset.mem_univ, forall_const]
          exact fun k => (K.U (σ k).1).2)
      (by simp only [Finset.forall_mem_image, Finset.mem_univ, forall_const, Set.univ_inter]
          exact fun k => (σ k).2)
    simp only [Set.univ_inter, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.sInter_range] at hirr

    have hopen : IsOpen (⋂ k : Fin m, (K.U (σ k).1 : Set V)) :=
      isOpen_iInter_of_finite fun k => (K.U (σ k).1).2
    have hle : (⟨_, hopen⟩ : V.Opens) ≤ U :=
      le_iInf fun k => fun x hx => Set.mem_iInter.mp hx k
    exact hirr.mono hle

  have hU_dense : Dense (U : Set V) := U.2.dense hU_ne

  let gU : ∀ k : Fin m, U.toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R) :=
    fun k => V.homOfLE (hU_le k) ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1)
  have hgU : ∀ k, gU k ≫ ProjSpace.π R (e k) = U.ι ≫ π := fun k => by
    show (V.homOfLE (hU_le k) ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1))
        ≫ ProjSpace.π R (e k) = U.ι ≫ π
    rw [Category.assoc, chartJ_over, ← Category.assoc, Scheme.homOfLE_ι]
  let jU : U.toScheme ⟶ ProjSpace.prodOver R e :=
    ProjSpace.prodLift R (U.ι ≫ π) e gU hgU
  have hjU_over : jU ≫ ProjSpace.prodOverπ R e = U.ι ≫ π :=
    ProjSpace.prodLift_comp_prodOverπ R (U.ι ≫ π) e gU hgU

  haveI : IsSeparated (ProjSpace.prodOverπ R e) :=
    (ProjSpace.isProper_prodOverπ R e).toIsSeparated
  let ψ₀ : U.toScheme ⟶ pullback (jU ≫ ProjSpace.prodOverπ R e)
      (ProjSpace.prodOverπ R e) :=
    pullback.lift (𝟙 _) jU (Category.id_comp _)
  haveI hψ₀ : IsClosedImmersion ψ₀ := inferInstance

  let θ : pullback (jU ≫ ProjSpace.prodOverπ R e) (ProjSpace.prodOverπ R e)
      ⟶ pullback π (ProjSpace.prodOverπ R e) :=
    pullback.map _ _ _ _ U.ι (𝟙 _) (𝟙 _) (by rw [hjU_over, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])
  haveI hθ : IsOpenImmersion θ := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  have hθ_fst : θ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ U.ι :=
    pullback.lift_fst _ _ _
  have hθ_snd : θ ≫ pullback.snd _ _ = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)

  let ψ : U.toScheme ⟶ pullback π (ProjSpace.prodOverπ R e) := ψ₀ ≫ θ
  have hψ_fst : ψ ≫ pullback.fst _ _ = U.ι := by
    rw [show ψ = ψ₀ ≫ θ from rfl, Category.assoc, hθ_fst, ← Category.assoc,
      show ψ₀ ≫ pullback.fst _ _ = 𝟙 _ from pullback.lift_fst _ _ _, Category.id_comp]
  have hψ_snd : ψ ≫ pullback.snd _ _ = jU := by
    rw [show ψ = ψ₀ ≫ θ from rfl, Category.assoc, hθ_snd,
      show ψ₀ ≫ pullback.snd _ _ = jU from pullback.lift_snd _ _ _]

  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  haveI : IsNoetherian V := ⟨⟩
  haveI : NoetherianSpace V := inferInstance
  haveI : NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ψ := inferInstance

  let V' : Scheme := ψ.image
  let α : V' ⟶ pullback π (ProjSpace.prodOverπ R e) := ψ.imageι
  let p : V' ⟶ V := α ≫ pullback.fst _ _
  let ι : V' ⟶ ProjSpace.prodOver R e := α ≫ pullback.snd _ _
  have hover : ι ≫ ProjSpace.prodOverπ R e = p ≫ π := by
    simp only [ι, p, Category.assoc, ← pullback.condition]
  have hψ_toImage_p : ψ.toImage ≫ p = U.ι := by
    rw [show p = ψ.imageι ≫ pullback.fst _ _ from rfl, ← Category.assoc,
      Scheme.Hom.toImage_imageι, hψ_fst]
  have hψ_toImage_ι : ψ.toImage ≫ ι = jU := by
    rw [show ι = ψ.imageι ≫ pullback.snd _ _ from rfl, ← Category.assoc,
      Scheme.Hom.toImage_imageι, hψ_snd]

  haveI hfst_proper : IsProper (pullback.fst π (ProjSpace.prodOverπ R e)) := inferInstance
  haveI hp_proper : IsProper p := inferInstanceAs (IsProper (α ≫ pullback.fst _ _))

  haveI hψ_dom : IsDominant ψ.toImage := inferInstance
  have hp_surj : Function.Surjective p := by
    rw [← Set.range_eq_univ, ← (IsClosedMap.isClosed_range p.isClosedMap).closure_eq,
      ← Set.univ_subset_iff, ← hU_dense.closure_eq]
    refine closure_mono ?_
    have hr : Set.range U.ι ⊆ Set.range p := by
      rw [← hψ_toImage_p]
      exact Set.range_comp_subset_range (⇑(Scheme.Hom.toImage ψ).base) (⇑p.base)
    simpa only [Scheme.Opens.range_ι] using hr

  haveI hU_red : IsReduced U.toScheme := inferInstance
  have hUV_irr : IsIrreducible (U : Set V) :=
    isIrreducible_iff_closure.mp (hU_dense.closure_eq ▸ IrreducibleSpace.isIrreducible_univ _)
  haveI hU_irr : IrreducibleSpace U.toScheme := isIrreducible_iff_irreducibleSpace.mp hUV_irr
  haveI hV'_ne : Nonempty V' := ⟨(ψ.toImage).base hU_ne.to_subtype.some⟩
  haveI hV'_irr : IrreducibleSpace V' := by
    have hrange : IsIrreducible (Set.range (α : V' → _)) := by
      rw [show (α : V' ⟶ _) = ψ.imageι from rfl,
        show Set.range (ψ.imageι : V' → _) = (ψ.ker.support : Set _) from
          Scheme.IdealSheafData.range_subschemeι _,
        Scheme.Hom.support_ker]
      refine IsIrreducible.closure ?_
      rw [← Set.image_univ]
      exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) (⇑ψ.base)
        (Continuous.continuousOn ψ.continuous)

    refine { toNonempty := hV'_ne, isPreirreducible_univ := ?_ }
    have hind := (ψ.imageι).isClosedEmbedding.isEmbedding.isInducing
    intro u v hu hv hune hvne
    obtain ⟨u', hu', rfl⟩ := hind.isOpen_iff.mp hu
    obtain ⟨v', hv', rfl⟩ := hind.isOpen_iff.mp hv
    obtain ⟨xu, -, hxu⟩ := hune
    obtain ⟨xv, -, hxv⟩ := hvne
    have key := hrange.2 u' v' hu' hv'
      ⟨_, ⟨xu, rfl⟩, hxu⟩ ⟨_, ⟨xv, rfl⟩, hxv⟩
    obtain ⟨_, ⟨x, rfl⟩, hx_u', hx_v'⟩ := key
    exact ⟨x, trivial, hx_u', hx_v'⟩

  haveI : QuasiCompact ψ.toImage := inferInstance
  haveI : IsSchemeTheoreticallyDominant ψ.toImage := by

    refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
      (ι := (pullback π (ProjSpace.prodOverπ R e)).affineOpens)
      (fun W'' => ⟨ψ.imageι ⁻¹ᵁ W''.1, W''.2.preimage ψ.imageι⟩) ?_ (fun W'' => ?_)⟩
    · rw [← top_le_iff]
      intro x _
      obtain ⟨_, ⟨W₀, hW₀_aff, rfl⟩, hxW'', -⟩ :=
        (pullback π (ProjSpace.prodOverπ R e)).isBasis_affineOpens
          |>.exists_subset_of_mem_open (Set.mem_univ (ψ.imageι.base x)) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W₀, hW₀_aff⟩, hxW''⟩
    · simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact (RingHom.injective_iff_ker_eq_bot _).mp
        (Scheme.Hom.toImage_app_injective ψ W'')
  haveI hV'_red : IsReduced V' := IsSchemeTheoreticallyDominant.isReduced ψ.toImage
  haveI hV'_int : IsIntegral V' := isIntegral_of_irreducibleSpace_of_isReduced V'

  haveI : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : NoetherianSpace V' := by
    haveI : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace p
    haveI : IsNoetherian V' := ⟨⟩
    infer_instance

  haveI hι_proper : IsProper ι := by
    have : IsProper (ι ≫ ProjSpace.prodOverπ R e) := hover ▸ inferInstance
    exact IsProper.of_comp ι (ProjSpace.prodOverπ R e)

  have hψ_ιpr : ∀ k, ψ.toImage ≫ ι ≫ ProjSpace.prodPr R e k
      = V.homOfLE (hU_le k) ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1) := by
    intro k
    rw [← Category.assoc, hψ_toImage_ι, ProjSpace.prodLift_comp_prodPr]

  have hjₖ_mono : ∀ k : Fin m, Mono (chartJ π (K.U (σ k).1) (K.hU (σ k).1)) := by
    intro k
    rw [← chartJD_ι]
    haveI := chartJD_closed π (K.U (σ k).1) (K.hU (σ k).1)
    infer_instance

  have h5b : ∀ k : Fin m,
      pullback.fst p (K.U (σ k).1).ι ≫ ι ≫ ProjSpace.prodPr R e k
        = pullback.snd p (K.U (σ k).1).ι
            ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1) := by
    intro k

    let βₖ : U.toScheme ⟶ pullback p (K.U (σ k).1).ι :=
      pullback.lift ψ.toImage (V.homOfLE (hU_le k))
        (by rw [hψ_toImage_p, Scheme.homOfLE_ι])

    haveI : IsOpenImmersion (pullback.fst p (K.U (σ k).1).ι) := inferInstance
    haveI : IsReduced (pullback p (K.U (σ k).1).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst p (K.U (σ k).1).ι)
    have hβₖ_fst : βₖ ≫ pullback.fst _ _ = ψ.toImage := pullback.lift_fst _ _ _
    haveI : IsDominant βₖ := by
      refine ⟨?_⟩
      rw [DenseRange, dense_iff_closure_eq,
        (pullback.fst p (K.U (σ k).1).ι).isOpenEmbedding.isEmbedding.isInducing
          |>.closure_eq_preimage_closure_image,
        ← Set.range_comp,
        show ⇑(pullback.fst p (K.U (σ k).1).ι).base ∘ ⇑βₖ.base
          = ⇑(βₖ ≫ pullback.fst p (K.U (σ k).1).ι).base from rfl,
        hβₖ_fst, hψ_dom.denseRange.closure_eq, Set.preimage_univ]

    refine ext_of_isDominant_of_isSeparated (ProjSpace.π R (e k))
      ?_ βₖ ?_
    ·

      have lhs : (pullback.fst p (K.U (σ k).1).ι ≫ ι ≫ ProjSpace.prodPr R e k)
          ≫ ProjSpace.π R (e k) = pullback.fst p (K.U (σ k).1).ι ≫ p ≫ π := by
        rw [Category.assoc, Category.assoc, ProjSpace.prodPr_comp_π]
        exact (pullback.fst p (K.U (σ k).1).ι) ≫= hover
      have rhs : (pullback.snd p (K.U (σ k).1).ι
            ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1))
          ≫ ProjSpace.π R (e k) = pullback.snd p (K.U (σ k).1).ι ≫ (K.U (σ k).1).ι ≫ π :=
        (Category.assoc _ _ _).trans
          ((pullback.snd p (K.U (σ k).1).ι) ≫= chartJ_over π _ _)
      rw [lhs, rhs]
      exact pullback.condition_assoc π
    ·

      rw [← Category.assoc, hβₖ_fst, hψ_ιpr k, ← Category.assoc,
        show βₖ ≫ pullback.snd _ _ = V.homOfLE (hU_le k) from pullback.lift_snd _ _ _]

  let Wₖ : ∀ k, (ProjSpace.prodOver R e).Opens := fun k =>
    ProjSpace.prodPr R e k ⁻¹ᵁ
      Proj.basicOpen _ (MvPolynomial.X (0 : Fin (e k + 1)))
  have h5c : ∀ k : Fin m, ι ⁻¹ᵁ Wₖ k = p ⁻¹ᵁ K.U (σ k).1 := by
    intro k
    refine le_antisymm ?_ ?_
    ·

      have hrange1 : Set.range ⇑(ι ≫ ProjSpace.prodPr R e k).base
          ⊆ closure (Set.range ⇑(V.homOfLE (hU_le k)
            ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1)).base) := by
        have hc : ⇑(ι ≫ ProjSpace.prodPr R e k).base '' Set.range ⇑ψ.toImage.base
            = Set.range ⇑(V.homOfLE (hU_le k)
              ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1)).base := by
          rw [← Set.range_comp, ← hψ_ιpr k]; rfl
        calc Set.range ⇑(ι ≫ ProjSpace.prodPr R e k).base
            = ⇑(ι ≫ ProjSpace.prodPr R e k).base '' Set.univ := (Set.image_univ).symm
          _ = ⇑(ι ≫ ProjSpace.prodPr R e k).base
              '' closure (Set.range ⇑ψ.toImage.base) := by rw [hψ_dom.denseRange.closure_eq]
          _ ⊆ closure (⇑(ι ≫ ProjSpace.prodPr R e k).base
              '' Set.range ⇑ψ.toImage.base) :=
            image_closure_subset_closure_image (ι ≫ ProjSpace.prodPr R e k).continuous
          _ = _ := by rw [hc]

      haveI := chartJD_closed π (K.U (σ k).1) (K.hU (σ k).1)
      let D₀ₖ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R)).Opens :=
        Proj.basicOpen _ (MvPolynomial.X (0 : Fin (e k + 1)))
      let γₖ : (ι ⁻¹ᵁ Wₖ k).toScheme ⟶ D₀ₖ.toScheme :=
        (ι ≫ ProjSpace.prodPr R e k).resLE D₀ₖ _
          (le_of_eq (Scheme.Hom.comp_preimage _ _ _).symm)
      have hγₖ_ι : γₖ ≫ D₀ₖ.ι = (ι ⁻¹ᵁ Wₖ k).ι ≫ ι ≫ ProjSpace.prodPr R e k :=
        Scheme.Hom.resLE_comp_ι _ _
      have hrange_γₖ : Set.range ⇑γₖ.base
          ⊆ Set.range ⇑(chartJD π (K.U (σ k).1) (K.hU (σ k).1)).base := by
        have hemb := D₀ₖ.ι.isOpenEmbedding

        have hcl : Set.range ⇑(chartJD π (K.U (σ k).1) (K.hU (σ k).1)).base
            = (⇑D₀ₖ.ι.base)⁻¹' closure
              (Set.range ⇑(chartJ π (K.U (σ k).1) (K.hU (σ k).1)).base) := by
          have hjₖ_eq : Set.range ⇑(chartJ π (K.U (σ k).1) (K.hU (σ k).1)).base
              = ⇑D₀ₖ.ι.base
                '' Set.range ⇑(chartJD π (K.U (σ k).1) (K.hU (σ k).1)).base := by
            rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
              chartJD_ι π (K.U (σ k).1) (K.hU (σ k).1)]
          rw [hjₖ_eq, ← hemb.isInducing.closure_eq_preimage_closure_image,
            (chartJD π (K.U (σ k).1)
              (K.hU (σ k).1)).isClosedEmbedding.isClosed_range.closure_eq]
        rw [hcl]
        rintro z ⟨w, rfl⟩
        show D₀ₖ.ι.base (γₖ.base w) ∈ closure _
        have hw : D₀ₖ.ι.base (γₖ.base w)
            = (ι ≫ ProjSpace.prodPr R e k).base ((ι ⁻¹ᵁ Wₖ k).ι.base w) := by
          change (γₖ ≫ D₀ₖ.ι).base w = _
          rw [hγₖ_ι]; rfl
        rw [hw]
        exact closure_mono (Set.range_comp_subset_range _ _) (hrange1 ⟨_, rfl⟩)

      haveI : IsReduced (ι ⁻¹ᵁ Wₖ k).toScheme :=
        isReduced_of_isOpenImmersion (ι ⁻¹ᵁ Wₖ k).ι
      have hψ_range : Set.range ⇑ψ.toImage.base ⊆ Set.range ⇑(ι ⁻¹ᵁ Wₖ k).ι.base := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨u, rfl⟩
        show (ψ.toImage ≫ ι ≫ ProjSpace.prodPr R e k).base u ∈ D₀ₖ
        rw [hψ_ιpr k]
        show (V.homOfLE (hU_le k)).base u
          ∈ chartJ π (K.U (σ k).1) (K.hU (σ k).1) ⁻¹ᵁ D₀ₖ
        rw [chartJ_preimage_D0]; trivial
      let δ : U.toScheme ⟶ (ι ⁻¹ᵁ Wₖ k).toScheme :=
        IsOpenImmersion.lift (ι ⁻¹ᵁ Wₖ k).ι ψ.toImage hψ_range
      have hδ_ι : δ ≫ (ι ⁻¹ᵁ Wₖ k).ι = ψ.toImage := IsOpenImmersion.lift_fac _ _ _
      haveI : IsDominant δ := by
        refine ⟨?_⟩
        rw [DenseRange, dense_iff_closure_eq,
          (ι ⁻¹ᵁ Wₖ k).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
          ← Set.range_comp,
          show ⇑(ι ⁻¹ᵁ Wₖ k).ι.base ∘ ⇑δ.base = ⇑(δ ≫ (ι ⁻¹ᵁ Wₖ k).ι).base from rfl,
          hδ_ι, hψ_dom.denseRange.closure_eq, Set.preimage_univ]

      have hker : (chartJD π (K.U (σ k).1) (K.hU (σ k).1)).ker ≤ γₖ.ker := by
        haveI : NoetherianSpace (ι ⁻¹ᵁ Wₖ k).toScheme :=
          (ι ⁻¹ᵁ Wₖ k).ι.isOpenEmbedding.isInducing.noetherianSpace
        haveI : QuasiCompact γₖ := inferInstance

        have h1 : (chartJD π (K.U (σ k).1) (K.hU (σ k).1)).ker
            ≤ γₖ.ker.radical := by
          rw [← Scheme.IdealSheafData.vanishingIdeal_support,
            ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
          refine SetLike.coe_subset_coe.mp ?_
          rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
          exact closure_mono hrange_γₖ
        refine h1.trans ?_

        intro W'
        rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
        intro s hs
        obtain ⟨n, hn⟩ := hs
        rw [RingHom.mem_ker] at hn ⊢
        exact IsReduced.eq_zero _ ⟨n, by rw [← map_pow]; exact hn⟩
      let φₖ : (ι ⁻¹ᵁ Wₖ k).toScheme ⟶ (K.U (σ k).1).toScheme :=
        IsClosedImmersion.lift (chartJD π (K.U (σ k).1) (K.hU (σ k).1)) γₖ hker
      have hφₖ_fac : φₖ ≫ chartJD π (K.U (σ k).1) (K.hU (σ k).1) = γₖ :=
        IsClosedImmersion.lift_fac _ _ _

      have hstep4 : φₖ ≫ (K.U (σ k).1).ι = (ι ⁻¹ᵁ Wₖ k).ι ≫ p := by
        refine ext_of_isDominant_of_isSeparated π ?_ δ ?_
        ·
          simp only [Category.assoc]
          rw [← chartJ_over π (K.U (σ k).1) (K.hU (σ k).1),
            ← chartJD_ι π (K.U (σ k).1) (K.hU (σ k).1)]
          simp only [← Category.assoc]
          rw [hφₖ_fac, hγₖ_ι]
          simp only [Category.assoc]
          rw [ProjSpace.prodPr_comp_π, hover]
        ·

          have hδφ : δ ≫ φₖ = V.homOfLE (hU_le k) := by
            haveI : Mono (chartJD π (K.U (σ k).1) (K.hU (σ k).1)) := inferInstance
            rw [← cancel_mono (chartJD π (K.U (σ k).1) (K.hU (σ k).1)),
              Category.assoc, hφₖ_fac, ← cancel_mono D₀ₖ.ι, Category.assoc, hγₖ_ι,
              ← Category.assoc, hδ_ι, hψ_ιpr k, Category.assoc,
              chartJD_ι π (K.U (σ k).1) (K.hU (σ k).1)]
          simp only [← Category.assoc]
          rw [hδφ, Scheme.homOfLE_ι, hδ_ι, hψ_toImage_p]

      intro x hx
      show p.base x ∈ K.U (σ k).1
      have hx' : ((ι ⁻¹ᵁ Wₖ k).ι ≫ p).base ⟨x, hx⟩ = p.base x := rfl
      rw [← hx', ← hstep4]
      show (φₖ ≫ (K.U (σ k).1).ι).base ⟨x, hx⟩ ∈ (K.U (σ k).1 : Set V)
      rw [← Scheme.Opens.range_ι]
      exact ⟨φₖ.base ⟨x, hx⟩, rfl⟩
    ·

      intro x hx

      have hx' : x ∈ Set.range ⇑(pullback.fst p (K.U (σ k).1).ι).base := by
        rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
        exact hx
      obtain ⟨y, rfl⟩ := hx'
      show (pullback.fst p (K.U (σ k).1).ι ≫ ι ≫ ProjSpace.prodPr R e k).base y
        ∈ Proj.basicOpen _ (MvPolynomial.X (0 : Fin (e k + 1)))
      rw [h5b k]
      show (pullback.snd p (K.U (σ k).1).ι).base y
        ∈ chartJ π (K.U (σ k).1) (K.hU (σ k).1) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X (0 : Fin (e k + 1)))
      rw [chartJ_preimage_D0]; trivial

  haveI hι_closed : IsClosedImmersion ι := by
    rw [IsClosedImmersion.iff_isProper_and_mono]
    refine ⟨hι_proper, ⟨fun {T} a b hab => ?_⟩⟩

    suffices hp_eq : a ≫ p = b ≫ p by
      have hα_eq : a ≫ α = b ≫ α := by
        refine pullback.hom_ext ?_ ?_
        · simpa only [Category.assoc] using hp_eq
        · simpa only [Category.assoc] using hab
      exact (cancel_mono α).mp hα_eq

    have hTₖ_eq : ∀ k, a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1) = b ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1) := by
      intro k
      calc a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1)
          = a ⁻¹ᵁ (ι ⁻¹ᵁ Wₖ k) := by rw [h5c k]
        _ = (a ≫ ι) ⁻¹ᵁ Wₖ k := (Scheme.Hom.comp_preimage _ _ _).symm
        _ = (b ≫ ι) ⁻¹ᵁ Wₖ k := by rw [hab]
        _ = b ⁻¹ᵁ (ι ⁻¹ᵁ Wₖ k) := Scheme.Hom.comp_preimage _ _ _
        _ = b ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1) := by rw [h5c k]

    have hpUcov : ⨆ k : Fin m, p ⁻¹ᵁ K.U (σ k).1 = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hcov']; rfl
    have hTₖ_cov : ⨆ k : Fin m, a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hpUcov]; rfl

    have hlocal : ∀ k : Fin m,
        (a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1)).ι ≫ a ≫ p
          = (a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1)).ι ≫ b ≫ p := by
      intro k
      let Tₖ := a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1)

      have hTₖa : Tₖ ≤ (a ≫ p) ⁻¹ᵁ K.U (σ k).1 := le_of_eq (Scheme.Hom.comp_preimage _ _ _).symm
      have hTₖb : Tₖ ≤ (b ≫ p) ⁻¹ᵁ K.U (σ k).1 :=
        (hTₖ_eq k).le.trans (le_of_eq (Scheme.Hom.comp_preimage _ _ _).symm)
      let a' : Tₖ.toScheme ⟶ (K.U (σ k).1).toScheme := (a ≫ p).resLE _ Tₖ hTₖa
      let b' : Tₖ.toScheme ⟶ (K.U (σ k).1).toScheme := (b ≫ p).resLE _ Tₖ hTₖb
      have ha'_ι : a' ≫ (K.U (σ k).1).ι = Tₖ.ι ≫ a ≫ p := Scheme.Hom.resLE_comp_ι _ _
      have hb'_ι : b' ≫ (K.U (σ k).1).ι = Tₖ.ι ≫ b ≫ p := Scheme.Hom.resLE_comp_ι _ _

      have ha'_j : a' ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1)
          = Tₖ.ι ≫ a ≫ ι ≫ ProjSpace.prodPr R e k := by
        have key := (pullback.lift (Tₖ.ι ≫ a) a'
          (by rw [Category.assoc, ha'_ι])) ≫= h5b k
        rw [pullback.lift_snd_assoc, pullback.lift_fst_assoc, Category.assoc,
          Category.assoc] at key
        exact key.symm
      have hb'_j : b' ≫ chartJ π (K.U (σ k).1) (K.hU (σ k).1)
          = Tₖ.ι ≫ b ≫ ι ≫ ProjSpace.prodPr R e k := by
        have key := (pullback.lift (Tₖ.ι ≫ b) b'
          (by rw [Category.assoc, hb'_ι])) ≫= h5b k
        rw [pullback.lift_snd_assoc, pullback.lift_fst_assoc, Category.assoc,
          Category.assoc] at key
        exact key.symm

      have ha'b' : a' = b' := by
        haveI := hjₖ_mono k
        rw [← cancel_mono (chartJ π (K.U (σ k).1) (K.hU (σ k).1)),
          ha'_j, hb'_j]
        exact Tₖ.ι ≫= (hab =≫ ProjSpace.prodPr R e k)
      rw [← ha'_ι, ← hb'_ι, ha'b']

    refine (T.openCoverOfIsOpenCover (fun k => a ⁻¹ᵁ (p ⁻¹ᵁ K.U (σ k).1)) hTₖ_cov).hom_ext
      _ _ (fun k => ?_)
    exact hlocal k

  haveI hp_isoU : IsIso (pullback.snd p U.ι) := by
    haveI : IsSeparated p := hp_proper.toIsSeparated

    let β₀ : U.toScheme ⟶ pullback (ψ.toImage ≫ p) p :=
      pullback.lift (𝟙 _) ψ.toImage (Category.id_comp _)
    haveI : IsClosedImmersion β₀ := inferInstance
    let β : U.toScheme ⟶ pullback p U.ι :=
      β₀ ≫ (pullback.congrHom hψ_toImage_p rfl).hom ≫ (pullbackSymmetry _ _).hom
    haveI hβ_closed : IsClosedImmersion β :=
      MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
    have hβ_fst : β ≫ pullback.fst p U.ι = ψ.toImage := by
      simp only [β, β₀, Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    have hβ_snd : β ≫ pullback.snd p U.ι = 𝟙 _ := by
      simp only [β, β₀, Category.assoc, pullbackSymmetry_hom_comp_snd,
        pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

    haveI : IsOpenImmersion (pullback.fst p U.ι) := inferInstance

    have hβ_surj : Function.Surjective β := by
      rw [← Set.range_eq_univ, ← β.isClosedEmbedding.isClosed_range.closure_eq,
        ← Set.univ_subset_iff]
      intro x _

      have hfst_emb := (pullback.fst p U.ι).isOpenEmbedding
      have hdense' : closure (⇑(pullback.fst p U.ι).base '' Set.range ⇑β.base)
          = Set.univ := by
        rw [← Set.range_comp,
          show ⇑(pullback.fst p U.ι).base ∘ ⇑β.base = ⇑(β ≫ pullback.fst p U.ι).base from rfl,
          hβ_fst]
        exact hψ_dom.denseRange.closure_eq
      rw [hfst_emb.isEmbedding.isInducing.closure_eq_preimage_closure_image, hdense']
      exact Set.mem_preimage.mpr trivial
    haveI : Surjective β := ⟨hβ_surj⟩

    haveI : IsReduced (pullback p U.ι) := isReduced_of_isOpenImmersion (pullback.fst p U.ι)
    haveI : IsIso β := isIso_of_isClosedImmersion_of_surjective β
    rw [show pullback.snd p U.ι = inv β from (IsIso.inv_eq_of_hom_inv_id hβ_snd).symm]
    infer_instance

  exact ⟨{
    m := m, e := e, V' := V', p := p, ι := ι,
    hp_proper := hp_proper, hι_closed := hι_closed, hover := hover,
    U := U, hU_dense := hU_dense, hp_isoU := hp_isoU }⟩

end Headline

end ChowLemma
p2m_reactivate "P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry.ChowLemma"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry.ChowLemma P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry"

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : AlgebraicGeometry.Scheme.{u}}
    (π : V ⟶ AlgebraicGeometry.Spec (.of R)) [AlgebraicGeometry.IsProper π] [AlgebraicGeometry.IsIntegral V] :
    Nonempty (AlgebraicGeometry.ChowDatum π) :=
  AlgebraicGeometry.ChowLemma.chowDatum_nonempty π

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry.ChowLemma P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.AlgebraicGeometry"

end S_AlgebraicGeometry_ChowDatum_nonempty
end P2MW
export P2MW.S_AlgebraicGeometry_ChowDatum_nonempty (solution)
