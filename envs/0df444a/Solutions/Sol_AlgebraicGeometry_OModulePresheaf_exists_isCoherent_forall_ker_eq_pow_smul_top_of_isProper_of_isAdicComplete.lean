-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7ce22c83-85d8-5786-aecf-e926f05142d7

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom
import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open TopologicalSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace GEDriver

theorem support_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).support = T :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal T)

theorem radical_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).radical = Scheme.IdealSheafData.vanishingIdeal T := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]

theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal T
  refine @IsReduced.of_openCover _ I.subschemeCover.openCover (fun U => ?_)
  have hrad : (I.ideal U).IsRadical := by
    rw [← Ideal.radical_eq_iff]
    have := congrArg (fun J : X.IdealSheafData => J.ideal U) (radical_vanishingIdeal T)
    simp [Scheme.IdealSheafData.radical_ideal] at this
    exact this
  haveI : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := (Ideal.isRadical_iff_quotient_reduced _).1 hrad
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  infer_instance

theorem irreducibleSpace_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) (hT : IsIrreducible (T : Set X)) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal T).subscheme :=
  Subtype.irreducibleSpace hT

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (T : Closeds X) (hT : IsIrreducible (T : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  haveI := isReduced_subscheme_vanishingIdeal T
  haveI := irreducibleSpace_subscheme_vanishingIdeal T hT
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem compactSpace_of_isProper {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    [IsProper q] : CompactSpace P :=
  QuasiCompact.compactSpace_of_compactSpace q

theorem isNoetherian_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : IsNoetherian P :=
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := compactSpace_of_isProper q
  {}

theorem noetherianSpace_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] : NoetherianSpace P :=
  haveI := isNoetherian_of_isProper q
  inferInstance

theorem isProper_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) : IsProper I.subschemeι := inferInstance

theorem isProper_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] : IsProper (f ≫ g) :=
  inferInstance

theorem isSeparated_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsSeparated f := inferInstance

theorem idealAnnihilates_ker_subschemeι {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (J : P.IdealSheafData) (F : ℕ → OModulePresheaf q)
    (hS : ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ J.ideal U ^ 1, ∀ x : (F k).obj U.1, a • x = 0) :
    ∀ k, OModulePresheaf.IdealAnnihilates q J.subschemeι.ker (F k) := by
  intro k U a ha x
  rw [Scheme.IdealSheafData.ker_subschemeι] at ha
  exact hS k U a (by rwa [pow_one]) x

private theorem _root_.GEDriver.nonempty_orderedAffineCover_of_compactSpace_univ (X : Scheme.{u}) [CompactSpace X] :
    Nonempty X.OrderedAffineCover := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  letI : LinearOrder ↥t := LinearOrder.lift' (Fintype.equivFin ↥t) (Fintype.equivFin ↥t).injective
  refine ⟨{ ι := ↥t, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨U, hUt, hxU⟩ := hx
  exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

p2m_export "GEDriver" "nonempty_orderedAffineCover_of_compactSpace_univ"

theorem exists_closeds_lt_sup_eq {X : Type*} [TopologicalSpace X] (T : Closeds X) (hne : (T : Set X).Nonempty)
    (hT : ¬ IsIrreducible (T : Set X)) : ∃ T₁ T₂ : Closeds X, T₁ < T ∧ T₂ < T ∧ T = T₁ ⊔ T₂ := by
  have hpre : ¬ IsPreirreducible (T : Set X) := fun h => hT ⟨hne, h⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  push Not at hpre
  obtain ⟨z₁, z₂, hz₁, hz₂, hsub, h₁, h₂⟩ := hpre
  refine ⟨T ⊓ ⟨z₁, hz₁⟩, T ⊓ ⟨z₂, hz₂⟩, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun h => h₁ ?_
    have : (T : Set X) ∩ z₁ = (T : Set X) := congrArg (fun S : Closeds X => (S : Set X)) h
    rw [← this]; exact Set.inter_subset_right
  · refine lt_of_le_of_ne inf_le_left fun h => h₂ ?_
    have : (T : Set X) ∩ z₂ = (T : Set X) := congrArg (fun S : Closeds X => (S : Set X)) h
    rw [← this]; exact Set.inter_subset_right
  · apply Closeds.ext
    show (T : Set X) = (T : Set X) ∩ z₁ ∪ (T : Set X) ∩ z₂
    rw [← Set.inter_union_distrib_left]
    exact (Set.inter_eq_left.2 hsub).symm

theorem vanishingIdeal_sup_pow_mul_le {X : Scheme.{u}} (T₁ T₂ : Closeds X) (U : X.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal T₂).ideal U ^ 1 * (Scheme.IdealSheafData.vanishingIdeal T₁).ideal U
      ≤ (Scheme.IdealSheafData.vanishingIdeal (T₁ ⊔ T₂)).ideal U ^ 1 := by
  rw [pow_one, pow_one, Scheme.IdealSheafData.vanishingIdeal_sup, Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
  exact Ideal.mul_le_inf.trans (by rw [inf_comm])

theorem vanishingIdeal_top_ideal_le_radical_bot {X : Scheme.{u}} (U : X.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).ideal U ≤ ((⊥ : X.IdealSheafData).ideal U).radical := by
  rw [Scheme.IdealSheafData.vanishingIdeal_top, ← Scheme.IdealSheafData.radical_bot,
    Scheme.IdealSheafData.radical_ideal]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]

structure AdicSys where
  F : ℕ → OModulePresheaf q
  hc : ∀ k, (F k).IsCoherent
  hq : ∀ k, (F k).IsQuasicoherent
  φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k)
  hs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U)
  hk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))

variable {I q}

def AdicSys.Algebraised (S : AdicSys I q) : Prop :=
  ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (S.F k)),
    G.IsCoherent ∧ G.IsQuasicoherent ∧
    (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
    (∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
    (∀ (k : ℕ) (U : P.affineOpens), (S.φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)

theorem algebraised_of_quot_of_ker (S : AdicSys I q) (𝓙 : P.IdealSheafData)
    (hQ : ∀ Q : AdicSys I q, (∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (Q.F k)) → Q.Algebraised)
    (hK : ∀ (K : AdicSys I q) (j : ∀ k, OModulePresheaf.AffHom (K.F k) (S.F k)),
      (∀ (k : ℕ) (U : P.affineOpens), (S.φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (K.φ k).app U) →
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.range ((j k).app U) = OModulePresheaf.idealPowSub q 𝓙 (S.F k) 1 U.1) →
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K.F (k + c)).obj U.1))) →
      K.Algebraised) :
    S.Algebraised := by
  classical

  obtain ⟨Q, τ, ε, hQc, hQq, hτs, hτk, hεc, hεs, hεk, hann⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
      I 𝓙 S.F S.hc S.hq S.φ S.hs S.hk
  let QS : AdicSys I q := ⟨Q, hQc, hQq, τ, hτs, hτk⟩

  obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, huj, hAR, hsurj, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I S.F S.hc S.hq S.φ S.hs S.hk Q hQc hQq τ hτs hτk ε hεc
  let KS : AdicSys I q := ⟨Ks, hKc, hKq, κ, hκs, hκk⟩
  have hjr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((j k).app U) = LinearMap.ker ((ε k).app U) := hsurj hεs

  obtain ⟨GQ, ψQ, hGQc, hGQq, hψQs, hψQk, hψQc⟩ := hQ QS hann
  obtain ⟨GK, ψK, hGKc, hGKq, hψKs, hψKk, hψKc⟩ :=
    hK KS j hjc (fun k U => (hjr k U).trans (hεk k U)) (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).2⟩)

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q S.F S.hc S.hq S.φ S.hs S.hk Q hQc hQq τ hτs hτk ε hεs hεc GQ hGQc hGQq ψQ hψQs hψQk hψQc
      GK hGKc hGKq (fun k => (j k).comp (ψK k))
      (by
        intro k U
        show (S.φ k).app U ∘ₗ ((j (k + 1)).app U ∘ₗ (ψK (k + 1)).app U)
          = (j k).app U ∘ₗ (ψK k).app U
        rw [← LinearMap.comp_assoc, hjc, LinearMap.comp_assoc, hψKc])
      (by
        intro k U
        show LinearMap.range ((j k).app U ∘ₗ (ψK k).app U) = LinearMap.ker ((ε k).app U)
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hψKs k U))]
        exact hjr k U)
      (by
        intro U
        obtain ⟨c, hc⟩ := hAR U
        refine ⟨c, fun k => ?_⟩
        intro x hx
        have hx' : (ψK (k + c)).app U x ∈ LinearMap.ker ((j (k + c)).app U) := by
          simpa [LinearMap.mem_ker] using hx
        have h1 : (ψK (k + c)).app U x ∈ I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) :=
          (hc k).2 hx'

        have hmap : Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
            = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hψKs (k + c) U)]
        have h2 : x ∈ Submodule.comap ((ψK (k + c)).app U)
            (Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))) := by
          rw [hmap]; exact h1
        rw [Submodule.comap_map_eq, hψKk] at h2
        have hle : I ^ (k + c + 1) • (⊤ : Submodule A (GK.obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact (sup_le le_rfl hle) h2)
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

def AdicSys.KilledBy (S : AdicSys I q) (𝓙 : P.IdealSheafData) (t : ℕ) : Prop :=
  ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ t, ∀ x : (S.F k).obj U.1, a • x = 0

theorem AdicSys.killedBy_one_iff (S : AdicSys I q) (𝓙 : P.IdealSheafData) :
    S.KilledBy 𝓙 1 ↔ ∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (S.F k) := by
  simp [AdicSys.KilledBy, OModulePresheaf.IdealAnnihilates, pow_one]

noncomputable abbrev idealOf (T : Closeds P) : P.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T

theorem AdicSys.algebraised_of_forall_eq_zero (S : AdicSys I q)
    (h : ∀ (k : ℕ) (U : P.affineOpens) (x : (S.F k).obj U.1), x = 0) : S.Algebraised := by
  have hcoh : (OModulePresheaf.zero q).IsCoherent := fun U => Module.Finite.of_finite
  have hqc : (OModulePresheaf.zero q).IsQuasicoherent := fun U f =>
    ⟨fun x => ⟨0, 0, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨OModulePresheaf.zero q, fun k => OModulePresheaf.AffHom.zeroFrom (S.F k), hcoh, hqc,
    fun k U y => ⟨0, by rw [h k U y]; exact map_zero _⟩, fun k U => ?_, fun k U => ?_⟩
  · haveI : Subsingleton (Submodule A ((OModulePresheaf.zero q).obj U.1)) := (Submodule.subsingleton_iff A).2 inferInstance
    exact Subsingleton.elim _ _
  · exact LinearMap.ext fun x => (h k U _).trans (h k U _).symm

theorem AdicSys.algebraised_of_killedBy_zero (S : AdicSys I q) (𝓙 : P.IdealSheafData) (h : S.KilledBy 𝓙 0) :
    S.Algebraised :=
  S.algebraised_of_forall_eq_zero (fun k U x => by
    have := h k U 1 (by rw [pow_zero, Ideal.one_eq_top]; trivial) x
    rwa [one_smul] at this)

theorem AdicSys.algebraised_of_killedBy_coe_eq_empty (S : AdicSys I q) (T : Closeds P) (hT : (T : Set P) = ∅)
    (h : S.KilledBy (idealOf T) 1) : S.Algebraised :=
  S.algebraised_of_forall_eq_zero (fun k U x => by
    have h1 : (1 : Γ(P, U.1)) ∈ (idealOf T).ideal U ^ 1 := by
      have hT' : T = ⊥ := Closeds.ext (by simpa using hT)
      subst hT'
      rw [pow_one, show idealOf (⊥ : Closeds P) = ⊤ from Scheme.IdealSheafData.vanishingIdeal_bot,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply]
      trivial
    have := h k U 1 h1 x
    rwa [one_smul] at this)

theorem stepC
    (T : Closeds P) (hTirr : IsIrreducible (T : Set P))
    (ih : ∀ T' : Closeds P, T' < T → ∀ (t : ℕ) (S : AdicSys I q), S.KilledBy (idealOf T') t → S.Algebraised)
    (S : AdicSys I q) (hS : S.KilledBy (idealOf T) 1) : S.Algebraised := by
  classical

  let Z : Scheme.{u} := (idealOf T).subscheme
  let i : Z ⟶ P := (idealOf T).subschemeι
  haveI : IsIntegral Z := isIntegral_subscheme_vanishingIdeal T hTirr
  haveI : IsProper i := isProper_subschemeι _
  haveI : IsProper (i ≫ q) := inferInstance
  obtain ⟨cd⟩ := AlgebraicGeometry.ChowDatumProj.nonempty_of (i ≫ q)
    (AlgebraicGeometry.ChowDatum.nonempty (i ≫ q))
  haveI : IsProper (cd.p ≫ i) := inferInstance
  haveI : IsSeparated (cd.p ≫ i) := inferInstance
  haveI : IsProper ((cd.p ≫ i) ≫ q) := inferInstance
  haveI : CompactSpace cd.V' := compactSpace_of_isProper ((cd.p ≫ i) ≫ q)
  obtain ⟨K'⟩ := AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ cd.V'
  have hSZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (S.F k) :=
    idealAnnihilates_ker_subschemeι q (idealOf T) S.F hS

  obtain ⟨F', φ', η, hF'c, hF'q, hφ's, hφ'k, hηs, hηV, hηU, hηφ, hβ, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom I q (cd.p ≫ i) S.F S.hc S.hq S.φ S.hs S.hk

  have hιq : cd.ιN ≫ ProjSpace.π A cd.Nd = (cd.p ≫ i) ≫ q := by rw [cd.hoverN, Category.assoc]
  obtain ⟨G', ψ', hG'c, hG'q, hψ's, hψ'k, hψ'c⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete I cd.ιN hιq F' hF'c hF'q φ' hφ's hφ'k

  obtain ⟨v, hvη, hvc⟩ : ∃ v : ∀ k, OModulePresheaf.AffHom (S.F k)
      (OModulePresheaf.cechPushforward (cd.p ≫ i) q K' (F' k)),
      (∀ (k : ℕ) (U₀ : P.affineOpens) (x : (S.F k).obj U₀.1) (jx : K'.ι),
        ((v k).app U₀ x).1 jx = η k U₀ (OModulePresheaf.AffHom.affineChart (cd.p ≫ i) q K' U₀ jx)
          (OModulePresheaf.cechPushforward.chart_le_preimage (cd.p ≫ i) K' U₀.1 jx) x) ∧
      (∀ (k : ℕ) (U₀ : P.affineOpens),
        ((φ' k).cechPushforward (cd.p ≫ i) q K').app U₀ ∘ₗ (v (k + 1)).app U₀ = (v k).app U₀ ∘ₗ (S.φ k).app U₀) :=
    by
      choose v hv using fun k =>
        AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
          q (cd.p ≫ i) K' (S.F k) (F' k) (η k) (hηs k) (hηV k) (hηU k)
      refine ⟨v, hv, fun k U₀ => ?_⟩
      apply LinearMap.ext
      intro x
      apply OModulePresheaf.cechPushforward.ext
      intro jx
      show (((φ' k).cechPushforward (cd.p ≫ i) q K').app U₀ ((v (k + 1)).app U₀ x)).1 jx
        = ((v k).app U₀ ((S.φ k).app U₀ x)).1 jx
      rw [OModulePresheaf.AffHom.coe_cechPushforward_app, hv, hv, hηφ]

  obtain ⟨hGPc, hGPq, Ps, π, ψP, ν, u, hPsc, hPsq, hπs, hπk, hψPs, hψPk, hψPc, hνc, hνψP, hνi, huc, hνu⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper I q (cd.p ≫ i) K' F' φ' G' hG'c hG'q ψ' hψ's hψ'k hψ'c S.F S.φ S.hs S.hk v hvc

  have hZne : Nonempty Z := by
    haveI := irreducibleSpace_subscheme_vanishingIdeal T hTirr
    infer_instance
  have hrange : Set.range i.base = (T : Set P) := by
    show Set.range (idealOf T).subschemeι.base = (T : Set P)
    rw [Scheme.IdealSheafData.range_subschemeι, support_vanishingIdeal]
  obtain ⟨T', hT'lt, hT'⟩ :=
    AlgebraicGeometry.exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
      i T hrange cd.U (cd.hU_dense.nonempty)
  obtain ⟨N, hcoker, hker⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
      I q i cd.p K' cd.U cd.hp_isoU T' hT' S.F S.hc S.hq S.φ S.hs S.hk hSZ F' φ' η hηs hηV hηU hηφ hβ
      G' hG'c hG'q ψ' hψ's hψ'k hψ'c v hvη Ps hPsc hPsq π hπs hπk ψP hψPs hψPk hψPc ν hνc hνψP hνi u huc hνu

  obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, huj, hAR, -, hCc, hCq, hγs, hγk, hθc, hθs, hθk⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I S.F S.hc S.hq S.φ S.hs S.hk Ps hPsc hPsq π hπs hπk u huc

  obtain ⟨GK, ψK, hGKc, hGKq, hψKs, hψKk, hψKc⟩ :=
    ih T' hT'lt N ⟨Ks, hKc, hKq, κ, hκs, hκk⟩
      (AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
        I S.F S.φ S.hs S.hk Ks κ hκs hκk j hjc (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).2⟩)
        Ps u huj (idealOf T') N hker)
  obtain ⟨GC, ψC, hGCc, hGCq, hψCs, hψCk, hψCc⟩ :=
    ih T' hT'lt N ⟨Cs, hCc, hCq, γ, hγs, hγk⟩ (by
      intro k U a ha z
      obtain ⟨y, rfl⟩ := hθs k U z
      obtain ⟨x, hx⟩ := hcoker k U a ha y
      rw [← (θ k).app_smul, ← hx]
      have hmem : (u k).app U x ∈ LinearMap.ker ((θ k).app U) := by
        rw [hθk]; exact LinearMap.mem_range_self _ x
      exact LinearMap.mem_ker.mp hmem)

  obtain ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, huEc, huEr, huEi⟩ :
      ∃ (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k)),
        (∀ k, (E k).IsCoherent) ∧ (∀ k, (E k).IsQuasicoherent) ∧
        (∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((τ k).app W)) ∧
        (∀ (k : ℕ) (W : P.affineOpens),
          LinearMap.ker ((τ k).app W) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj W.1))) ∧
        ∃ ε : ∀ k, OModulePresheaf.AffHom (S.F k) (E k),
        (∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ε k).app W)) ∧
        (∀ (k : ℕ) (W : P.affineOpens), (τ k).app W ∘ₗ (ε (k + 1)).app W = (ε k).app W ∘ₗ (S.φ k).app W) ∧
        (∀ (k : ℕ) (W : P.affineOpens), LinearMap.ker ((ε k).app W) = LinearMap.range ((j k).app W)) ∧
        ∃ uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k),
        (∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (uE (k + 1)).app W = (uE k).app W ∘ₗ (τ k).app W) ∧
        (∀ (k : ℕ) (W : P.affineOpens), LinearMap.range ((uE k).app W) = LinearMap.ker ((θ k).app W)) ∧
        (∀ W : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
          LinearMap.ker ((uE (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj W.1))) :=
    by
      obtain ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, -, huEc, huEr, huEi⟩ :=
        AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
          I S.F S.hc S.hq S.φ S.hs S.hk Ks hKq κ hκs j hjc Ps π u huc huj
          (fun U => ⟨(hAR U).choose, fun k => ((hAR U).choose_spec k).1⟩)
      exact ⟨E, τ, hEc, hEq, hτs, hτk, ε, hεs, hεc, hεk, uE, huEc, fun k U => (huEr k U).trans (hθk k U).symm, huEi⟩

  obtain ⟨GE, ψE, hGEc, hGEq, hψEs, hψEk, hψEc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q E hEc hEq τ hτs hτk Ps hPsc hPsq π hπs hπk Cs hCc hCq γ hγs hγk θ hθc uE huEc huEr huEi
      (OModulePresheaf.cechPushforward (cd.p ≫ i) q K' G') hGPc hGPq ψP hψPs hψPk hψPc GC hGCc hGCq ψC hψCs hψCk hψCc

  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q S.F S.hc S.hq S.φ S.hs S.hk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc
      GK hGKc hGKq (fun k => (j k).comp (ψK k))
      (by
        intro k U
        show (S.φ k).app U ∘ₗ ((j (k + 1)).app U ∘ₗ (ψK (k + 1)).app U) = (j k).app U ∘ₗ (ψK k).app U
        rw [← LinearMap.comp_assoc, hjc, LinearMap.comp_assoc, hψKc])
      (by
        intro k U
        show LinearMap.range ((j k).app U ∘ₗ (ψK k).app U) = LinearMap.ker ((ε k).app U)
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hψKs k U))]
        exact (hεk k U).symm)
      (by
        intro U
        obtain ⟨c, hc⟩ := hAR U
        refine ⟨c, fun k => ?_⟩
        intro x hx
        have hx' : (ψK (k + c)).app U x ∈ LinearMap.ker ((j (k + c)).app U) := by
          simpa [LinearMap.mem_ker] using hx
        have h1 := (hc k).2 hx'
        have hmap : Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
            = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hψKs (k + c) U)]
        have h2 : x ∈ Submodule.comap ((ψK (k + c)).app U)
            (Submodule.map ((ψK (k + c)).app U) (I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))) := by
          rw [hmap]; exact h1
        rw [Submodule.comap_map_eq, hψKk] at h2
        have hle : I ^ (k + c + 1) • (⊤ : Submodule A (GK.obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        exact (sup_le le_rfl hle) h2)
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

theorem algebraised_of_killedBy
    (T : Closeds P) (t : ℕ) (S : AdicSys I q) (hS : S.KilledBy (idealOf T) t) : S.Algebraised := by
  haveI : NoetherianSpace P := noetherianSpace_of_isProper q
  induction T using (wellFounded_lt (α := Closeds P)).induction generalizing t S with
  | _ T ih =>

  have h1 : ∀ S : AdicSys I q, S.KilledBy (idealOf T) 1 → S.Algebraised := by
    intro S hS1
    by_cases hirr : IsIrreducible (T : Set P)
    · exact stepC T hirr ih S hS1
    ·
      by_cases hT : (T : Set P) = ∅
      · exact AdicSys.algebraised_of_killedBy_coe_eq_empty S T hT hS1
      ·
        obtain ⟨T₁, T₂, hT₁, hT₂, hT12⟩ : ∃ T₁ T₂ : Closeds P, T₁ < T ∧ T₂ < T ∧ T = T₁ ⊔ T₂ := by
          exact exists_closeds_lt_sup_eq T (Set.nonempty_iff_ne_empty.2 hT) hirr
        refine algebraised_of_quot_of_ker S (idealOf T₁)
          (fun Q hQ => ih T₁ hT₁ 1 Q ((Q.killedBy_one_iff _).2 hQ)) ?_
        intro K j hjc hjr hji
        refine ih T₂ hT₂ 1 K ?_
        exact AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
          I S.F S.φ S.hs S.hk K.F K.φ K.hs K.hk j hjc (idealOf T) (idealOf T₁) (idealOf T₂) 1 1 hjr hji
          (fun U => by rw [hT12]; exact vanishingIdeal_sup_pow_mul_le T₁ T₂ U) hS1

  induction t generalizing S with
  | zero =>
    exact AdicSys.algebraised_of_killedBy_zero S _ hS
  | succ t iht =>
    refine algebraised_of_quot_of_ker S (idealOf T)
      (fun Q hQ => h1 Q ((Q.killedBy_one_iff _).2 hQ)) ?_
    intro K j hjc hjr hji
    refine iht K ?_
    exact AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
      I S.F S.φ S.hs S.hk K.F K.φ K.hs K.hk j hjc (idealOf T) (idealOf T) (idealOf T) (t + 1) t hjr hji
      (fun U => by rw [pow_succ]) hS

end GEDriver

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  haveI : IsNoetherian P := GEDriver.isNoetherian_of_isProper q

  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_ideal_pow_le_of_forall_le_radical
    (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds P)) ⊥ (GEDriver.vanishingIdeal_top_ideal_le_radical_bot)
  exact GEDriver.algebraised_of_killedBy (I := I) (q := q) ⊤ e ⟨F, hc, hq, φ, hφs, hφk⟩ (by
    intro k U a ha x
    have ha' : a ∈ (⊥ : P.IdealSheafData).ideal U := he U ha
    rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot] at ha'
    rw [ha', zero_smul])

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete (solution)
