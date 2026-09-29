-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2711b789-c1b3-5e92-9436-a84c8b82ce64

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint
import Theorems.Thm_AlgebraicGeometry_Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FiniteStabiliserSketch

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))

abbrev Pt := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

noncomputable abbrev T [GrpObj (Over.mk t)] (a : Pt t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left

noncomputable abbrev pt (z : Pt t) : X := z.left.base (IsLocalRing.closedPoint k)

theorem eq_singleton_of_finite_inter_closedPoints {Y : Type*} [TopologicalSpace Y] [JacobsonSpace Y]
    {Z : Set Y} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hfin : (Z ∩ closedPoints Y).Finite)
    {x : Y} (hxZ : x ∈ Z) (hxc : IsClosed ({x} : Set Y)) : Z = {x} := by
  have hdisc : IsDiscrete (Z ∩ closedPoints Y) :=
    hfin.isDiscrete_of_subset_closedPoints Set.inter_subset_right
  have hirr : IsIrreducible (Z ∩ closedPoints Y) := by
    rwa [← isIrreducible_iff_closure,
      JacobsonSpace.closure_inter_closedPoints_eq_closure hZc.isLocallyClosed, isIrreducible_iff_closure]
  have hsubs : (Z ∩ closedPoints Y).Subsingleton := hdisc.subsingleton_of_isPreirreducible hirr.isPreirreducible
  have h1 : Z ∩ closedPoints Y = {x} := hsubs.eq_singleton_of_mem ⟨hxZ, hxc⟩
  calc Z = closure Z := hZc.closure_eq.symm
    _ = closure (Z ∩ closedPoints Y) :=
        (JacobsonSpace.closure_inter_closedPoints_eq_closure hZc.isLocallyClosed).symm
    _ = {x} := by rw [h1, hxc.closure_eq]

end FiniteStabiliserSketch

open FiniteStabiliserSketch in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (hK : Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0})
    {N : ℕ} (𝔓 : (L.tensorPow 3).ProjPresentation t N) :
    IsFinite 𝔓.toProj := by

  haveI : IsProper (𝔓.toProj ≫ ProjSpace.π k N) := by rw [𝔓.toProj_π]; infer_instance
  haveI : IsProper 𝔓.toProj := IsProper.of_comp 𝔓.toProj (ProjSpace.π k N)

  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t

  by_contra hfin
  have hnlqf : ¬ LocallyQuasiFinite 𝔓.toProj := fun h => hfin (IsFinite.of_isProper_of_locallyQuasiFinite _)

  obtain ⟨x, hxc, hx⟩ : ∃ x : X, IsClosed ({x} : Set X) ∧ ¬ 𝔓.toProj.QuasiFiniteAt x := by
    have hne : ((𝔓.toProj.quasiFiniteLocus : Set X)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      intro htop
      apply hnlqf
      rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
      exact TopologicalSpace.Opens.ext (htop.trans TopologicalSpace.Opens.coe_top.symm)
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace t
    obtain ⟨x, hx, hxc⟩ := IsClosed.exists_closed_singleton (𝔓.toProj.quasiFiniteLocus.isOpen.isClosed_compl) hne
    exact ⟨x, hxc, fun h => hx (Scheme.Hom.mem_quasiFiniteLocus.mpr h)⟩

  obtain ⟨Z, hZc, hZi, hxZ, hZne, hZfib⟩ :=
    Scheme.Hom.exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt 𝔓.toProj x hx
  have hyc : IsClosed ({𝔓.toProj.base x} : Set _) := by
    have := (𝔓.toProj.isClosedMap) _ hxc
    rwa [Set.image_singleton] at this
  have hZy : Z ⊆ 𝔓.toProj.base ⁻¹' {𝔓.toProj.base x} := by rwa [hyc.closure_eq] at hZfib

  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t x hxc

  set D : Set X := ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) with hD
  have hDc : IsClosed D := (Scheme.Modules.zeroSchemeIdeal θ).support.isClosed

  have hdich : ∀ a b : Pt t,
      Z ⊆ ((T t a).base ⁻¹' D ∪ (T t b).base ⁻¹' D ∪ (T t (a * b)⁻¹).base ⁻¹' D) ∨
        Disjoint Z ((T t a).base ⁻¹' D ∪ (T t b).base ⁻¹' D ∪ (T t (a * b)⁻¹).base ⁻¹' D) := by
    intro a b
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq k t L hL hsq θ a b
    have h3 := Scheme.Modules.ProjPresentation.subset_support_zeroSchemeIdeal_or_disjoint k t (L.tensorPow 3)
      (hL.tensorPow 3) 𝔓 Z hZc hZi (𝔓.toProj.base x) hyc hZy s
    rw [hs] at h3
    exact h3

  have hvan : ∀ w : Pt t, Scheme.Modules.pullbackSection w.left θ = 0 ↔ pt t w ∈ D := fun w =>
    hL.pullbackSection_eq_zero_iff_mem_support θ w.left

  have hstab : ∀ z' : Pt t, pt t z' ∈ Z → ∀ w : Pt t, pt t w ∈ D ↔ pt t (w * (z⁻¹ * z')) ∈ D := by
    intro z' hz' w
    by_cases hDu : D = Set.univ
    · simp [hDu]
    exact Scheme.forall_mem_iff_of_subset_union_preimage_or_disjoint k t D hDc hDu Z hZc hZi hdich z z'
      (hz ▸ hxZ) hz' w

  have hsub : Z ∩ closedPoints X ⊆
      (fun κ : Pt t => pt t (z * κ)) ''
        {x : Pt t | ∀ w : Pt t,
          Scheme.Modules.pullbackSection w.left θ = 0 ↔ Scheme.Modules.pullbackSection (w * x).left θ = 0} := by
    rintro x' ⟨hx'Z, hx'c⟩
    obtain ⟨z', hz'⟩ :=
      AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t x' hx'c
    have hz'Z : pt t z' ∈ Z := by rw [show pt t z' = x' from hz']; exact hx'Z
    refine ⟨z⁻¹ * z', fun w => (hvan w).trans ((hstab z' hz'Z w).trans (hvan _).symm), ?_⟩
    show pt t (z * (z⁻¹ * z')) = x'
    rw [mul_inv_cancel_left]
    exact hz'
  have hZfin : (Z ∩ closedPoints X).Finite := (hK.image _).subset hsub

  exact hZne (eq_singleton_of_finite_inter_closedPoints hZc hZi hZfin hxZ hxc)

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff (solution)
