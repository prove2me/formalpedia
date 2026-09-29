-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1e01abdc-9f7a-5ffd-baff-611f67c5e298

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace F1Aux

theorem preirreducibleSpace_of_two_opens {X : Type*} [TopologicalSpace X] {U₁ U₂ : Set X}
    (h₁ : IsPreirreducible U₁) (h₂ : IsPreirreducible U₂) (ho₁ : IsOpen U₁)
    (hcov : U₁ ∪ U₂ = Set.univ) (hmeet : (U₁ ∩ U₂).Nonempty) : PreirreducibleSpace X := by
  have key : ∀ w : Set X, IsOpen w → w.Nonempty → (U₁ ∩ w).Nonempty := by
    intro w hw ⟨x, hx⟩
    have hx' : x ∈ U₁ ∪ U₂ := hcov ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact ⟨x, h, hx⟩
    · obtain ⟨y, hy⟩ := hmeet
      have := h₂ w U₁ hw ho₁ ⟨x, h, hx⟩ ⟨y, hy.2, hy.1⟩
      obtain ⟨z, _, hzw, hz1⟩ := this
      exact ⟨z, hz1, hzw⟩
  refine PreirreducibleSpace.of_forall_nonempty_inter fun u v hu hv hune hvne => ?_
  obtain ⟨z, _, hz⟩ := h₁ u v hu hv (key u hu hune) (key v hv hvne)
  exact ⟨z, hz⟩

theorem isIntegral_and_nonempty_of_isAffineOpen_of_isDomain {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
    [IsDomain Γ(Y, U)] : IsIntegral (U : Scheme.{u}) ∧ Nonempty U := by
  haveI : IsIntegral (Spec Γ(Y, U)) := (affine_isIntegral_iff _).mpr inferInstance
  haveI hne : Nonempty (U : Scheme.{u}) := Nonempty.map hU.isoSpec.inv.base inferInstance
  exact ⟨isIntegral_of_isOpenImmersion hU.isoSpec.hom, hne⟩

theorem nonempty_of_isAffineOpen_of_nontrivial {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
    [Nontrivial Γ(Y, U)] : Nonempty U :=
  Nonempty.map hU.isoSpec.inv.base inferInstance

end F1Aux

open F1Aux in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (k : Type u) [CommRing k] [Algebra R k]
    [IsDomain (k ⊗[R] (𝒱.cover c).A0)] [IsDomain (k ⊗[R] (𝒱.cover c).A1)]
    [Nontrivial (k ⊗[R] (𝒱.cover c).A01)] :
    IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k)) ∧
      Nonempty (𝒱.pullback c k).U0 ∧ Nonempty (𝒱.pullback c k).U1 := by

  obtain ⟨e0, e1, e01, -, -, -, -, -, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c k
  set Y := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k) with hY
  set c' := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k) with hc'
  set 𝒲 := 𝒱.pullback c k with h𝒲

  haveI hd0 : IsDomain Γ(Y, 𝒲.U0) := by
    show IsDomain (𝒲.cover c').A0
    exact MulEquiv.isDomain _ e0.symm.toMulEquiv
  haveI hd1 : IsDomain Γ(Y, 𝒲.U1) := by
    show IsDomain (𝒲.cover c').A1
    exact MulEquiv.isDomain _ e1.symm.toMulEquiv
  haveI hn01 : Nontrivial Γ(Y, 𝒲.U0 ⊓ 𝒲.U1) := by
    show Nontrivial (𝒲.cover c').A01
    exact e01.symm.toEquiv.nontrivial

  obtain ⟨hi0, hne0⟩ := isIntegral_and_nonempty_of_isAffineOpen_of_isDomain 𝒲.U0 𝒲.isAffineOpen_U0
  obtain ⟨hi1, hne1⟩ := isIntegral_and_nonempty_of_isAffineOpen_of_isDomain 𝒲.U1 𝒲.isAffineOpen_U1
  have hne01 : Nonempty (𝒲.U0 ⊓ 𝒲.U1 : Y.Opens) :=
    nonempty_of_isAffineOpen_of_nontrivial (𝒲.U0 ⊓ 𝒲.U1) 𝒲.isAffineOpen_inf
  refine ⟨?_, hne0, hne1⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨?_, ?_⟩
  ·
    have hirr : ∀ (U : Y.Opens), IsIntegral (U : Scheme.{u}) → IsPreirreducible (U : Set Y) := by
      intro U hU
      haveI : IrreducibleSpace (U : Scheme.{u}) := inferInstance
      haveI : PreirreducibleSpace (U : Set Y) := by
        show PreirreducibleSpace (U : Scheme.{u}); infer_instance
      exact IsPreirreducible.of_subtype
    have hcov : (𝒲.U0 : Set Y) ∪ (𝒲.U1 : Set Y) = Set.univ := by
      rw [← TopologicalSpace.Opens.coe_sup, 𝒲.sup_eq_top, TopologicalSpace.Opens.coe_top]
    have hmeet : ((𝒲.U0 : Set Y) ∩ (𝒲.U1 : Set Y)).Nonempty := by
      obtain ⟨z⟩ := hne01
      exact ⟨z.1, z.2⟩
    haveI : PreirreducibleSpace Y :=
      preirreducibleSpace_of_two_opens (hirr _ hi0) (hirr _ hi1)
        𝒲.U0.isOpen hcov hmeet
    obtain ⟨y, -⟩ := hmeet
    exact ⟨⟨y⟩⟩
  ·
    have hU : TopologicalSpace.IsOpenCover (fun b : Bool => cond b 𝒲.U0 𝒲.U1) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      rintro y -
      have hy : y ∈ (𝒲.U0 ⊔ 𝒲.U1 : Y.Opens) := by rw [𝒲.sup_eq_top]; trivial
      rcases hy with h | h
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, h⟩
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, h⟩
    let 𝒰 : Y.OpenCover := Y.openCoverOfIsOpenCover (fun b : Bool => cond b 𝒲.U0 𝒲.U1) hU
    haveI hred : ∀ b : Bool, IsReduced ((cond b 𝒲.U0 𝒲.U1 : Y.Opens) : Scheme.{u}) := by
      intro b
      cases b
      · change IsReduced (𝒲.U1 : Scheme.{u}); haveI := hi1; infer_instance
      · change IsReduced (𝒲.U0 : Scheme.{u}); haveI := hi0; infer_instance
    haveI : ∀ b, IsReduced (𝒰.X b) := fun b => hred b
    exact IsReduced.of_openCover _ 𝒰

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct (solution)
