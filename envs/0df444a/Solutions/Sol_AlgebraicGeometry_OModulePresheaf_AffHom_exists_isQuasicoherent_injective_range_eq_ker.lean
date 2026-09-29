-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4ac3fc81-9a90-50d7-81ea-d04a4f607c25

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mAffKerSol

p2m_open "AlgebraicGeometry.OModulePresheaf"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (.of A)}
variable {G F : OModulePresheaf q} (θ : OModulePresheaf.AffHom G F)

noncomputable def L (U : P.Opens) : Submodule A (G.obj U) where
  carrier := {x | ∀ (W : P.affineOpens) (hW : W.1 ≤ U), θ.app W (G.res hW x) = 0}
  add_mem' {x y} hx hy W hW := by
    rw [Set.mem_setOf_eq] at hx hy
    rw [map_add, map_add, hx W hW, hy W hW, add_zero]
  zero_mem' W hW := by rw [map_zero, map_zero]
  smul_mem' a x hx W hW := by
    rw [Set.mem_setOf_eq] at hx
    rw [map_smul, map_smul, hx W hW, smul_zero]

theorem mem_L {U : P.Opens} {x : G.obj U} :
    x ∈ L θ U ↔ ∀ (W : P.affineOpens) (hW : W.1 ≤ U), θ.app W (G.res hW x) = 0 :=
  Iff.rfl

theorem L_smul_mem (U : P.Opens) (a : Γ(P, U)) {x : G.obj U} (hx : x ∈ L θ U) : a • x ∈ L θ U := by
  intro W hW
  rw [G.res_smul, θ.app_smul, hx W hW, smul_zero]

theorem L_res {U U' : P.Opens} (hUU' : U ≤ U') {x : G.obj U'} (hx : x ∈ L θ U') :
    G.res hUU' x ∈ L θ U := by
  intro W hW
  rw [G.res_res]
  exact hx W (hW.trans hUU')

theorem L_eq_ker (U : P.affineOpens) : L θ U.1 = LinearMap.ker (θ.app U) := by
  ext x
  constructor
  · intro hx
    have hx' := hx U le_rfl
    rw [G.res_refl_apply] at hx'
    exact hx'
  · intro hx W hW
    rw [LinearMap.mem_ker] at hx
    rw [θ.naturality_apply hW x, hx, map_zero]

@[reducible] noncomputable def lModuleSections (U : P.Opens) : Module Γ(P, U) ↥(L θ U) :=
  letI : SMul Γ(P, U) ↥(L θ U) := ⟨fun a x => ⟨a • x.1, L_smul_mem θ U a x.2⟩⟩
  Function.Injective.module Γ(P, U) ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ Subtype.val_injective (fun _ _ => rfl)

noncomputable def K : OModulePresheaf q where
  obj U := ↥(L θ U)
  module U := inferInstance
  moduleSections U := lModuleSections θ U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    letI := lModuleSections θ U
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res {U U'} hle := (G.res hle).restrict fun x hx => L_res θ hle hx
  res_smul {U U'} hle a x := Subtype.ext (G.res_smul hle a x.1)
  res_refl U := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (G.res_refl U) x.1)
  res_comp {U U' U''} hle hle' := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (G.res_comp hle hle') x.1)

theorem K_obj (U : P.Opens) : (K θ).obj U = ↥(L θ U) := rfl

theorem K_res_val {U U' : P.Opens} (hle : U ≤ U') (x : (K θ).obj U') :
    ((K θ).res hle x).1 = G.res hle x.1 := rfl

theorem K_smul_val (U : P.Opens) (a : Γ(P, U)) (x : (K θ).obj U) : (a • x).1 = a • x.1 := rfl

noncomputable def ι : AffHom (K θ) G where
  app U := (L θ U.1).subtype
  app_smul _ _ _ := rfl
  naturality _ := rfl

theorem ι_app (U : P.affineOpens) (x : (K θ).obj U.1) : (ι θ).app U x = x.1 := rfl

theorem ι_injective (U : P.affineOpens) : Function.Injective ((ι θ).app U) :=
  Subtype.val_injective

theorem range_ι (U : P.affineOpens) : LinearMap.range ((ι θ).app U) = LinearMap.ker (θ.app U) := by
  rw [← L_eq_ker θ U]
  exact Submodule.range_subtype _

theorem isCoherent_K [IsLocallyNoetherian P] (hGc : G.IsCoherent) : (K θ).IsCoherent := by
  intro U
  haveI := hGc U
  haveI : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : IsNoetherian Γ(P, U.1) (G.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let f : (K θ).obj U.1 →ₗ[Γ(P, U.1)] G.obj U.1 :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem isQuasicoherent_K (hGq : G.IsQuasicoherent) (hFq : F.IsQuasicoherent) :
    (K θ).IsQuasicoherent := by
  intro U f
  obtain ⟨hG1, hG2⟩ := hGq U f
  obtain ⟨-, hF2⟩ := hFq U f
  have hDf : IsAffineOpen (P.basicOpen f) := U.2.basicOpen f
  set D : P.affineOpens := ⟨P.basicOpen f, hDf⟩ with hD
  refine ⟨?_, ?_⟩
  · intro x

    obtain ⟨n, y, hy⟩ := hG1 x.1

    have hx0 : θ.app D x.1 = 0 := by
      have := x.2 D le_rfl
      rwa [G.res_refl_apply] at this
    have hres0 : F.res (P.basicOpen_le f) (θ.app U y) = 0 := by
      rw [← θ.naturality_apply (U := D) (U' := U) (P.basicOpen_le f) y]
      show θ.app D (G.res (P.basicOpen_le f) y) = 0
      rw [hy, θ.app_smul, hx0, smul_zero]
    obtain ⟨m, hm⟩ := hF2 _ hres0
    have hmem : (f ^ m : Γ(P, U.1)) • y ∈ L θ U.1 := by
      rw [L_eq_ker, LinearMap.mem_ker, θ.app_smul, hm]
    refine ⟨m + n, ⟨(f ^ m : Γ(P, U.1)) • y, hmem⟩, Subtype.ext ?_⟩
    show G.res (P.basicOpen_le f) ((f ^ m : Γ(P, U.1)) • y) = _ • x.1
    rw [G.res_smul, hy, ← mul_smul, ← map_mul, ← pow_add]
  · intro y hy
    have hy0 : G.res (P.basicOpen_le f) y.1 = 0 := congrArg Subtype.val hy
    obtain ⟨n, hn⟩ := hG2 _ hy0
    exact ⟨n, Subtype.ext hn⟩

theorem main (hGq : G.IsQuasicoherent) (hFq : F.IsQuasicoherent) :
    ∃ (K : OModulePresheaf q) (ι : OModulePresheaf.AffHom K G),
      (IsLocallyNoetherian P → G.IsCoherent → K.IsCoherent) ∧ K.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Injective (ι.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.range (ι.app U) = LinearMap.ker (θ.app U)) :=
  ⟨K θ, ι θ, fun _ hGc => isCoherent_K θ hGc, isQuasicoherent_K θ hGq hFq, ι_injective θ, range_ι θ⟩

end P2mAffKerSol

theorem solution
    {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {G F : OModulePresheaf q} (hGq : G.IsQuasicoherent) (hFq : F.IsQuasicoherent)
    (θ : OModulePresheaf.AffHom G F) :
    ∃ (K : OModulePresheaf q) (ι : OModulePresheaf.AffHom K G),
      (IsLocallyNoetherian P → G.IsCoherent → K.IsCoherent) ∧ K.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Injective (ι.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.range (ι.app U) = LinearMap.ker (θ.app U)) :=
  P2mAffKerSol.main θ hGq hFq

end S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker (solution)
