-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a7e87baa-4071-5412-b296-6e4d2df43a17

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso

set_option autoImplicit false

noncomputable section

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules OModulePresheaf.ofModules OModulePresheaf OModulePresheaf.cechFinite_iff"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "ofModules ofModules_algebraMap_smul cochain d d_apply H0 HSucc CechFinite cechFinite_iff res module obj"
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"
namespace IsoTransfer

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

structure LinIso (F G : OModulePresheaf π) where
  app : ∀ U : V.Opens, F.obj U ≃ₗ[R] G.obj U
  res_app : ∀ {U U' : V.Opens} (h : U ≤ U') (x : F.obj U'), G.res h (app U' x) = app U (F.res h x)

variable {F G : OModulePresheaf π} (φ : LinIso F G) (K : V.OrderedAffineCover)

def cochainEquiv (i : ℕ) : F.cochain K i ≃ₗ[R] G.cochain K i :=
  LinearEquiv.piCongrRight fun s => φ.app (K.inter s)

theorem cochainEquiv_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx i) :
    cochainEquiv φ K i c s = φ.app (K.inter s) (c s) := rfl

theorem d_cochainEquiv (i : ℕ) (c : F.cochain K i) :
    G.d K i (cochainEquiv φ K i c) = cochainEquiv φ K (i + 1) (F.d K i c) := by
  funext s
  rw [d_apply, cochainEquiv_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cochainEquiv_apply, φ.res_app, map_zsmul]

theorem d_comp_cochainEquiv (i : ℕ) :
    G.d K i ∘ₗ (cochainEquiv φ K i).toLinearMap = (cochainEquiv φ K (i + 1)).toLinearMap ∘ₗ F.d K i :=
  LinearMap.ext fun c => d_cochainEquiv φ K i c

theorem map_ker (i : ℕ) :
    Submodule.map (cochainEquiv φ K i).toLinearMap (LinearMap.ker (F.d K i)) = LinearMap.ker (G.d K i) := by
  ext c
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have : c = cochainEquiv φ K i ((cochainEquiv φ K i).symm c) := ((cochainEquiv φ K i).apply_symm_apply c).symm
    rw [this, d_cochainEquiv, h, map_zero]
  · intro h
    apply (cochainEquiv φ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, h, map_zero]

def H0Equiv : F.H0 K ≃ₗ[R] G.H0 K :=
  (cochainEquiv φ K 0).ofSubmodules _ _ (map_ker φ K 0)

def kerEquiv (i : ℕ) : LinearMap.ker (F.d K (i + 1)) ≃ₗ[R] LinearMap.ker (G.d K (i + 1)) :=
  (cochainEquiv φ K (i + 1)).ofSubmodules _ _ (map_ker φ K (i + 1))

theorem kerEquiv_apply_coe (i : ℕ) (x : LinearMap.ker (F.d K (i + 1))) :
    ((kerEquiv φ K i x : LinearMap.ker (G.d K (i + 1))) : G.cochain K (i + 1)) = cochainEquiv φ K (i + 1) x := rfl

theorem map_boundaries (i : ℕ) :
    Submodule.map (kerEquiv φ K i).toLinearMap
        ((LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype)
      = (LinearMap.range (G.d K i)).comap (LinearMap.ker (G.d K (i + 1))).subtype := by
  ext y
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨cochainEquiv φ K i c, ?_⟩
    rw [d_cochainEquiv, hc]

    have : kerEquiv φ K i ((kerEquiv φ K i).symm y) = y := (kerEquiv φ K i).apply_symm_apply y
    exact (congrArg (fun z : LinearMap.ker (G.d K (i + 1)) => (z : G.cochain K (i + 1))) this)
  · rintro ⟨c, hc⟩
    refine ⟨(cochainEquiv φ K i).symm c, ?_⟩
    apply (cochainEquiv φ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, hc]
    exact (congrArg (fun z : LinearMap.ker (G.d K (i + 1)) => (z : G.cochain K (i + 1)))
      ((kerEquiv φ K i).apply_symm_apply y)).symm

def HSuccEquiv (i : ℕ) : F.HSucc K i ≃ₗ[R] G.HSucc K i :=
  Submodule.Quotient.equiv _ _ (kerEquiv φ K i) (map_boundaries φ K i)

include φ in
private theorem _root_.AlgebraicGeometry.OModulePresheaf.IsoTransfer.cechFinite_iff : F.CechFinite K ↔ G.CechFinite K := by
  rw [OModulePresheaf.cechFinite_iff, OModulePresheaf.cechFinite_iff]
  exact and_congr (⟨fun _ => Module.Finite.equiv (H0Equiv φ K), fun _ => Module.Finite.equiv (H0Equiv φ K).symm⟩)
    (forall_congr' fun i => ⟨fun _ => Module.Finite.equiv (HSuccEquiv φ K i),
      fun _ => Module.Finite.equiv (HSuccEquiv φ K i).symm⟩)

p2m_export "AlgebraicGeometry.OModulePresheaf.IsoTransfer" "cechFinite_iff"

def ofIso {M M' : V.Modules} (e : M ≅ M') : LinIso (ofModules π M) (ofModules π M') where
  app U :=
    { toFun := fun x => (e.hom.app U).hom x
      invFun := fun y => (e.inv.app U).hom y
      map_add' := fun x y => (e.hom.app U).hom.map_add x y
      map_smul' := fun r x => by

        rw [ofModules_algebraMap_smul, ofModules_algebraMap_smul, RingHom.id_apply]
        exact Scheme.Modules.Hom.app_smul e.hom _ _
      left_inv := fun x => by
        show (e.hom.app U ≫ e.inv.app U).hom x = x
        rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        show (e.inv.app U ≫ e.hom.app U).hom y = y
        rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }
  res_app {U U'} h x := by
    show (M'.presheaf.map (homOfLE h).op) ((e.hom.app U').hom x) = (e.hom.app U).hom ((M.presheaf.map (homOfLE h).op) x)
    have hnat := e.hom.mapPresheaf.naturality (homOfLE h).op
    have hx := ConcreteCategory.congr_hom hnat x
    simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
    exact hx.symm

end IsoTransfer
end AlgebraicGeometry.OModulePresheaf

open AlgebraicGeometry.OModulePresheaf.IsoTransfer in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M M' : V.Modules} (e : M ≅ M')
    (K : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M').H0 K) ∧
      (∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R] (OModulePresheaf.ofModules π M').HSucc K i)) ∧
      ((OModulePresheaf.ofModules π M).CechFinite K ↔ (OModulePresheaf.ofModules π M').CechFinite K) :=
  ⟨⟨H0Equiv (ofIso (π := π) e) K⟩, fun i => ⟨HSuccEquiv (ofIso (π := π) e) K i⟩, cechFinite_iff (ofIso (π := π) e) K⟩

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso (solution)
