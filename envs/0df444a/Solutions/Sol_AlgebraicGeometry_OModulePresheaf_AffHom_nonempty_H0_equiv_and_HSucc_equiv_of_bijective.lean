-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8eef7de7-021e-508b-b602-dbc6d8254c31

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mCechIso

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
variable {F G : OModulePresheaf π} (φ : AffHom F G) (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U))
variable (K : V.OrderedAffineCover)

include hφ in
theorem cochainMap_bijective (i : ℕ) : Function.Bijective (φ.cochainMap K i) := by
  constructor
  · intro x y h
    exact funext fun s => (hφ (K.affineInter π s)).1 (congrFun h s)
  · intro y
    exact ⟨fun s => ((hφ (K.affineInter π s)).2 (y s)).choose,
      funext fun s => ((hφ (K.affineInter π s)).2 (y s)).choose_spec⟩

noncomputable def cochainEquiv (i : ℕ) : F.cochain K i ≃ₗ[R] G.cochain K i :=
  LinearEquiv.ofBijective (φ.cochainMap K i) (cochainMap_bijective φ hφ K i)

theorem cochainEquiv_apply (i : ℕ) (x : F.cochain K i) : cochainEquiv φ hφ K i x = φ.cochainMap K i x := rfl

theorem d_cochainEquiv (i : ℕ) (x : F.cochain K i) :
    G.d K i (cochainEquiv φ hφ K i x) = cochainEquiv φ hφ K (i + 1) (F.d K i x) := by
  rw [cochainEquiv_apply, cochainEquiv_apply, ← LinearMap.comp_apply, ← φ.cochainMap_comp_d K i]
  rfl

theorem map_ker (i : ℕ) :
    (LinearMap.ker (F.d K i)).map (cochainEquiv φ hφ K i : F.cochain K i →ₗ[R] G.cochain K i) =
      LinearMap.ker (G.d K i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearMap.mem_ker, LinearEquiv.coe_coe, d_cochainEquiv, LinearMap.mem_ker.mp hx, map_zero]
  · intro hy
    refine ⟨(cochainEquiv φ hφ K i).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply (cochainEquiv φ hφ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, LinearMap.mem_ker.mp hy, map_zero]

noncomputable def kerEquiv (i : ℕ) : LinearMap.ker (F.d K i) ≃ₗ[R] LinearMap.ker (G.d K i) :=
  LinearEquiv.ofSubmodules (cochainEquiv φ hφ K i) _ _ (map_ker φ hφ K i)

theorem kerEquiv_coe (i : ℕ) (x : LinearMap.ker (F.d K i)) :
    (kerEquiv φ hφ K i x : G.cochain K i) = φ.cochainMap K i x := rfl

theorem map_bdry (i : ℕ) :
    ((LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype).map
        (kerEquiv φ hφ K (i + 1) : LinearMap.ker (F.d K (i + 1)) →ₗ[R] LinearMap.ker (G.d K (i + 1))) =
      (LinearMap.range (G.d K i)).comap (LinearMap.ker (G.d K (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨c, hc⟩, rfl⟩
    refine ⟨cochainEquiv φ hφ K i c, ?_⟩
    rw [LinearEquiv.coe_coe, kerEquiv_coe, d_cochainEquiv, hc]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨(kerEquiv φ hφ K (i + 1)).symm y, ⟨(cochainEquiv φ hφ K i).symm c, ?_⟩,
      LinearEquiv.apply_symm_apply _ _⟩
    apply (cochainEquiv φ hφ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, hc]
    have := congrArg (fun z : LinearMap.ker (G.d K (i + 1)) => (z : G.cochain K (i + 1)))
      (LinearEquiv.apply_symm_apply (kerEquiv φ hφ K (i + 1)) y)
    exact this.symm

noncomputable def HSuccEquiv (i : ℕ) : F.HSucc K i ≃ₗ[R] G.HSucc K i :=
  Submodule.Quotient.equiv _ _ (kerEquiv φ hφ K (i + 1)) (map_bdry φ hφ K i)

include φ hφ in
theorem main :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) :=
  ⟨⟨kerEquiv φ hφ K 0⟩, fun i => ⟨HSuccEquiv φ hφ K i⟩⟩

end P2mCechIso

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F G : OModulePresheaf π} (φ : OModulePresheaf.AffHom F G)
    (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) (K : V.OrderedAffineCover) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) :=
  P2mCechIso.main φ hφ K

end S_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective (solution)
