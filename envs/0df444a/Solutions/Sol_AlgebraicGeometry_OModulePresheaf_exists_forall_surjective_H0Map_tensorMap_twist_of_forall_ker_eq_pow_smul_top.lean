-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8a24d8a7-0465-58cd-b96b-df1fb092a2af

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mUnifLift

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) [IsSeparated q]
  (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
  (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
  (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
  (hφk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))

omit [IsNoetherianRing A] [IsSeparated q] in
include hιq in
theorem locallyOfFiniteType : LocallyOfFiniteType q := by
  subst hιq; infer_instance

omit [IsNoetherianRing A] [IsSeparated q] in

theorem affHom_tensor_ext {F₁ G F₂ : OModulePresheaf q} (α β : OModulePresheaf.AffHom (F₁.tensor G) F₂)
    (h : ∀ (U : P.affineOpens) (x : F₁.obj U.1) (y : G.obj U.1),
      α.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ y) = β.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ y)) :
    α = β := by
  refine OModulePresheaf.AffHom.ext_app fun U => LinearMap.ext fun t => ?_
  have key : α.appSections U = β.appSections U := TensorProduct.ext' fun x y => h U x y
  exact LinearMap.congr_fun key t

include hιq hc hq hφs hφk in
theorem main :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
      Function.Surjective
        ((OModulePresheaf.AffHom.tensorMap (φ k) (OModulePresheaf.AffHom.id (ProjSpace.twist q ι d))).H0Map
          (ProjSpace.stdCoverPullback ι)) := by
  haveI : LocallyOfFiniteType q := locallyOfFiniteType ι hιq
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q

  choose K j hKc hKq hji hjr using
    fun k => AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker
      (hq (k + 1)) (hq k) (φ k)
  have hKc' : ∀ k, (K k).IsCoherent := fun k => hKc k inferInstance (hc (k + 1))

  obtain ⟨d₀, hd₀⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
      I ι hιq F hc hq φ hφs hφk K hKc' hKq j hji hjr
  refine ⟨d₀, fun d hd k => ?_⟩

  let S : OModulePresheaf.AffSES (K k) (F (k + 1)) (F k) :=
    { inc := j k, proj := φ k, injective := hji k, surjective := hφs k, exact := hjr k }

  set T : OModulePresheaf q := ProjSpace.twist q ι d
  have hflat : ∀ U : P.affineOpens, Module.Flat Γ(P, U.1) (T.obj U.1) :=
    (AlgebraicGeometry.ProjSpace.isCoherent_twist_and_flat q ι d).2
  obtain ⟨S', hS'⟩ := AlgebraicGeometry.OModulePresheaf.exists_affSES_tensor_of_flat S T hflat

  have hproj : S'.proj = OModulePresheaf.AffHom.tensorMap (φ k) (OModulePresheaf.AffHom.id T) := by
    refine affHom_tensor_ext _ _ fun U x y => ?_
    rw [(hS' U).2 x y, OModulePresheaf.AffHom.tensorMap_app_tmul]
    rfl

  obtain ⟨δ₀, δ, hδ₀, -, -, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom S' (ProjSpace.stdCoverPullback ι)
  haveI : Subsingleton (((K k).tensor T).HSucc (ProjSpace.stdCoverPullback ι) 0) := hd₀ d hd k 0
  have hker : LinearMap.ker δ₀ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
  have hrange : LinearMap.range (S'.proj.H0Map (ProjSpace.stdCoverPullback ι)) = ⊤ :=
    top_le_iff.mp (hker ▸ hδ₀)
  rw [hproj] at hrange
  exact LinearMap.range_eq_top.mp hrange

end P2mUnifLift

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) [IsSeparated q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
      Function.Surjective
        ((OModulePresheaf.AffHom.tensorMap (φ k) (OModulePresheaf.AffHom.id (ProjSpace.twist q ι d))).H0Map
          (ProjSpace.stdCoverPullback ι)) :=
  P2mUnifLift.main I ι hιq F hc hq φ hφs hφk

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top (solution)
