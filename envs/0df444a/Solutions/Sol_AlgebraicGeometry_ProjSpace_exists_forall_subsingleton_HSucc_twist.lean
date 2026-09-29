-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/20377a79-c5b8-5c17-a54f-779c884b8884

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
import Theorems.Thm_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated
import Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsFinite Spec Scheme Proj IsAffineHom ProjSpace.stdCoverPullback ProjSpace.π OModulePresheaf OModulePresheaf.d_apply ProjSpace.pullbackChart ProjSpace.restrictFun ProjSpace.restrictFun_restrictFun ProjSpace.restrictFun_refl ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twist ProjSpace.twistGradedModule ProjSpace.twistObj.ext ProjSpace.exists_sec_shift_twistGradedModule_equiv ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "stdCoverPullback π map pullbackChart restrictFun restrictFun_restrictFun restrictFun_refl twistObj twistRes twistRes_val twist twistGradedModule twistObj.ext exists_sec_shift_twistGradedModule_equiv exists_isFG_hom_injective_saturated_twistGradedModule"
namespace Pack
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ] (π : X ⟶ Spec (.of A)) (m : ℕ)

def idxEquiv (i : ℕ) : (ProjSpace.stdCoverPullback φ).Idx i ≃ ProjSpaceCech.Idx N i where
  toFun s := ⟨fun k => (s.1 k).down, fun _ _ h => (s.2 h : _)⟩
  invFun s := ⟨fun k => ULift.up (s.1 k), fun _ _ h => (s.2 h : _)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

omit [IsAffineHom φ] in
theorem img_nonempty {i : ℕ} (s : ProjSpaceCech.Idx N i) : (ProjSpaceCech.Idx.img N s).Nonempty :=
  Finset.card_pos.mp ((ProjSpaceCech.Idx.card_img N s).symm ▸ Nat.succ_pos i)

theorem inter_eq (i : ℕ) (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    (ProjSpace.stdCoverPullback φ).inter s = ⨅ j ∈ ProjSpaceCech.Idx.img N (idxEquiv φ i s), ProjSpace.pullbackChart φ j := by
  refine le_antisymm (le_iInf fun j => le_iInf fun hj => ?_) (le_iInf fun k => ?_)
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact iInf_le (fun k => (ProjSpace.stdCoverPullback φ).U (s.1 k)) k
  · exact iInf_le_of_le ((idxEquiv φ i s).1 k) (iInf_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))

omit [IsAffineHom φ] in
theorem twistRes_val {U V : X.Opens} (h : U ≤ V) (g : ProjSpace.twistObj π φ m V) (i : Fin (N + 1)) :
    (ProjSpace.twistRes π φ m h g).val i = ProjSpace.restrictFun (inf_le_inf_right _ h) (g.val i) := rfl

omit [IsAffineHom φ] in
theorem twistRes_twistRes {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W) (g : ProjSpace.twistObj π φ m W) :
    ProjSpace.twistRes π φ m h (ProjSpace.twistRes π φ m h' g) = ProjSpace.twistRes π φ m (h.trans h') g := by
  refine ProjSpace.twistObj.ext (funext fun i => ?_)
  simp only [twistRes_val, ProjSpace.restrictFun_restrictFun]

omit [IsAffineHom φ] in
theorem twistRes_self {U : X.Opens} (h : U ≤ U) (g : ProjSpace.twistObj π φ m U) : ProjSpace.twistRes π φ m h g = g := by
  refine ProjSpace.twistObj.ext (funext fun i => ?_)
  rw [twistRes_val]
  exact ProjSpace.restrictFun_refl _

def chainFwd (i : ℕ) :
    ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i
      →ₗ[A] (ProjSpace.twist π φ m).cochain (ProjSpace.stdCoverPullback φ) i :=
  LinearMap.pi fun s => (ProjSpace.twistRes π φ m (inter_eq φ i s).le)
    ∘ₗ ((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N (idxEquiv φ i s)) (img_nonempty _)).toLinearMap
    ∘ₗ LinearMap.proj (idxEquiv φ i s)

def chainBwd (i : ℕ) :
    (ProjSpace.twist π φ m).cochain (ProjSpace.stdCoverPullback φ) i
      →ₗ[A] ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i :=
  LinearMap.pi fun s => ((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N s) (img_nonempty s)).symm.toLinearMap
    ∘ₗ (ProjSpace.twistRes π φ m (inter_eq φ i ((idxEquiv φ i).symm s)).ge)
    ∘ₗ LinearMap.proj ((idxEquiv φ i).symm s)

theorem chainFwd_apply (i : ℕ) (f : ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i)
    (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    chainFwd φ π m i f s = ProjSpace.twistRes π φ m (inter_eq φ i s).le
      ((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N (idxEquiv φ i s)) (img_nonempty _) (f (idxEquiv φ i s))) := rfl

theorem chainBwd_apply (i : ℕ) (g : (ProjSpace.twist π φ m).cochain (ProjSpace.stdCoverPullback φ) i) (s : ProjSpaceCech.Idx N i) :
    chainBwd φ π m i g s = ((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N s) (img_nonempty s)).symm
      (ProjSpace.twistRes π φ m (inter_eq φ i ((idxEquiv φ i).symm s)).ge (g ((idxEquiv φ i).symm s))) := rfl

def chainEquiv (i : ℕ) :
    ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i
      ≃ₗ[A] (ProjSpace.twist π φ m).cochain (ProjSpace.stdCoverPullback φ) i := by
  refine LinearEquiv.ofLinear (chainFwd φ π m i) (chainBwd φ π m i) ?_ ?_
  · refine LinearMap.ext fun g => funext fun s => ?_
    rw [LinearMap.comp_apply, chainFwd_apply, chainBwd_apply, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    show ProjSpace.twistRes π φ m (inter_eq φ i s).le (ProjSpace.twistRes π φ m (inter_eq φ i s).ge (g s)) = g s
    rw [twistRes_twistRes, twistRes_self]
  · refine LinearMap.ext fun f => funext fun s => ?_
    rw [LinearMap.comp_apply, chainBwd_apply, chainFwd_apply, LinearMap.id_apply]
    have hid : ∀ y : ProjSpace.twistObj π φ m (⨅ j ∈ ProjSpaceCech.Idx.img N s, ProjSpace.pullbackChart φ j),
        ProjSpace.twistRes π φ m (inter_eq φ i ((idxEquiv φ i).symm s)).ge
          (ProjSpace.twistRes π φ m (inter_eq φ i ((idxEquiv φ i).symm s)).le y) = y := fun y => by
      refine ProjSpace.twistObj.ext (funext fun k => ?_)
      simp only [twistRes_val, ProjSpace.restrictFun_restrictFun]
      exact ProjSpace.restrictFun_refl _
    exact (congrArg ((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N s) (img_nonempty s)).symm (hid _)).trans
      (((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N s) (img_nonempty s)).symm_apply_apply (f s))

theorem chainEquiv_apply (i : ℕ) (f : ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i)
    (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    chainEquiv φ π m i f s = ProjSpace.twistRes π φ m (inter_eq φ i s).le
      ((AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose (ProjSpaceCech.Idx.img N (idxEquiv φ i s)) (img_nonempty _) (f (idxEquiv φ i s))) := rfl

theorem idxEquiv_face (i : ℕ) (s : (ProjSpace.stdCoverPullback φ).Idx (i + 1)) (j : Fin (i + 2)) :
    idxEquiv φ i ((ProjSpace.stdCoverPullback φ).face s j) = ProjSpaceCech.Idx.face N (idxEquiv φ (i + 1) s) j := rfl

theorem chainEquiv_comm (i : ℕ) (f : ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i) :
    chainEquiv φ π m (i + 1) (ProjSpaceCech.GradedModule.d _ i f)
      = (ProjSpace.twist π φ m).d (ProjSpace.stdCoverPullback φ) i (chainEquiv φ π m i f) := by
  funext s
  rw [chainEquiv_apply, ProjSpaceCech.GradedModule.d_apply, OModulePresheaf.d_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, ProjSpaceCech.GradedModule.faceRes,
    show ((-1 : A) ^ (j : ℕ)) = (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) from by push_cast; ring, Int.cast_smul_eq_zsmul]
  refine congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) ?_
  rw [(AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv φ π m).choose_spec _ _ (img_nonempty _)
    (ProjSpaceCech.Idx.img_face_subset N (idxEquiv φ (i + 1) s) j)]
  show ProjSpace.twistRes π φ m _ (ProjSpace.twistRes π φ m _ _)
    = ProjSpace.twistRes π φ m ((ProjSpace.stdCoverPullback φ).inter_le_inter_face s j) (chainEquiv φ π m i f _)
  rw [chainEquiv_apply]
  refine ProjSpace.twistObj.ext (funext fun k => ?_)
  simp only [twistRes_val, ProjSpace.restrictFun_restrictFun]
  rfl

theorem nonempty_H_equiv_HSucc (i : ℕ) :
    Nonempty (ProjSpaceCech.GradedModule.H ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) (i + 1)
      ≃ₗ[A] (ProjSpace.twist π φ m).HSucc (ProjSpace.stdCoverPullback φ) i) :=
  (LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    (C := fun i => ProjSpaceCech.GradedModule.cochain ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) i)
    (C' := fun i => (ProjSpace.twist π φ m).cochain (ProjSpace.stdCoverPullback φ) i)
    (fun i => ProjSpaceCech.GradedModule.d _ i) (fun i => (ProjSpace.twist π φ m).d (ProjSpace.stdCoverPullback φ) i)
    (chainEquiv φ π m) (fun i x => chainEquiv_comm φ π m i x)).2 i

end AlgebraicGeometry.ProjSpace.Pack

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsFinite Spec Scheme Proj IsAffineHom ProjSpace.stdCoverPullback ProjSpace.π OModulePresheaf OModulePresheaf.d_apply ProjSpace.pullbackChart ProjSpace.restrictFun ProjSpace.restrictFun_restrictFun ProjSpace.restrictFun_refl ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twist ProjSpace.twistGradedModule ProjSpace.twistObj.ext ProjSpace.exists_sec_shift_twistGradedModule_equiv ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "stdCoverPullback π map pullbackChart restrictFun restrictFun_restrictFun restrictFun_refl twistObj twistRes twistRes_val twist twistGradedModule twistObj.ext exists_sec_shift_twistGradedModule_equiv exists_isFG_hom_injective_saturated_twistGradedModule"
namespace TV
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ] (π : X ⟶ Spec (.of A))

theorem sat_shift {M' : ProjSpaceCech.GradedModule A N} (ψ : ProjSpaceCech.GradedModule.Hom M' (ProjSpace.twistGradedModule φ π))
    (hsat : ∀ (j : Fin (N + 1)) (e : ℤ), ∀ x ∈ (ProjSpace.twistGradedModule φ π).grade e,
      ∃ k : ℕ, ∃ x' ∈ M'.grade (e + k), ψ.toLinearMap x' = ((ProjSpace.twistGradedModule φ π).xMul j ^ k) x) (m : ℕ) :
    ∀ (j : Fin (N + 1)) (e : ℤ), ∀ x ∈ ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)).grade e,
      ∃ k : ℕ, ∃ x' ∈ (M'.shift (m : ℤ)).grade (e + k),
        (ψ.shift (m : ℤ)).toLinearMap x' = (((ProjSpace.twistGradedModule φ π).shift (m : ℤ)).xMul j ^ k) x := by
  intro j e x hx
  obtain ⟨k, x', hx', heq⟩ := hsat j (e + m) x hx
  refine ⟨k, x', ?_, heq⟩
  show x' ∈ M'.grade (e + k + m)
  rw [add_right_comm]; exact hx'

theorem exists_forall_subsingleton_HSucc_twist (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ i : ℕ,
      Subsingleton ((ProjSpace.twist π φ m).HSucc (ProjSpace.stdCoverPullback φ) i) := by
  obtain ⟨M', ψ, hFG, hinj, hsat⟩ := AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule φ π hπ
  obtain ⟨d₀, hd₀⟩ := ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG M' hFG
  refine ⟨d₀.toNat, fun m hm i => ?_⟩
  have h1 : Subsingleton (ProjSpaceCech.GradedModule.H (M'.shift (m : ℤ)) (i + 1)) :=
    hd₀ (m : ℤ) (by omega) (i + 1) (by omega)
  have hbij := ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated (ψ.shift (m : ℤ)) hinj (sat_shift φ π ψ hsat m) (i + 1)
  haveI h2 : Subsingleton (ProjSpaceCech.GradedModule.H ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) (i + 1)) :=
    hbij.2.subsingleton
  obtain ⟨e⟩ := AlgebraicGeometry.ProjSpace.Pack.nonempty_H_equiv_HSucc φ π m i
  exact e.symm.toEquiv.subsingleton

end AlgebraicGeometry.ProjSpace.TV

end

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ]
    (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ i : ℕ,
      Subsingleton ((ProjSpace.twist π φ m).HSucc (ProjSpace.stdCoverPullback φ) i) :=
  AlgebraicGeometry.ProjSpace.TV.exists_forall_subsingleton_HSucc_twist φ π hπ

end

end S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist (solution)
