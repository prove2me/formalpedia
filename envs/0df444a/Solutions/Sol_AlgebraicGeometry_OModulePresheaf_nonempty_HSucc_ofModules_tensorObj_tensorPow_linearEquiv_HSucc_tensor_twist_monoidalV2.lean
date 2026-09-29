-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c8e5eebb-3d5d-5130-972b-d00981718285

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
import Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2.AlgebraicGeometry TensorProduct"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.preimage_inf Spec Scheme Scheme.Hom.preimage_top Proj Proj.basicOpen_one Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul IsAffineOpen Scheme.Modules IsAffineHom Scheme.Modules.IsInvertible Scheme.Modules.tensorSections Scheme.Modules.tensorSectionsBilin Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.ProjPresentation ProjSpace.X_mem_one OModulePresheaf.ofModules OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.tensor_res_tmul OModulePresheaf.twist_res_tmul ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twist ProjSpace.stdCoverPullback Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial"
namespace Ws23TTC
p2m_open "AlgebraicGeometry"

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {𝓛 : X.Modules} {N : ℕ}
  (𝔓 : 𝓛.ProjPresentation f N) (𝓕 : X.Modules) (d : ℕ)

omit 𝔓 𝓕 d in
theorem preimage_basicOpen_prod (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → Fin (N + 1)) :
    φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
        (∏ v ∈ S, (MvPolynomial.X (c v) : MvPolynomial (Fin (N + 1)) A))
      = S.inf fun v => φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X (c v)) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Proj.basicOpen_one, Scheme.Hom.preimage_top, Finset.inf_empty]
  | insert a S ha ih => rw [Finset.prod_insert ha, Proj.basicOpen_mul, Scheme.Hom.preimage_inf, ih, Finset.inf_insert]

theorem inter_eq [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    (ProjSpace.stdCoverPullback 𝔓.toProj).inter s
      = 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
          (∏ v ∈ (Finset.univ : Finset (Fin (i + 1))), (MvPolynomial.X ((s.1 v).down) : MvPolynomial (Fin (N + 1)) A)) := by
  classical
  rw [preimage_basicOpen_prod, Finset.inf_univ_eq_iInf]
  rfl

theorem isAffineOpen_inter [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    IsAffineOpen ((ProjSpace.stdCoverPullback 𝔓.toProj).inter s) := by
  classical
  rw [inter_eq 𝔓 s]
  refine (Proj.isAffineOpen_basicOpen _ _
    (SetLike.prod_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (fun _ => 1) _
      fun v _ => ProjSpace.X_mem_one A N ((s.1 v).down)) ?_).preimage 𝔓.toProj
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact Nat.succ_pos i

def W [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) : X.affineOpens :=
  ⟨(ProjSpace.stdCoverPullback 𝔓.toProj).inter s, isAffineOpen_inter 𝔓 s⟩

theorem inter_le_chart [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    (ProjSpace.stdCoverPullback 𝔓.toProj).inter s ≤ ProjSpace.pullbackChart 𝔓.toProj ((s.1 0).down) :=
  (ProjSpace.stdCoverPullback 𝔓.toProj).inter_le s 0

abbrev Sh : OModulePresheaf f := OModulePresheaf.ofModules f (𝓕 ⊗ 𝓛.tensorPow d)

abbrev Mid : OModulePresheaf f := (OModulePresheaf.ofModules f 𝓕).twist (𝓛.tensorPow d)

abbrev Tw : OModulePresheaf f := (OModulePresheaf.ofModules f 𝓕).tensor (ProjSpace.twist f 𝔓.toProj d)

def μ (W : X.Opens) : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W →ₗ[A] (Sh 𝓕 d (f := f) (𝓛 := 𝓛)).obj W where
  toFun t := TensorProduct.lift (Scheme.Modules.tensorSectionsBilin 𝓕 (𝓛.tensorPow d) W) t
  map_add' t t' := map_add _ t t'
  map_smul' r t := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f W
    show TensorProduct.lift (Scheme.Modules.tensorSectionsBilin 𝓕 (𝓛.tensorPow d) W) (algebraMap A Γ(X, W) r • t)
      = algebraMap A Γ(X, W) r • TensorProduct.lift (Scheme.Modules.tensorSectionsBilin 𝓕 (𝓛.tensorPow d) W) t
    exact LinearMap.map_smul _ _ _

theorem μ_tmul (W : X.Opens) (x : Γ(𝓕, W)) (y : Γ(𝓛.tensorPow d, W)) :
    μ 𝓕 d W (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W from x ⊗ₜ[Γ(X, W)] y)
      = (show (Sh 𝓕 d (f := f) (𝓛 := 𝓛)).obj W from Scheme.Modules.tensorSections x y) := by
  show TensorProduct.lift _ (x ⊗ₜ y) = _
  rw [TensorProduct.lift.tmul]
  rfl

theorem μ_res {W W' : X.Opens} (h : W ≤ W') (t : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W') :
    μ 𝓕 d W ((Mid 𝓕 d).res h t) = (Sh 𝓕 d).res h (μ 𝓕 d W' t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    change μ 𝓕 d W ((Mid 𝓕 d).res h (0 : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W'))
      = (Sh 𝓕 d).res h (μ 𝓕 d W' (0 : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W'))
    rw [map_zero, map_zero, map_zero, map_zero]
  | tmul x y =>
    change μ 𝓕 d W ((Mid 𝓕 d).res h (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from x ⊗ₜ[Γ(X, W')] y))
      = (Sh 𝓕 d).res h (μ 𝓕 d W' (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from x ⊗ₜ[Γ(X, W')] y))
    rw [OModulePresheaf.twist_res_tmul, μ_tmul, μ_tmul]
    exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
  | add t t' ht ht' =>
    change μ 𝓕 d W ((Mid 𝓕 d).res h ((show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t) + (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t')))
      = (Sh 𝓕 d).res h (μ 𝓕 d W' ((show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t) + (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t')))
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) ht ht'

theorem μ_bijective [IsAffineHom 𝔓.toProj] (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h𝓕 : (OModulePresheaf.ofModules f 𝓕).IsQuasicoherent) {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    Function.Bijective (μ 𝓕 d (f := f) (𝓛 := 𝓛) ((ProjSpace.stdCoverPullback 𝔓.toProj).inter s)) :=
  AlgebraicGeometry.Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 f h𝓕
    (AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial f (𝓛.tensorPow d)
      (h𝓛.tensorPow_monoidalV2 d).exists_trivialization)
    (W 𝔓 s)

def e : ∀ U : X.Opens, Γ(𝓛.tensorPow d, U) →ₗ[Γ(X, U)] ProjSpace.twistObj f 𝔓.toProj d U :=
  (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 𝔓 d).choose

theorem e_res {U U' : X.Opens} (h : U ≤ U') (y : Γ(𝓛.tensorPow d, U')) :
    e 𝔓 d U ((𝓛.tensorPow d).presheaf.map (homOfLE h).op y) = ProjSpace.twistRes f 𝔓.toProj d h (e 𝔓 d U' y) :=
  (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 𝔓 d).choose_spec.2.1
    U U' h y

theorem e_bijective (U : X.Opens) (j : Fin (N + 1)) (hU : U ≤ ProjSpace.pullbackChart 𝔓.toProj j) :
    Function.Bijective (e 𝔓 d U) :=
  (AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 𝔓 d).choose_spec.2.2
    U j hU

def ν (W : X.Opens) : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W →ₗ[A] (Tw 𝔓 𝓕 d).obj W where
  toFun t := TensorProduct.map (LinearMap.id : Γ(𝓕, W) →ₗ[Γ(X, W)] Γ(𝓕, W)) (e 𝔓 d W) t
  map_add' t t' := map_add _ t t'
  map_smul' r t := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f W
    show TensorProduct.map (LinearMap.id : Γ(𝓕, W) →ₗ[Γ(X, W)] Γ(𝓕, W)) (e 𝔓 d W) (algebraMap A Γ(X, W) r • t)
      = algebraMap A Γ(X, W) r • TensorProduct.map (LinearMap.id : Γ(𝓕, W) →ₗ[Γ(X, W)] Γ(𝓕, W)) (e 𝔓 d W) t
    exact LinearMap.map_smul _ _ _

theorem ν_tmul (W : X.Opens) (x : Γ(𝓕, W)) (y : Γ(𝓛.tensorPow d, W)) :
    ν 𝔓 𝓕 d W (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W from x ⊗ₜ[Γ(X, W)] y)
      = (show (Tw 𝔓 𝓕 d).obj W from x ⊗ₜ[Γ(X, W)] (show (ProjSpace.twist f 𝔓.toProj d).obj W from e 𝔓 d W y)) := by
  show TensorProduct.map _ _ (x ⊗ₜ y) = _
  rw [TensorProduct.map_tmul]
  rfl

theorem ν_res {W W' : X.Opens} (h : W ≤ W') (t : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W') :
    ν 𝔓 𝓕 d W ((Mid 𝓕 d).res h t) = (Tw 𝔓 𝓕 d).res h (ν 𝔓 𝓕 d W' t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    change ν 𝔓 𝓕 d W ((Mid 𝓕 d).res h (0 : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W'))
      = (Tw 𝔓 𝓕 d).res h (ν 𝔓 𝓕 d W' (0 : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W'))
    rw [map_zero, map_zero, map_zero, map_zero]
  | tmul x y =>
    change ν 𝔓 𝓕 d W ((Mid 𝓕 d).res h (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from x ⊗ₜ[Γ(X, W')] y))
      = (Tw 𝔓 𝓕 d).res h (ν 𝔓 𝓕 d W' (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from x ⊗ₜ[Γ(X, W')] y))
    rw [OModulePresheaf.twist_res_tmul, ν_tmul, ν_tmul, OModulePresheaf.tensor_res_tmul, e_res]
    rfl
  | add t t' ht ht' =>
    change ν 𝔓 𝓕 d W ((Mid 𝓕 d).res h ((show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t) + (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t')))
      = (Tw 𝔓 𝓕 d).res h (ν 𝔓 𝓕 d W' ((show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t) + (show (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).obj W' from t')))
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) ht ht'

theorem ν_bijective [IsAffineHom 𝔓.toProj] {i : ℕ} (s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx i) :
    Function.Bijective (ν 𝔓 𝓕 d (f := f) (𝓛 := 𝓛) ((ProjSpace.stdCoverPullback 𝔓.toProj).inter s)) := by
  let W := (ProjSpace.stdCoverPullback 𝔓.toProj).inter s
  let eW : Γ(𝓛.tensorPow d, W) ≃ₗ[Γ(X, W)] ProjSpace.twistObj f 𝔓.toProj d W :=
    LinearEquiv.ofBijective (e 𝔓 d W) (e_bijective 𝔓 d W _ (inter_le_chart 𝔓 s))
  exact (TensorProduct.congr (LinearEquiv.refl Γ(X, W) Γ(𝓕, W)) eW).bijective

section Cochains

variable [IsAffineHom 𝔓.toProj]

def cμ (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓕 : (OModulePresheaf.ofModules f 𝓕).IsQuasicoherent) (i : ℕ) : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i
    ≃ₗ[A] (Sh 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i :=
  LinearEquiv.piCongrRight fun s => LinearEquiv.ofBijective (μ 𝓕 d _) (μ_bijective 𝔓 𝓕 d h𝓛 h𝓕 s)

def cν (i : ℕ) : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i
    ≃ₗ[A] (Tw 𝔓 𝓕 d).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i :=
  LinearEquiv.piCongrRight fun s => LinearEquiv.ofBijective (ν 𝔓 𝓕 d _) (ν_bijective 𝔓 𝓕 d s)

theorem cμ_comm (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓕 : (OModulePresheaf.ofModules f 𝓕).IsQuasicoherent) (i : ℕ) (c : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i) :
    cμ 𝔓 𝓕 d h𝓛 h𝓕 (i + 1) ((Mid 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i c)
      = (Sh 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i (cμ 𝔓 𝓕 d h𝓛 h𝓕 i c) := by
  funext s
  show μ 𝓕 d _ ((Mid 𝓕 d).d _ i c s) = (Sh 𝓕 d).d _ i (fun s => μ 𝓕 d _ (c s)) s
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, μ_res]

theorem cν_comm (i : ℕ) (c : (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i) :
    cν 𝔓 𝓕 d (i + 1) ((Mid 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i c)
      = (Tw 𝔓 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i (cν 𝔓 𝓕 d i c) := by
  funext s
  show ν 𝔓 𝓕 d _ ((Mid 𝓕 d).d _ i c s) = (Tw 𝔓 𝓕 d).d _ i (fun s => ν 𝔓 𝓕 d _ (c s)) s
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, ν_res]

theorem nonempty_equiv_sh (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓕 : (OModulePresheaf.ofModules f 𝓕).IsQuasicoherent) (i : ℕ) :
    Nonempty ((Mid 𝓕 d (f := f) (𝓛 := 𝓛)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i
      ≃ₗ[A] (Sh 𝓕 d (f := f) (𝓛 := 𝓛)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) :=
  (LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    (C := fun i => (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (C' := fun i => (Sh 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (Mid 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (Sh 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (cμ 𝔓 𝓕 d h𝓛 h𝓕) (fun i x => cμ_comm 𝔓 𝓕 d h𝓛 h𝓕 i x)).2 i

theorem nonempty_equiv_tw (i : ℕ) :
    Nonempty ((Mid 𝓕 d (f := f) (𝓛 := 𝓛)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i
      ≃ₗ[A] (Tw 𝔓 𝓕 d).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) :=
  (LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    (C := fun i => (Mid 𝓕 d (f := f) (𝓛 := 𝓛)).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (C' := fun i => (Tw 𝔓 𝓕 d).cochain (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (Mid 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (fun i => (Tw 𝔓 𝓕 d).d (ProjSpace.stdCoverPullback 𝔓.toProj) i)
    (cν 𝔓 𝓕 d) (fun i x => cν_comm 𝔓 𝓕 d i x)).2 i

end Cochains

end AlgebraicGeometry.Ws23TTC

open AlgebraicGeometry.Ws23TTC in
theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (N : ℕ) (𝔓 : 𝓛.ProjPresentation f N) [IsAffineHom 𝔓.toProj]
    (𝓕 : X.Modules) (h𝓕 : (OModulePresheaf.ofModules f 𝓕).IsQuasicoherent) (d i : ℕ) :
    Nonempty ((OModulePresheaf.ofModules f (𝓕 ⊗ 𝓛.tensorPow d)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i ≃ₗ[A]
      ((OModulePresheaf.ofModules f 𝓕).tensor (ProjSpace.twist f 𝔓.toProj d)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) := by
  obtain ⟨e₁⟩ := nonempty_equiv_sh 𝔓 𝓕 d h𝓛 h𝓕 i
  obtain ⟨e₂⟩ := nonempty_equiv_tw 𝔓 𝓕 d i
  exact ⟨e₁.symm.trans e₂⟩

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2 (solution)
