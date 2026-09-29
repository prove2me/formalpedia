-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d038ac20-b286-5751-a54e-c43e95eeb076

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
import Theorems.Thm_DoubleComplex_nonempty_HTot_equiv_of_levelwise_equiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TensorProduct"

set_option maxHeartbeats 1600000

namespace L4Strip

def piUncurry (R : Type u) [CommRing R] {S T : Type u} (M : S → T → Type u) [∀ s t, AddCommGroup (M s t)]
    [∀ s t, Module R (M s t)] : (∀ s, ∀ t, M s t) ≃ₗ[R] (∀ st : S × T, M st.1 st.2) where
  toFun f st := f st.1 st.2
  invFun g s t := g (s, t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def resEquiv {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    {U U' : V.Opens} (h : U = U') : F.obj U' ≃ₗ[R] F.obj U :=
  LinearEquiv.ofLinear (F.res h.le) (F.res h.ge) (by rw [← F.res_comp]; exact F.res_refl U)
    (by rw [← F.res_comp]; exact F.res_refl U')

theorem resEquiv_apply {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    {U U' : V.Opens} (h : U = U') (x : F.obj U') : resEquiv F h x = F.res h.le x := rfl

end L4Strip

open L4Strip _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G)
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) (n : ℕ) :
    Nonempty (DoubleComplex.HTot
        ((OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
          ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
            (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).biCech
          (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))) n ≃ₗ[k]
      DoubleComplex.HTot
        ((CochainCx.Bounded.ofCech (OModulePresheaf.ofModules πX F) 𝔘
            (AlgebraicGeometry.OModulePresheaf.d_comp_d (OModulePresheaf.ofModules πX F) 𝔘)).tensor
          (CochainCx.Bounded.ofCech (OModulePresheaf.ofModules πY G) 𝔙
            (AlgebraicGeometry.OModulePresheaf.d_comp_d (OModulePresheaf.ofModules πY G) 𝔙))) n) := by
  classical
  obtain ⟨e2, he2⟩ :=
    OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible πX πY F hF G hG

  let FX := OModulePresheaf.ofModules πX F
  let GY := OModulePresheaf.ofModules πY G
  let NP := OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
    ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗ (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)
  let 𝔄 := 𝔘.preimageFamily (pullback.fst πX πY)
  let 𝔅 := 𝔙.preimageFamily (pullback.snd πX πY)

  have hbox : ∀ (p q : ℕ) (s : 𝔘.Idx p) (t : 𝔙.Idx q),
      𝔄.inter s ⊓ 𝔅.inter t = pullback.fst πX πY ⁻¹ᵁ 𝔘.inter s ⊓ pullback.snd πX πY ⁻¹ᵁ 𝔙.inter t := by
    intro p q s t
    change (⨅ j, pullback.fst πX πY ⁻¹ᵁ 𝔘.U (s.1 j)) ⊓ (⨅ j, pullback.snd πX πY ⁻¹ᵁ 𝔙.U (t.1 j)) =
      pullback.fst πX πY ⁻¹ᵁ (⨅ j, 𝔘.U (s.1 j)) ⊓ pullback.snd πX πY ⁻¹ᵁ (⨅ j, 𝔙.U (t.1 j))
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin, Scheme.OrderedAffineCover.preimage_iInf_fin]

  let E : ∀ (p q : ℕ) (st : 𝔘.Idx p × 𝔙.Idx q),
      (FX.obj (𝔘.inter st.1) ⊗[k] GY.obj (𝔙.inter st.2)) ≃ₗ[k] NP.obj (𝔄.inter st.1 ⊓ 𝔅.inter st.2) :=
    fun p q st => (e2 (𝔘.affineInter πX st.1) (𝔙.affineInter πY st.2)) ≪≫ₗ resEquiv NP (hbox p q st.1 st.2)
  have hE : ∀ (p q : ℕ) (st : 𝔘.Idx p × 𝔙.Idx q) (x : FX.obj (𝔘.inter st.1) ⊗[k] GY.obj (𝔙.inter st.2)),
      E p q st x = NP.res (hbox p q st.1 st.2).le (e2 (𝔘.affineInter πX st.1) (𝔙.affineInter πY st.2) x) :=
    fun p q st x => rfl

  let Φ : ∀ p q : ℕ, (FX.cochain 𝔘 p ⊗[k] GY.cochain 𝔙 q) ≃ₗ[k] OModulePresheaf.BiCech.C NP 𝔄 𝔅 p q := fun p q =>
    TensorProduct.piLeft k (GY.cochain 𝔙 q) (fun s : 𝔘.Idx p => FX.obj (𝔘.inter s)) ≪≫ₗ
      LinearEquiv.piCongrRight (fun s : 𝔘.Idx p =>
        TensorProduct.piRight k k (FX.obj (𝔘.inter s)) (fun t : 𝔙.Idx q => GY.obj (𝔙.inter t))) ≪≫ₗ
      piUncurry k (fun (s : 𝔘.Idx p) (t : 𝔙.Idx q) => FX.obj (𝔘.inter s) ⊗[k] GY.obj (𝔙.inter t)) ≪≫ₗ
      LinearEquiv.piCongrRight (fun st : 𝔘.Idx p × 𝔙.Idx q => E p q st)
  have hΦ : ∀ (p q : ℕ) (a : FX.cochain 𝔘 p) (b : GY.cochain 𝔙 q) (st : 𝔘.Idx p × 𝔙.Idx q),
      Φ p q (a ⊗ₜ b) st = E p q st (a st.1 ⊗ₜ b st.2) := by
    intro p q a b st
    simp only [Φ, LinearEquiv.trans_apply, TensorProduct.piLeft,
      TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, TensorProduct.comm_tmul]
    rfl

  have hnatH : ∀ (p q : ℕ) (s : 𝔘.Idx (p + 1)) (t : 𝔙.Idx q) (j : Fin (p + 2))
      (a : FX.obj (𝔘.inter (𝔘.face s j))) (b : GY.obj (𝔙.inter t)),
      NP.res (BiCech.inter_inf_le_left 𝔄 𝔅 s t j) (E p q (𝔘.face s j, t) (a ⊗ₜ b)) =
        E (p + 1) q (s, t) (FX.res (𝔘.inter_le_inter_face s j) a ⊗ₜ b) := by
    intro p q s t j a b
    rw [hE, hE]
    dsimp only
    refine (OModulePresheaf.res_res NP _ _ _).trans ?_
    conv_rhs => rw [← GY.res_refl_apply (𝔙.inter t) b]
    rw [← he2 (𝔘.affineInter πX (𝔘.face s j)) (𝔘.affineInter πX s) (𝔙.affineInter πY t) (𝔙.affineInter πY t)
        (𝔘.inter_le_inter_face s j) le_rfl a b]
    exact (OModulePresheaf.res_res NP _ _ _).symm
  have hnatV : ∀ (p q : ℕ) (s : 𝔘.Idx p) (t : 𝔙.Idx (q + 1)) (j : Fin (q + 2))
      (a : FX.obj (𝔘.inter s)) (b : GY.obj (𝔙.inter (𝔙.face t j))),
      NP.res (BiCech.inter_inf_le_right 𝔄 𝔅 s t j) (E p q (s, 𝔙.face t j) (a ⊗ₜ b)) =
        E p (q + 1) (s, t) (a ⊗ₜ GY.res (𝔙.inter_le_inter_face t j) b) := by
    intro p q s t j a b
    rw [hE, hE]
    dsimp only
    refine (OModulePresheaf.res_res NP _ _ _).trans ?_
    conv_rhs => rw [← FX.res_refl_apply (𝔘.inter s) a]
    rw [← he2 (𝔘.affineInter πX s) (𝔘.affineInter πX s) (𝔙.affineInter πY (𝔙.face t j)) (𝔙.affineInter πY t)
        le_rfl (𝔙.inter_le_inter_face t j) a b]
    exact (OModulePresheaf.res_res NP _ _ _).symm

  have hcomH : ∀ (p q : ℕ) (y : FX.cochain 𝔘 p ⊗[k] GY.cochain 𝔙 q),
      BiCech.dH NP 𝔄 𝔅 p q (Φ p q y) = Φ (p + 1) q ((FX.d 𝔘 p).rTensor (GY.cochain 𝔙 q) y) := by
    intro p q
    suffices h : (BiCech.dH NP 𝔄 𝔅 p q) ∘ₗ (Φ p q).toLinearMap =
        (Φ (p + 1) q).toLinearMap ∘ₗ (FX.d 𝔘 p).rTensor (GY.cochain 𝔙 q) from
      fun y => congrFun (congrArg DFunLike.coe h) y
    refine TensorProduct.ext' fun a b => ?_
    change BiCech.dH NP 𝔄 𝔅 p q (Φ p q (a ⊗ₜ b)) = Φ (p + 1) q ((FX.d 𝔘 p).rTensor (GY.cochain 𝔙 q) (a ⊗ₜ b))
    rw [LinearMap.rTensor_tmul]
    funext st
    obtain ⟨s, t⟩ := st
    rw [BiCech.dH_apply, hΦ]
    change _ = E (p + 1) q (s, t) ((FX.d 𝔘 p a s) ⊗ₜ b t)
    rw [OModulePresheaf.d_apply]
    let ℓ : FX.obj (𝔘.inter s) →ₗ[k] NP.obj (𝔄.inter s ⊓ 𝔅.inter t) :=
      (E (p + 1) q (s, t)).toLinearMap ∘ₗ ((TensorProduct.mk k (FX.obj (𝔘.inter s)) (GY.obj (𝔙.inter t))).flip (b t))
    have hℓ : ∀ m, ℓ m = E (p + 1) q (s, t) (m ⊗ₜ b t) := fun m => rfl
    rw [← hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, hℓ, hΦ]
    exact congrArg _ (hnatH p q s t j (a (𝔘.face s j)) (b t))

  have hcomV : ∀ (p q : ℕ) (y : FX.cochain 𝔘 p ⊗[k] GY.cochain 𝔙 q),
      BiCech.dV NP 𝔄 𝔅 p q (Φ p q y) = Φ p (q + 1) ((GY.d 𝔙 q).lTensor (FX.cochain 𝔘 p) y) := by
    intro p q
    suffices h : (BiCech.dV NP 𝔄 𝔅 p q) ∘ₗ (Φ p q).toLinearMap =
        (Φ p (q + 1)).toLinearMap ∘ₗ (GY.d 𝔙 q).lTensor (FX.cochain 𝔘 p) from
      fun y => congrFun (congrArg DFunLike.coe h) y
    refine TensorProduct.ext' fun a b => ?_
    change BiCech.dV NP 𝔄 𝔅 p q (Φ p q (a ⊗ₜ b)) = Φ p (q + 1) ((GY.d 𝔙 q).lTensor (FX.cochain 𝔘 p) (a ⊗ₜ b))
    rw [LinearMap.lTensor_tmul]
    funext st
    obtain ⟨s, t⟩ := st
    rw [BiCech.dV_apply, hΦ]
    change _ = E p (q + 1) (s, t) (a s ⊗ₜ (GY.d 𝔙 q b t))
    rw [OModulePresheaf.d_apply]
    let ℓ : GY.obj (𝔙.inter t) →ₗ[k] NP.obj (𝔄.inter s ⊓ 𝔅.inter t) :=
      (E p (q + 1) (s, t)).toLinearMap ∘ₗ (TensorProduct.mk k (FX.obj (𝔘.inter s)) (GY.obj (𝔙.inter t)) (a s))
    have hℓ : ∀ m, ℓ m = E p (q + 1) (s, t) (a s ⊗ₜ m) := fun m => rfl
    rw [← hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, hℓ, hΦ]
    exact congrArg _ (hnatV p q s t j (a s) (b (𝔙.face t j)))

  refine DoubleComplex.nonempty_HTot_equiv_of_levelwise_equiv _ _ (fun p q => (Φ p q).symm) ?_ ?_ n
  · intro p q x
    obtain ⟨y, rfl⟩ : ∃ y, x = Φ p q y := ⟨(Φ p q).symm x, ((Φ p q).apply_symm_apply x).symm⟩
    change (Φ (p + 1) q).symm (BiCech.dH NP 𝔄 𝔅 p q (Φ p q y)) =
      (FX.d 𝔘 p).rTensor (GY.cochain 𝔙 q) ((Φ p q).symm (Φ p q y))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    exact hcomH p q y
  · intro p q x
    obtain ⟨y, rfl⟩ : ∃ y, x = Φ p q y := ⟨(Φ p q).symm x, ((Φ p q).apply_symm_apply x).symm⟩
    change (Φ p (q + 1)).symm (BiCech.dV NP 𝔄 𝔅 p q (Φ p q y)) =
      (GY.d 𝔙 q).lTensor (FX.cochain 𝔘 p) ((Φ p q).symm (Φ p q y))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    exact hcomV p q y

end S_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech (solution)
