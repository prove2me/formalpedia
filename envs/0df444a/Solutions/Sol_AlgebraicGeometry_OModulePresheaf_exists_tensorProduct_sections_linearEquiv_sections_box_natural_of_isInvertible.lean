-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fa13b515-2cd2-5a59-8c4e-37c72229ffe9

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le
import Theorems.Thm_TensorProduct_exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TensorProduct Opposite"

set_option maxHeartbeats 1600000

noncomputable section

namespace L4Box

p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme.Modules"

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (G : Y.Modules)

abbrev box (U : X.Opens) (V : Y.Opens) : (pullback πX πY).Opens :=
  pullback.fst πX πY ⁻¹ᵁ U ⊓ pullback.snd πX πY ⁻¹ᵁ V

omit F G in
theorem box_le_fst (U : X.Opens) (V : Y.Opens) : box πX πY U V ≤ pullback.fst πX πY ⁻¹ᵁ U := inf_le_left
omit F G in
theorem box_le_snd (U : X.Opens) (V : Y.Opens) : box πX πY U V ≤ pullback.snd πX πY ⁻¹ᵁ V := inf_le_right
omit F G in
theorem box_mono {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V' ≤ V) :
    box πX πY U' V' ≤ box πX πY U V :=
  inf_le_inf ((pullback.fst πX πY).preimage_mono hU) ((pullback.snd πX πY).preimage_mono hV)

abbrev NN : (pullback πX πY).Modules :=
  (Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗ (Scheme.Modules.pullback (pullback.snd πX πY)).obj G

omit G in

noncomputable def ρ₁ (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) :
    Γ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F, box πX πY U V) :=
  ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F).presheaf.map (homOfLE (box_le_fst πX πY U V)).op
    (pullbackLocalSection (pullback.fst πX πY) s)

omit F in

noncomputable def ρ₂ (U : X.Opens) (V : Y.Opens) (t : Γ(G, V)) :
    Γ((Scheme.Modules.pullback (pullback.snd πX πY)).obj G, box πX πY U V) :=
  ((Scheme.Modules.pullback (pullback.snd πX πY)).obj G).presheaf.map (homOfLE (box_le_snd πX πY U V)).op
    (pullbackLocalSection (pullback.snd πX πY) t)

theorem map_map {Z : Scheme.{u}} (M : Z.Modules) {U₁ U₂ U₃ : Z.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (x : Γ(M, U₃)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op x) = M.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit G in
theorem map_ρ₁ {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V' ≤ V) (s : Γ(F, U)) :
    ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F).presheaf.map (homOfLE (box_mono πX πY hU hV)).op
        (ρ₁ πX πY F U V s) =
      ρ₁ πX πY F U' V' (F.presheaf.map (homOfLE hU).op s) := by
  rw [ρ₁, ρ₁, map_map, ← map_homOfLE_pullbackLocalSection (pullback.fst πX πY) hU s, map_map]

omit F in
theorem map_ρ₂ {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V' ≤ V) (t : Γ(G, V)) :
    ((Scheme.Modules.pullback (pullback.snd πX πY)).obj G).presheaf.map (homOfLE (box_mono πX πY hU hV)).op
        (ρ₂ πX πY G U V t) =
      ρ₂ πX πY G U' V' (G.presheaf.map (homOfLE hV).op t) := by
  rw [ρ₂, ρ₂, map_map, ← map_homOfLE_pullbackLocalSection (pullback.snd πX πY) hV t, map_map]

omit F G in

theorem appLE_fst_algebraMap (U : X.Opens) (V : Y.Opens) (r : k) :
    (((pullback.fst πX πY).appLE U (box πX πY U V) (box_le_fst πX πY U V)).hom
        ((algebraOfHom πX U).algebraMap r) : Γ(pullback πX πY, box πX πY U V)) =
      (algebraOfHom (pullback.fst πX πY ≫ πX) (box πX πY U V)).algebraMap r := by
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_comp_appLE]

omit F G in
theorem appLE_congr_hom {Z T : Scheme.{u}} {f g : Z ⟶ T} (h : f = g) (U : T.Opens) (V : Z.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

omit F G in

theorem appLE_snd_algebraMap (U : X.Opens) (V : Y.Opens) (r : k) :
    (((pullback.snd πX πY).appLE V (box πX πY U V) (box_le_snd πX πY U V)).hom
        ((algebraOfHom πY V).algebraMap r) : Γ(pullback πX πY, box πX πY U V)) =
      (algebraOfHom (pullback.fst πX πY ≫ πX) (box πX πY U V)).algebraMap r := by
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_comp_appLE, appLE_congr_hom pullback.condition.symm]

def fwd₀ (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) (t : Γ(G, V)) : Γ(NN πX πY F G, box πX πY U V) :=
  tensorSections (ρ₁ πX πY F U V s) (ρ₂ πX πY G U V t)

theorem fwd₀_add_left (U : X.Opens) (V : Y.Opens) (s s' : Γ(F, U)) (t : Γ(G, V)) :
    fwd₀ πX πY F G U V (s + s') t = fwd₀ πX πY F G U V s t + fwd₀ πX πY F G U V s' t := by
  unfold fwd₀ ρ₁
  rw [pullbackLocalSection_add, map_add]
  exact tensorSections_add_left _ _ _

theorem fwd₀_add_right (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) (t t' : Γ(G, V)) :
    fwd₀ πX πY F G U V s (t + t') = fwd₀ πX πY F G U V s t + fwd₀ πX πY F G U V s t' := by
  unfold fwd₀ ρ₂
  rw [pullbackLocalSection_add, map_add]
  exact tensorSections_add_right _ _ _

theorem fwd₀_smul_left (U : X.Opens) (V : Y.Opens) (r : k) (s : Γ(F, U)) (t : Γ(G, V)) :
    fwd₀ πX πY F G U V ((algebraOfHom πX U).algebraMap r • s) t =
      (algebraOfHom (pullback.fst πX πY ≫ πX) (box πX πY U V)).algebraMap r • fwd₀ πX πY F G U V s t := by
  unfold fwd₀ ρ₁
  rw [pullbackLocalSection_smul, Scheme.Modules.map_smul, tensorSections_smul_left, ← appLE_fst_algebraMap]
  rfl

theorem fwd₀_smul_right (U : X.Opens) (V : Y.Opens) (r : k) (s : Γ(F, U)) (t : Γ(G, V)) :
    fwd₀ πX πY F G U V s ((algebraOfHom πY V).algebraMap r • t) =
      (algebraOfHom (pullback.fst πX πY ≫ πX) (box πX πY U V)).algebraMap r • fwd₀ πX πY F G U V s t := by
  unfold fwd₀ ρ₂
  rw [pullbackLocalSection_smul, Scheme.Modules.map_smul, tensorSections_smul_right, ← appLE_snd_algebraMap]
  rfl

def fwdBilin (U : X.Opens) (V : Y.Opens) :
    (ofModules πX F).obj U →ₗ[k] (ofModules πY G).obj V →ₗ[k] (ofModules (pullback.fst πX πY ≫ πX) (NN πX πY F G)).obj (box πX πY U V) :=
  LinearMap.mk₂ k (fun s t => fwd₀ πX πY F G U V s t)
    (fun s s' t => fwd₀_add_left πX πY F G U V s s' t)
    (fun r s t => fwd₀_smul_left πX πY F G U V r s t)
    (fun s t t' => fwd₀_add_right πX πY F G U V s t t')
    (fun r s t => fwd₀_smul_right πX πY F G U V r s t)

def fwd (U : X.Opens) (V : Y.Opens) :
    (ofModules πX F).obj U ⊗[k] (ofModules πY G).obj V →ₗ[k]
      (ofModules (pullback.fst πX πY ≫ πX) (NN πX πY F G)).obj (box πX πY U V) :=
  TensorProduct.lift (fwdBilin πX πY F G U V)

theorem fwd_tmul (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) (t : Γ(G, V)) :
    fwd πX πY F G U V (s ⊗ₜ t) = tensorSections (ρ₁ πX πY F U V s) (ρ₂ πX πY G U V t) :=
  rfl

theorem fwd_bijective [IsSeparated πX] [IsSeparated πY] (hF : Scheme.Modules.IsInvertible F)
    (hG : Scheme.Modules.IsInvertible G) (U : X.affineOpens) (V : Y.affineOpens) :
    Function.Bijective (fwd πX πY F G U.1 V.1) := by
  classical

  obtain ⟨hW, Φ, hΦ⟩ := Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback πX πY
    (pullback.fst πX πY) (pullback.snd πX πY) (IsPullback.of_hasPullback πX πY) U.1 U.2 V.1 V.2
  let W : (pullback πX πY).affineOpens := ⟨box πX πY U.1 V.1, hW⟩
  letI iA : Algebra Γ(X, U.1) Γ(pullback πX πY, box πX πY U.1 V.1) :=
    ((pullback.fst πX πY).appLE U.1 (box πX πY U.1 V.1) (box_le_fst πX πY U.1 V.1)).hom.toAlgebra
  letI iB : Algebra Γ(Y, V.1) Γ(pullback πX πY, box πX πY U.1 V.1) :=
    ((pullback.snd πX πY).appLE V.1 (box πX πY U.1 V.1) (box_le_snd πX πY U.1 V.1)).hom.toAlgebra
  letI := algebraOfHom πX U.1
  letI := algebraOfHom πY V.1
  letI := algebraOfHom (pullback.fst πX πY ≫ πX) (box πX πY U.1 V.1)
  haveI : IsScalarTower k Γ(X, U.1) Γ(pullback πX πY, box πX πY U.1 V.1) :=
    IsScalarTower.of_algebraMap_eq (fun r => (appLE_fst_algebraMap πX πY U.1 V.1 r).symm)
  haveI : IsScalarTower k Γ(Y, V.1) Γ(pullback πX πY, box πX πY U.1 V.1) :=
    IsScalarTower.of_algebraMap_eq (fun r => (appLE_snd_algebraMap πX πY U.1 V.1 r).symm)

  obtain ⟨β₁, hβ₁⟩ := Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback_of_le
    (pullback.fst πX πY) hF U.1 U.2 (box πX πY U.1 V.1) hW (box_le_fst πX πY U.1 V.1)
  obtain ⟨β₂, hβ₂⟩ := Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback_of_le
    (pullback.snd πX πY) hG V.1 V.2 (box πX πY U.1 V.1) hW (box_le_snd πX πY U.1 V.1)
  have hτ := Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2
    (hF.pullback (pullback.fst πX πY)) (hG.pullback (pullback.snd πX πY)) W
  let τ := LinearEquiv.ofBijective _ hτ
  obtain ⟨g, hg⟩ := TensorProduct.exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective
    (k := k) Φ (fun a b => hΦ a b) ((ofModules πX F).obj U.1) ((ofModules πY G).obj V.1)

  let Gf : ((ofModules πX F).obj U.1 ⊗[k] (ofModules πY G).obj V.1) →+
      ((ofModules πX F).obj U.1 ⊗[k] (ofModules πY G).obj V.1) :=
    g.toAddMonoidHom.comp ((((TensorProduct.congr β₁.symm β₂.symm).toLinearMap.toAddMonoidHom.comp
      τ.symm.toLinearMap.toAddMonoidHom)).comp (fwd πX πY F G U.1 V.1).toAddMonoidHom)
  have hGf : ∀ x, Gf x = g (TensorProduct.congr β₁.symm β₂.symm (τ.symm (fwd πX πY F G U.1 V.1 x))) := fun x => rfl
  have hleft : ∀ x, g (TensorProduct.congr β₁.symm β₂.symm (τ.symm (fwd πX πY F G U.1 V.1 x))) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [← hGf]; exact Gf.map_zero
    | add x y hx hy => rw [← hGf] at hx hy ⊢; rw [Gf.map_add, hx, hy]
    | tmul s t =>
      rw [fwd_tmul]
      have h1 : τ.symm (tensorSections (ρ₁ πX πY F U.1 V.1 s) (ρ₂ πX πY G U.1 V.1 t)) =
          ρ₁ πX πY F U.1 V.1 s ⊗ₜ ρ₂ πX πY G U.1 V.1 t := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      rw [h1, TensorProduct.congr_tmul]
      have h2 : β₁.symm (ρ₁ πX πY F U.1 V.1 s) = (1 : Γ(pullback πX πY, box πX πY U.1 V.1)) ⊗ₜ s := by
        rw [LinearEquiv.symm_apply_eq]; exact (hβ₁ s).symm
      have h3 : β₂.symm (ρ₂ πX πY G U.1 V.1 t) = (1 : Γ(pullback πX πY, box πX πY U.1 V.1)) ⊗ₜ t := by
        rw [LinearEquiv.symm_apply_eq]; exact (hβ₂ t).symm
      rw [h2, h3]
      exact hg s t
  have hinj : Function.Injective (fun n => g (TensorProduct.congr β₁.symm β₂.symm (τ.symm n))) :=
    g.injective.comp ((TensorProduct.congr β₁.symm β₂.symm).injective.comp τ.symm.injective)
  constructor
  · intro x y hxy
    have h := congrArg (fun n => g (TensorProduct.congr β₁.symm β₂.symm (τ.symm n))) hxy
    simp only [hleft] at h
    exact h
  · intro n
    exact ⟨g (TensorProduct.congr β₁.symm β₂.symm (τ.symm n)), hinj (hleft _)⟩

end L4Box

open L4Box _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G) :
    ∃ e : ∀ (U : X.affineOpens) (V : Y.affineOpens),
        (OModulePresheaf.ofModules πX F).obj U.1 ⊗[k] (OModulePresheaf.ofModules πY G).obj V.1 ≃ₗ[k]
          (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
            ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
              (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).obj
            (pullback.fst πX πY ⁻¹ᵁ U.1 ⊓ pullback.snd πX πY ⁻¹ᵁ V.1),
      ∀ (U U' : X.affineOpens) (V V' : Y.affineOpens) (hU : U'.1 ≤ U.1) (hV : V'.1 ≤ V.1)
        (s : (OModulePresheaf.ofModules πX F).obj U.1) (t : (OModulePresheaf.ofModules πY G).obj V.1),
        (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
            ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
              (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).res
          (inf_le_inf ((pullback.fst πX πY).preimage_mono hU) ((pullback.snd πX πY).preimage_mono hV))
          (e U V (s ⊗ₜ t)) =
        e U' V' ((OModulePresheaf.ofModules πX F).res hU s ⊗ₜ (OModulePresheaf.ofModules πY G).res hV t) := by
  refine ⟨fun U V => LinearEquiv.ofBijective (fwd πX πY F G U.1 V.1) (fwd_bijective πX πY F G hF hG U V), ?_⟩
  intro U U' V V' hU hV s t
  change (NN πX πY F G).presheaf.map (homOfLE (box_mono πX πY hU hV)).op
      (tensorSections (ρ₁ πX πY F U.1 V.1 s) (ρ₂ πX πY G U.1 V.1 t)) =
    fwd πX πY F G U'.1 V'.1 (F.presheaf.map (homOfLE hU).op s ⊗ₜ G.presheaf.map (homOfLE hV).op t)
  rw [fwd_tmul, map_homOfLE_tensorSections, map_ρ₁ πX πY F hU hV, map_ρ₂ πX πY G hU hV]

end

end S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible (solution)
