-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/03988335-07fb-58ca-8d0a-7ad7dd14f253

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mAffCech

section Eta

variable {V W : Scheme.{u}} (γ : W ⟶ V) (N : V.Modules)

abbrev pb : W.Modules := (Scheme.Modules.pullback γ).obj N

abbrev unitHom : N ⟶ (Scheme.Modules.pushforward γ).obj (pb γ N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction γ).unit.app N

def eta (U : V.Opens) (s : Γ(N, U)) : Γ(pb γ N, γ ⁻¹ᵁ U) := (unitHom γ N).app U s

theorem eta_add (U : V.Opens) (s₁ s₂ : Γ(N, U)) : eta γ N U (s₁ + s₂) = eta γ N U s₁ + eta γ N U s₂ :=
  map_add _ s₁ s₂

theorem eta_smul (U : V.Opens) (a : Γ(V, U)) (s : Γ(N, U)) : eta γ N U (a • s) = γ.app U a • eta γ N U s := by
  unfold eta
  rw [Scheme.Modules.Hom.app_smul]
  rfl

theorem app_map {M M' : V.Modules} (φ : M ⟶ M') {U₁ U₂ : V.Opens} (i : U₁ ⟶ U₂) (x : Γ(M, U₂)) :
    φ.app U₁ (M.presheaf.map i.op x) = M'.presheaf.map i.op (φ.app U₂ x) :=
  PresheafOfModules.naturality_apply φ.val i.op x

theorem map_eta {U₁ U₂ : V.Opens} (i : U₁ ⟶ U₂) (k : γ ⁻¹ᵁ U₁ ⟶ γ ⁻¹ᵁ U₂) (s : Γ(N, U₂)) :
    (pb γ N).presheaf.map k.op (eta γ N U₂ s) = eta γ N U₁ (N.presheaf.map i.op s) := by
  rw [Subsingleton.elim k ((Opens.map γ.base).map i)]
  exact (app_map (unitHom γ N) i s).symm

theorem map_map (M : W.Modules) {W₁ W₂ W₃ : W.Opens} (i : W₁ ⟶ W₂) (j : W₂ ⟶ W₃) (k : W₁ ⟶ W₃) (y : Γ(M, W₃)) :
    M.presheaf.map i.op (M.presheaf.map j.op y) = M.presheaf.map k.op y := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, M.presheaf.map_comp]; rfl

theorem map_self (M : W.Modules) {O : W.Opens} (i : O ⟶ O) (y : Γ(M, O)) : M.presheaf.map i.op y = y := by
  rw [Subsingleton.elim i (𝟙 O), op_id, M.presheaf.map_id]; rfl

end Eta

section Chart

variable {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R)) (γ : W ⟶ V) [IsAffineHom γ]
  (N : V.Modules)

theorem res_rfl {X : Scheme.{u}} (O : X.Opens) (x : Γ(X, O)) : X.presheaf.map (homOfLE (le_refl O)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl O)).op (𝟙 (op O)), X.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : γ.appLE U (γ ⁻¹ᵁ U) le_rfl a = γ.app U a := by
  show W.presheaf.map (homOfLE (le_refl _)).op (γ.app U a) = _
  exact res_rfl _ _

@[reducible] def algVW (U : V.Opens) : Algebra Γ(V, U) Γ(W, γ ⁻¹ᵁ U) := (γ.app U).hom.toAlgebra

def kappa (U : V.Opens) :
    letI := algVW γ U
    (OModulePresheaf.pushforwardUnit π γ).obj U ≃ₗ[Γ(V, U)] Γ(W, γ ⁻¹ᵁ U) :=
  letI := algVW γ U
  { toFun := fun x => (show Γ(W, γ ⁻¹ᵁ U) from x)
    invFun := fun y => (show (OModulePresheaf.pushforwardUnit π γ).obj U from y)
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      show γ.appLE U (γ ⁻¹ᵁ U) le_rfl a * (show Γ(W, γ ⁻¹ᵁ U) from x) = γ.app U a * (show Γ(W, γ ⁻¹ᵁ U) from x)
      rw [appLE_rfl_apply]
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem kappa_apply (U : V.Opens) (x : Γ(W, γ ⁻¹ᵁ U)) :
    kappa π γ U (show (OModulePresheaf.pushforwardUnit π γ).obj U from x) = x := rfl

variable (β : ∀ U : V.affineOpens,
    letI := algVW γ U.1
    Γ(W, γ ⁻¹ᵁ U.1) ⊗[Γ(V, U.1)] Γ(N, U.1) ≃ₗ[Γ(W, γ ⁻¹ᵁ U.1)] Γ(pb γ N, γ ⁻¹ᵁ U.1))
  (hβ : ∀ (U : V.affineOpens) (s : Γ(N, U.1)),
    letI := algVW γ U.1
    β U ((1 : Γ(W, γ ⁻¹ᵁ U.1)) ⊗ₜ[Γ(V, U.1)] s) = eta γ N U.1 s)

abbrev Tobj (U : V.Opens) : Type u :=
  (OModulePresheaf.pushforwardUnit π γ).obj U ⊗[(V.presheaf.obj (op U) : Type u)] (OModulePresheaf.ofModules π N).obj U

def theta (U : V.affineOpens) : Tobj π γ N U.1 →+ Γ(pb γ N, γ ⁻¹ᵁ U.1) :=
  letI := algVW γ U.1
  ((β U).toLinearMap.toAddMonoidHom).comp
    (TensorProduct.congr (kappa π γ U.1) (LinearEquiv.refl Γ(V, U.1) ((OModulePresheaf.ofModules π N).obj U.1))).toLinearMap.toAddMonoidHom

theorem theta_apply (U : V.affineOpens) (x : Tobj π γ N U.1) :
    letI := algVW γ U.1
    theta π γ N β U x = β U (TensorProduct.congr (kappa π γ U.1) (LinearEquiv.refl Γ(V, U.1) ((OModulePresheaf.ofModules π N).obj U.1)) x) := rfl

theorem theta_bijective (U : V.affineOpens) : Function.Bijective (theta π γ N β U) := by
  letI := algVW γ U.1
  exact (β U).bijective.comp (TensorProduct.congr (kappa π γ U.1) (LinearEquiv.refl Γ(V, U.1) ((OModulePresheaf.ofModules π N).obj U.1))).bijective

include hβ in

theorem theta_tmul (U : V.affineOpens) (b : Γ(W, γ ⁻¹ᵁ U.1)) (s : Γ(N, U.1)) :
    theta π γ N β U ((show (OModulePresheaf.pushforwardUnit π γ).obj U.1 from b) ⊗ₜ[Γ(V, U.1)]
      (show (OModulePresheaf.ofModules π N).obj U.1 from s)) = b • eta γ N U.1 s := by
  letI := algVW γ U.1
  rw [theta_apply, TensorProduct.congr_tmul, kappa_apply, LinearEquiv.refl_apply]
  have h1 : β U (b ⊗ₜ[Γ(V, U.1)] s) = b • eta γ N U.1 s := by
    rw [show b ⊗ₜ[Γ(V, U.1)] s = b • ((1 : Γ(W, γ ⁻¹ᵁ U.1)) ⊗ₜ[Γ(V, U.1)] s) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      LinearEquiv.map_smul, hβ]
  exact h1

theorem theta_smulA (U : V.affineOpens) (a : Γ(V, U.1)) (x : Tobj π γ N U.1) :
    theta π γ N β U (a • x) = γ.app U.1 a • theta π γ N β U x := by
  letI := algVW γ U.1
  rw [theta_apply, theta_apply, LinearEquiv.map_smul]
  show β U (algebraMap Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) a • _) = _
  rw [LinearEquiv.map_smul]
  rfl

include hβ in

theorem theta_res {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : Tobj π γ N U'.1) :
    theta π γ N β U (OModulePresheaf.tensorResₛₗ (OModulePresheaf.pushforwardUnit π γ) (OModulePresheaf.ofModules π N) h x) =
      (pb γ N).presheaf.map (homOfLE ((Opens.map γ.base).monotone h)).op (theta π γ N β U' x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b s =>
    rw [OModulePresheaf.tensorResₛₗ_tmul, OModulePresheaf.pushforward_res]
    erw [theta_tmul π γ N β hβ U, theta_tmul π γ N β hβ U']
    rw [Scheme.Modules.map_smul, map_eta γ N (homOfLE h) (homOfLE ((Opens.map γ.base).monotone h))]
    rfl

end Chart

section Complex

variable {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
  (γ : W ⟶ V) [IsAffineHom γ] (K : V.OrderedAffineCover) (N : V.Modules)
  (β : ∀ U : V.affineOpens,
    letI := algVW γ U.1
    Γ(W, γ ⁻¹ᵁ U.1) ⊗[Γ(V, U.1)] Γ(N, U.1) ≃ₗ[Γ(W, γ ⁻¹ᵁ U.1)] Γ(pb γ N, γ ⁻¹ᵁ U.1))
  (hβ : ∀ (U : V.affineOpens) (s : Γ(N, U.1)),
    letI := algVW γ U.1
    β U ((1 : Γ(W, γ ⁻¹ᵁ U.1)) ⊗ₜ[Γ(V, U.1)] s) = eta γ N U.1 s)

local notation "F₁" => OModulePresheaf.ofModules (γ ≫ π) (pb γ N)
local notation "F₂" => OModulePresheaf.twist (OModulePresheaf.pushforwardUnit π γ) N

theorem res_app_algebraMap (U : V.Opens) (O : W.Opens) (hO : O ≤ γ ⁻¹ᵁ U) (r : R) :
    (W.presheaf.map (homOfLE hO).op).hom (γ.app U ((Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r)) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (γ ≫ π) O).algebraMap r := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (γ ≫ π) (γ ⁻¹ᵁ U)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (γ ≫ π) O
  rw [← appLE_rfl_apply γ U, OModulePresheaf.appLE_algebraMap (π := π) γ U r]
  exact (Scheme.TwoAffineOpenCover.restrictAlgHom (γ ≫ π) hO).commutes r

def phiComp {n : ℕ} (s : K.Idx n) : (F₂).obj (K.inter s) →ₗ[R] (F₁).obj ((K.comap γ).inter s) where
  toFun x := (F₁).res (K.comap_inter_le γ s)
    (show (F₁).obj (γ ⁻¹ᵁ K.inter s) from theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from x))
  map_add' x y := by
    show (pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ s)).op
        (theta π γ N β (K.affineInter π s) ((show Tobj π γ N (K.inter s) from x) + (show Tobj π γ N (K.inter s) from y))) =
      (pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ s)).op (theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from x)) +
        (pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ s)).op (theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from y))
    rw [map_add, map_add]
  map_smul' r x := by
    have h1 : theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from r • x) =
        γ.app (K.inter s) ((Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)).algebraMap r) •
          theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from x) :=
      theta_smulA π γ N β (K.affineInter π s) _ _
    show (pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ s)).op
        (theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from r • x)) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (γ ≫ π) ((K.comap γ).inter s)).algebraMap r •
        (pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ s)).op
          (theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from x))
    rw [h1, Scheme.Modules.map_smul, res_app_algebraMap]

theorem phiComp_apply {n : ℕ} (s : K.Idx n) (x : (F₂).obj (K.inter s)) :
    phiComp π γ K N β s x =
      (F₁).res (K.comap_inter_le γ s) (show (F₁).obj (γ ⁻¹ᵁ K.inter s) from
        theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from x)) :=
  rfl

theorem phiComp_bijective {n : ℕ} (s : K.Idx n) : Function.Bijective (phiComp π γ K N β s) := by
  have h1 : Function.Bijective (fun x : (F₂).obj (K.inter s) =>
      theta π γ N β (K.affineInter π s) (show Tobj π γ N (K.inter s) from x)) :=
    theta_bijective π γ N β (K.affineInter π s)
  have h2 : Function.Bijective ((F₁).res (K.comap_inter_le γ s) :
      (F₁).obj (γ ⁻¹ᵁ K.inter s) → (F₁).obj ((K.comap γ).inter s)) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨(F₁).res (K.le_comap_inter γ s) y, ?_⟩⟩
    · have := congrArg ((F₁).res (K.le_comap_inter γ s)) hxy
      rwa [(F₁).res_res, (F₁).res_res, (F₁).res_refl_apply, (F₁).res_refl_apply] at this
    · rw [(F₁).res_res, (F₁).res_refl_apply]
  exact h2.comp h1

def phi (n : ℕ) : (F₂).cochain K n →ₗ[R] (F₁).cochain (K.comap γ) n :=
  LinearMap.pi fun s => (phiComp π γ K N β s).comp (LinearMap.proj s)

theorem phi_apply (n : ℕ) (c : (F₂).cochain K n) (s : K.Idx n) :
    phi π γ K N β n c s = phiComp π γ K N β s (c s) := rfl

theorem phi_bijective (n : ℕ) : Function.Bijective (phi π γ K N β n) := by
  constructor
  · intro c c' h
    funext s
    exact (phiComp_bijective π γ K N β s).1 (by rw [← phi_apply, ← phi_apply, h])
  · intro c'
    refine ⟨fun s => ((phiComp_bijective π γ K N β s).2 (c' s)).choose, funext fun s => ?_⟩
    rw [phi_apply]
    exact ((phiComp_bijective π γ K N β s).2 (c' s)).choose_spec

include hβ in

theorem phiComp_res {n : ℕ} (t : K.Idx (n + 1)) (j : Fin (n + 2)) (y : (F₂).obj (K.inter (K.face t j))) :
    phiComp π γ K N β t ((F₂).res (K.inter_le_inter_face t j) y) =
      (F₁).res ((K.comap γ).inter_le_inter_face t j) (phiComp π γ K N β (K.face t j) y) := by
  have hnat : theta π γ N β (K.affineInter π t)
      (show Tobj π γ N (K.inter t) from (F₂).res (K.inter_le_inter_face t j) y) =
      (pb γ N).presheaf.map (homOfLE ((Opens.map γ.base).monotone (K.inter_le_inter_face t j))).op
        (theta π γ N β (K.affineInter π (K.face t j)) (show Tobj π γ N (K.inter (K.face t j)) from y)) :=
    theta_res π γ N β hβ (U := K.affineInter π t) (U' := K.affineInter π (K.face t j)) (K.inter_le_inter_face t j) _
  rw [phiComp_apply, phiComp_apply]
  show (pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ t)).op
      (theta π γ N β (K.affineInter π t) (show Tobj π γ N (K.inter t) from (F₂).res (K.inter_le_inter_face t j) y)) =
    (pb γ N).presheaf.map (homOfLE ((K.comap γ).inter_le_inter_face t j)).op
      ((pb γ N).presheaf.map (homOfLE (K.comap_inter_le γ (K.face t j))).op
        (theta π γ N β (K.affineInter π (K.face t j)) (show Tobj π γ N (K.inter (K.face t j)) from y)))
  have X : (K.comap γ).inter t ≤ γ ⁻¹ᵁ K.inter (K.face t j) :=
    ((K.comap γ).inter_le_inter_face t j).trans (K.comap_inter_le γ (K.face t j))
  rw [hnat, map_map (pb γ N) _ _ (homOfLE X)]
  exact (map_map (pb γ N) _ _ (homOfLE X) _).symm

include hβ in

theorem d_phi (n : ℕ) (c : (F₂).cochain K n) :
    (F₁).d (K.comap γ) n (phi π γ K N β n c) = phi π γ K N β (n + 1) ((F₂).d K n c) := by
  funext t
  rw [phi_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower, phiComp_res π γ K N β hβ t j, phi_apply]
  rfl

include hβ in
theorem main_of_beta :
    Nonempty ((F₁).H0 (K.comap γ) ≃ₗ[R] (F₂).H0 K) ∧
      ∀ i : ℕ, Nonempty ((F₁).HSucc (K.comap γ) i ≃ₗ[R] (F₂).HSucc K i) := by
  have key := LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    (R := R) (C := fun n => (F₂).cochain K n) (D := fun n => (F₁).cochain (K.comap γ) n)
    (fun n => (F₂).d K n) (fun n => (F₁).d (K.comap γ) n) (fun n => phi π γ K N β n)
    (fun n x => (d_phi π γ K N β hβ n x).symm)
    (fun n x => by
      have := LinearMap.congr_fun ((F₂).d_comp_d K n) x
      exact this)
    (fun n => (phi_bijective π γ K N β n).2)
    (fun x hx _ => (phi_bijective π γ K N β 0).1 (by rw [hx, map_zero]))
    (fun n x hx _ => ⟨0, map_zero _, by
      rw [map_zero]; exact ((phi_bijective π γ K N β (n + 1)).1 (by rw [hx, map_zero])).symm⟩)
  obtain ⟨⟨e0, -⟩, hS⟩ := key
  exact ⟨⟨e0.symm⟩, fun i => by obtain ⟨eS, -⟩ := hS i; exact ⟨eS.symm⟩⟩

end Complex

theorem main {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (γ : W ⟶ V) [IsAffineHom γ] (K : V.OrderedAffineCover) (N : V.Modules)
    (hN : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).H0 (K.comap γ) ≃ₗ[R]
        ((OModulePresheaf.pushforwardUnit π γ).twist N).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).HSucc
          (K.comap γ) i ≃ₗ[R] ((OModulePresheaf.pushforwardUnit π γ).twist N).HSucc K i) := by
  have hNi : Scheme.Modules.IsInvertible N := ⟨hN⟩
  have hβ' : ∀ U : V.affineOpens,
      letI := algVW γ U.1
      ∃ βU : Γ(W, γ ⁻¹ᵁ U.1) ⊗[Γ(V, U.1)] Γ(N, U.1) ≃ₗ[Γ(W, γ ⁻¹ᵁ U.1)] Γ(pb γ N, γ ⁻¹ᵁ U.1),
        ∀ s : Γ(N, U.1), βU (1 ⊗ₜ s) = eta γ N U.1 s := fun U =>
    Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback γ hNi U.1 U.2 (U.2.preimage γ)
  choose β hβ using hβ'
  exact main_of_beta π γ K N β hβ

end P2mAffCech

theorem solution
    {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (γ : W ⟶ V) [IsAffineHom γ] (K : V.OrderedAffineCover) (N : V.Modules)
    (hN : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).H0 (K.comap γ) ≃ₗ[R]
        ((OModulePresheaf.pushforwardUnit π γ).twist N).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).HSucc
          (K.comap γ) i ≃ₗ[R] ((OModulePresheaf.pushforwardUnit π γ).twist N).HSucc K i) :=
  P2mAffCech.main π γ K N hN

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit (solution)
