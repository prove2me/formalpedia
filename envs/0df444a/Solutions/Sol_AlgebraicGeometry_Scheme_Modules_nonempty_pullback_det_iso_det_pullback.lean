-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_det_iso_det_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/656fc14b-f65b-56f3-a1c1-6e0d5e536973

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.det Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens grothendieckTopology Modules.map_smul PresheafOfModules Modules.det Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf Hom.app_smul pushforward pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.app pullbackPushforwardAdjunction map_smul presheafExteriorPower exteriorPower det IsLocallyFreeOfRank IsInvertible pullback_locally_mem_span_unit isInvertible_det_of_isLocallyFreeOfRank IsInvertible.isIso_of_locallySurjective"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace DetPullback

variable {X Y : Scheme.{u}} (ψ : X ⟶ Y) (n : ℕ) (E : Y.Modules)

noncomputable abbrev F : X.Modules := (Modules.pullback ψ).obj E

noncomputable abbrev pre {Z : Scheme.{u}} (M : Z.Modules) : Z.PresheafOfModules :=
  (presheafExteriorPower Z n).obj M.val

noncomputable def eta (U : Y.Opens) (e : Γ(E, U)) : Γ(F ψ E, ψ ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction ψ).unit.app E).app U e

lemma eta_add (U : Y.Opens) (e e' : Γ(E, U)) : eta ψ E U (e + e') = eta ψ E U e + eta ψ E U e' :=
  map_add _ e e'

lemma eta_sum (U : Y.Opens) {ι : Type*} (T : Finset ι) (f : ι → Γ(E, U)) :
    eta ψ E U (∑ t ∈ T, f t) = ∑ t ∈ T, eta ψ E U (f t) :=
  map_sum (((pullbackPushforwardAdjunction ψ).unit.app E).app U).hom f T

lemma eta_smul (U : Y.Opens) (r : Γ(Y, U)) (e : Γ(E, U)) :
    eta ψ E U (r • e) = ψ.app U r • eta ψ E U e :=
  Modules.Hom.app_smul _ r e

noncomputable def toSh {Z : Scheme.{u}} (M : Z.Modules) (W : Z.Opens) :
    (⋀[Γ(Z, W)]^n Γ(M, W)) → Γ(det n M, W) :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W) (show (pre n M).obj (op W) from w)

lemma toSh_add {Z : Scheme.{u}} (M : Z.Modules) (W : Z.Opens) (w w' : ⋀[Γ(Z, W)]^n Γ(M, W)) :
    toSh n M W (w + w') = toSh n M W w + toSh n M W w' :=
  map_add (((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom _ _

lemma toSh_smul {Z : Scheme.{u}} (M : Z.Modules) (W : Z.Opens) (r : Γ(Z, W)) (w : ⋀[Γ(Z, W)]^n Γ(M, W)) :
    toSh n M W (r • w) = r • toSh n M W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom.map_smul r _

lemma toSh_res {Z : Scheme.{u}} (M : Z.Modules) {W W' : Z.Opens} (i : W' ⟶ W) (w : ⋀[Γ(Z, W)]^n Γ(M, W)) :
    (det n M).presheaf.map i.op (toSh n M W w) =
      toSh n M W' (show ⋀[Γ(Z, W')]^n Γ(M, W') from (pre n M).map i.op (show (pre n M).obj (op W) from w)) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app
    (pre n M))).naturality i.op
  have hx := congrArg (fun φ => φ.hom (show (pre n M).obj (op W) from w)) hnat
  exact hx.symm

section compare

variable (U : Y.Opens)

@[reducible] noncomputable def along (N : Type u) [AddCommGroup N] [Module Γ(X, ψ ⁻¹ᵁ U) N] :
    Module Γ(Y, U) N :=
  Module.compHom N (ψ.app U).hom

noncomputable def etaₗ : letI := along ψ U Γ(F ψ E, ψ ⁻¹ᵁ U); Γ(E, U) →ₗ[Γ(Y, U)] Γ(F ψ E, ψ ⁻¹ᵁ U) :=
  letI := along ψ U Γ(F ψ E, ψ ⁻¹ᵁ U)
  { toFun := fun e => eta ψ E U e
    map_add' := eta_add ψ E U
    map_smul' := fun r e => eta_smul ψ E U r e }

set_option backward.isDefEq.respectTransparency false in
noncomputable def ιMultiAlong :
    letI := along ψ U Γ(F ψ E, ψ ⁻¹ᵁ U)
    letI := along ψ U (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U))
    Γ(F ψ E, ψ ⁻¹ᵁ U) [⋀^Fin n]→ₗ[Γ(Y, U)] (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U)) :=
  letI := along ψ U Γ(F ψ E, ψ ⁻¹ᵁ U)
  letI := along ψ U (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U))
  letI : Algebra Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := (ψ.app U).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) Γ(F ψ E, ψ ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { (exteriorPower.ιMulti Γ(X, ψ ⁻¹ᵁ U) n).toMultilinearMap.restrictScalars (Y.presheaf.obj (op U)) with
    map_eq_zero_of_eq' := fun v _ _ h hij =>
      (exteriorPower.ιMulti Γ(X, ψ ⁻¹ᵁ U) n).map_eq_zero_of_eq v h hij }

lemma ιMultiAlong_apply (v : Fin n → Γ(F ψ E, ψ ⁻¹ᵁ U)) :
    ιMultiAlong ψ n E U v = exteriorPower.ιMulti Γ(X, ψ ⁻¹ᵁ U) n v := by
  simp only [ιMultiAlong]
  rfl

lemma etaₗ_apply (e : Γ(E, U)) : etaₗ ψ E U e = eta ψ E U e := rfl

noncomputable def wedgeEtaₗ :
    letI := along ψ U (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U))
    (⋀[Γ(Y, U)]^n Γ(E, U)) →ₗ[Γ(Y, U)] (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U)) :=
  letI := along ψ U Γ(F ψ E, ψ ⁻¹ᵁ U)
  letI := along ψ U (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U))
  exteriorPower.alternatingMapLinearEquiv ((ιMultiAlong ψ n E U).compLinearMap (etaₗ ψ E U))

lemma wedgeEtaₗ_ιMulti (e : Fin n → Γ(E, U)) :
    wedgeEtaₗ ψ n E U (exteriorPower.ιMulti Γ(Y, U) n e) =
      exteriorPower.ιMulti Γ(X, ψ ⁻¹ᵁ U) n (fun i => eta ψ E U (e i)) := by
  letI := along ψ U Γ(F ψ E, ψ ⁻¹ᵁ U)
  letI := along ψ U (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U))
  simp only [wedgeEtaₗ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  rw [ιMultiAlong_apply]
  rfl

lemma wedgeEtaₗ_smul (r : Γ(Y, U)) (w : ⋀[Γ(Y, U)]^n Γ(E, U)) :
    wedgeEtaₗ ψ n E U (r • w) = ψ.app U r • wedgeEtaₗ ψ n E U w := by
  letI := along ψ U (⋀[Γ(X, ψ ⁻¹ᵁ U)]^n Γ(F ψ E, ψ ⁻¹ᵁ U))
  exact (wedgeEtaₗ ψ n E U).map_smul r w

noncomputable def bFun : (⋀[Γ(Y, U)]^n Γ(E, U)) → Γ(det n (F ψ E), ψ ⁻¹ᵁ U) :=
  fun w => toSh n (F ψ E) (ψ ⁻¹ᵁ U) (wedgeEtaₗ ψ n E U w)

lemma bFun_ιMulti (e : Fin n → Γ(E, U)) :
    bFun ψ n E U (exteriorPower.ιMulti Γ(Y, U) n e) =
      toSh n (F ψ E) (ψ ⁻¹ᵁ U) (exteriorPower.ιMulti Γ(X, ψ ⁻¹ᵁ U) n (fun i => eta ψ E U (e i))) := by
  rw [bFun, wedgeEtaₗ_ιMulti]

lemma bFun_add (w w' : ⋀[Γ(Y, U)]^n Γ(E, U)) : bFun ψ n E U (w + w') = bFun ψ n E U w + bFun ψ n E U w' := by
  simp only [bFun, map_add, toSh_add]

lemma bFun_smul (r : Γ(Y, U)) (w : ⋀[Γ(Y, U)]^n Γ(E, U)) :
    bFun ψ n E U (r • w) = ψ.app U r • bFun ψ n E U w := by
  simp only [bFun, wedgeEtaₗ_smul, toSh_smul]

end compare

end DetPullback

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.det Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens grothendieckTopology Modules.map_smul PresheafOfModules Modules.det Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf Hom.app_smul pushforward pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.app pullbackPushforwardAdjunction map_smul presheafExteriorPower exteriorPower det IsLocallyFreeOfRank IsInvertible pullback_locally_mem_span_unit isInvertible_det_of_isLocallyFreeOfRank IsInvertible.isIso_of_locallySurjective"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace DetPullback

variable {X Y : Scheme.{u}} (ψ : X ⟶ Y) (n : ℕ) (E : Y.Modules)

lemma map_eta {U U' : (Y.Opens)ᵒᵖ} (i : U ⟶ U') (e : Γ(E, U.unop)) :
    (((F ψ E).presheaf.map ((Opens.map ψ.base).map i.unop).op :
        Γ(F ψ E, ψ ⁻¹ᵁ U.unop) ⟶ _) (eta ψ E U.unop e) : Γ(F ψ E, ψ ⁻¹ᵁ U'.unop)) =
      eta ψ E U'.unop ((E.presheaf.map i : Γ(E, U.unop) ⟶ _) e) := by
  have hnat := ((pullbackPushforwardAdjunction ψ).unit.app E).mapPresheaf.naturality i
  have hx := ConcreteCategory.congr_hom hnat e
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  exact hx.symm

noncomputable abbrev preMap {Z : Scheme.{u}} (M : Z.Modules) {W W' : Z.Opens} (j : W' ⟶ W)
    (w : ⋀[Γ(Z, W)]^n Γ(M, W)) : ⋀[Γ(Z, W')]^n Γ(M, W') :=
  show ⋀[Γ(Z, W')]^n Γ(M, W') from (pre n M).map j.op (show (pre n M).obj (op W) from w)

lemma preMap_ιMulti {Z : Scheme.{u}} (M : Z.Modules) {W W' : Z.Opens} (j : W' ⟶ W) (m : Fin n → Γ(M, W)) :
    preMap n M j (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun k => (M.presheaf.map j.op : Γ(M, W) ⟶ _) (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti n M.val j.op m

lemma preMap_add {Z : Scheme.{u}} (M : Z.Modules) {W W' : Z.Opens} (j : W' ⟶ W)
    (w w' : ⋀[Γ(Z, W)]^n Γ(M, W)) : preMap n M j (w + w') = preMap n M j w + preMap n M j w' :=
  map_add ((pre n M).map j.op).hom _ _

lemma preMap_smul {Z : Scheme.{u}} (M : Z.Modules) {W W' : Z.Opens} (j : W' ⟶ W)
    (r : Γ(Z, W)) (w : ⋀[Γ(Z, W)]^n Γ(M, W)) :
    preMap n M j (r • w) = Z.presheaf.map j.op r • preMap n M j w :=
  (pre n M).map_smul j.op r (show (pre n M).obj (op W) from w)

lemma bFun_natural {U U' : Y.Opens} (i : U' ⟶ U) (w : ⋀[Γ(Y, U)]^n Γ(E, U)) :
    bFun ψ n E U' (preMap n E i w) =
      ((det n (F ψ E)).presheaf.map ((Opens.map ψ.base).map i).op :
        Γ(det n (F ψ E), ψ ⁻¹ᵁ U) ⟶ Γ(det n (F ψ E), ψ ⁻¹ᵁ U')) (bFun ψ n E U w) := by
  have hw : w ∈ Submodule.span Γ(Y, U) (Set.range (exteriorPower.ιMulti Γ(Y, U) n (M := Γ(E, U)))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, rfl⟩ := hw
    rw [preMap_ιMulti, bFun_ιMulti, bFun_ιMulti, toSh_res]
    change _ = toSh n (F ψ E) (ψ ⁻¹ᵁ U') (preMap n (F ψ E) ((Opens.map ψ.base).map i) _)
    rw [preMap_ιMulti]
    have hfun : (fun k => ((F ψ E).presheaf.map ((Opens.map ψ.base).map i).op :
          Γ(F ψ E, ψ ⁻¹ᵁ U) ⟶ Γ(F ψ E, ψ ⁻¹ᵁ U')) (eta ψ E U (m k))) =
        fun k => eta ψ E U' ((E.presheaf.map i.op : Γ(E, U) ⟶ Γ(E, U')) (m k)) :=
      funext fun k => map_eta ψ E i.op (m k)
    exact congrArg (fun v : Fin n → Γ(F ψ E, ψ ⁻¹ᵁ U') =>
      toSh n (F ψ E) (ψ ⁻¹ᵁ U') (exteriorPower.ιMulti Γ(X, ψ ⁻¹ᵁ U') n v)) hfun.symm
  | zero =>
    rw [show preMap n E i (0 : ⋀[Γ(Y, U)]^n Γ(E, U)) = 0 from map_zero ((pre n E).map i.op).hom]
    have h0 : bFun ψ n E U (0 : ⋀[Γ(Y, U)]^n Γ(E, U)) = 0 := by
      have h := bFun_add ψ n E U 0 0
      rw [add_zero] at h
      exact left_eq_add.mp h
    have h0' : bFun ψ n E U' (0 : ⋀[Γ(Y, U')]^n Γ(E, U')) = 0 := by
      have h := bFun_add ψ n E U' 0 0
      rw [add_zero] at h
      exact left_eq_add.mp h
    rw [h0, h0', map_zero]
  | add w w' _ _ h h' => rw [preMap_add, bFun_add, h, h', bFun_add, map_add]
  | smul r w _ h =>
    rw [preMap_smul, bFun_smul, h, bFun_smul, Modules.map_smul]
    congr 1
    have := ConcreteCategory.congr_hom (ψ.naturality i.op) r
    simp only [ConcreteCategory.comp_apply, Quiver.Hom.unop_op] at this
    exact this

noncomputable abbrev tgt : Y.PresheafOfModules :=
  (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj ((pushforward ψ).obj (det n (F ψ E))).val

lemma bFun_zero (U : Y.Opens) : bFun ψ n E U 0 = 0 := by
  have h := bFun_add ψ n E U 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

noncomputable def bAb : (pre n E).presheaf ⟶ (tgt ψ n E).presheaf where
  app U := AddCommGrpCat.ofHom (X := ⋀[Γ(Y, U.unop)]^n Γ(E, U.unop)) (Y := Γ(det n (F ψ E), ψ ⁻¹ᵁ U.unop))
    { toFun := bFun ψ n E U.unop
      map_zero' := bFun_zero ψ n E U.unop
      map_add' := bFun_add ψ n E U.unop }
  naturality {U U'} i := by
    ext w
    exact bFun_natural ψ n E i.unop w

noncomputable def bHom : pre n E ⟶ tgt ψ n E :=
  PresheafOfModules.homMk (bAb ψ n E) (fun U r w => by
    change bFun ψ n E U.unop (r • w) = ψ.app U.unop r • bFun ψ n E U.unop w
    exact bFun_smul ψ n E U.unop r w)

noncomputable def β : det n E ⟶ (pushforward ψ).obj (det n (F ψ E)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv (pre n E)
    ((pushforward ψ).obj (det n (F ψ E)))).symm (bHom ψ n E)

noncomputable def α : (Modules.pullback ψ).obj (det n E) ⟶ det n (F ψ E) :=
  ((pullbackPushforwardAdjunction ψ).homEquiv (det n E) (det n (F ψ E))).symm (β ψ n E)

lemma β_toSh (U : Y.Opens) (w : ⋀[Γ(Y, U)]^n Γ(E, U)) :
    (β ψ n E).app U (toSh n E U w) = bFun ψ n E U w := by
  have h3 : ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv (pre n E)
      ((pushforward ψ).obj (det n (F ψ E)))) (β ψ n E) = bHom ψ n E := Equiv.apply_symm_apply _ _
  rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply] at h3
  have h4 := congrArg (fun γ : pre n E ⟶ tgt ψ n E =>
    (((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map γ).app (op U))
      (show ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj (pre n E)).obj (op U) from w)) h3
  simp only [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h4
  exact h4

lemma α_unit_toSh (U : Y.Opens) (e : Fin n → Γ(E, U)) :
    (α ψ n E).app (ψ ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction ψ).unit.app (det n E)).app U
          (toSh n E U (exteriorPower.ιMulti _ n e))) =
      toSh n (F ψ E) (ψ ⁻¹ᵁ U) (exteriorPower.ιMulti _ n (fun i => eta ψ E U (e i))) := by
  have h1 : ((pullbackPushforwardAdjunction ψ).homEquiv _ _) (α ψ n E) = β ψ n E :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h1
  have h2 := congrArg (fun γ => (Modules.Hom.app γ U) (toSh n E U (exteriorPower.ιMulti _ n e))) h1
  simp only [Modules.Hom.comp_app] at h2
  rw [β_toSh, bFun_ιMulti] at h2
  exact h2

end DetPullback

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.det Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens grothendieckTopology Modules.map_smul PresheafOfModules Modules.det Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf Hom.app_smul pushforward pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.app pullbackPushforwardAdjunction map_smul presheafExteriorPower exteriorPower det IsLocallyFreeOfRank IsInvertible pullback_locally_mem_span_unit isInvertible_det_of_isLocallyFreeOfRank IsInvertible.isIso_of_locallySurjective"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace DetPullback

variable {X Y : Scheme.{u}} (ψ : X ⟶ Y) (n : ℕ) (E : Y.Modules)

noncomputable abbrev res {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (s : Γ(M, W)) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op s

lemma res_res {Z : Scheme.{u}} (M : Z.Modules) {W₁ W₂ W₃ : Z.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : Γ(M, W₁)) : res M h₃₂ (res M h₂₁ s) = res M (h₃₂.trans h₂₁) s := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_eq_map {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (f : W' ⟶ W) (s : Γ(M, W)) :
    M.presheaf.map f.op s = res M f.le s := by
  rw [Subsingleton.elim f (homOfLE f.le)]

lemma res_smul {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (r : Γ(Z, W)) (s : Γ(M, W)) :
    res M h (r • s) = Z.presheaf.map (homOfLE h).op r • res M h s :=
  Modules.map_smul M (homOfLE h) r s

lemma res_add {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (s t : Γ(M, W)) :
    res M h (s + t) = res M h s + res M h t := map_add _ s t

lemma res_sum {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) {ι : Type*} (T : Finset ι)
    (s : ι → Γ(M, W)) : res M h (∑ t ∈ T, s t) = ∑ t ∈ T, res M h (s t) := map_sum _ s T

lemma app_res {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) {W' W : Z.Opens} (h : W' ≤ W) (s : Γ(M, W)) :
    φ.app W' (res M h s) = res N h (φ.app W s) := by
  have hnat := φ.mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat s
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  exact hx

lemma preMap_comp {Z : Scheme.{u}} (M : Z.Modules) {W₁ W₂ W₃ : Z.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (w : ⋀[Γ(Z, W₁)]^n Γ(M, W₁)) :
    preMap n M (homOfLE h₃₂) (preMap n M (homOfLE h₂₁) w) = preMap n M (homOfLE (h₃₂.trans h₂₁)) w := by
  change ((pre n M).presheaf.map (homOfLE h₂₁).op ≫ (pre n M).presheaf.map (homOfLE h₃₂).op)
    (show (pre n M).presheaf.obj (op W₁) from w) = _
  rw [← Functor.map_comp]
  rfl

lemma preMap_zero {Z : Scheme.{u}} (M : Z.Modules) {W W' : Z.Opens} (j : W' ⟶ W) :
    preMap n M j (0 : ⋀[Γ(Z, W)]^n Γ(M, W)) = 0 :=
  map_zero ((pre n M).map j.op).hom

lemma res_toSh {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (w : ⋀[Γ(Z, W)]^n Γ(M, W)) :
    res (det n M) h (toSh n M W w) = toSh n M W' (preMap n M (homOfLE h) w) :=
  toSh_res n M (homOfLE h) w

lemma res_eta {V U : Y.Opens} (h : U ≤ V) (e : Γ(E, V)) :
    res (F ψ E) (ψ.preimage_mono h) (eta ψ E V e) = eta ψ E U (res E h e) := by
  have := map_eta ψ E (homOfLE h).op e
  rw [res_eq_map] at this
  exact this

lemma ιMulti_comp_mem {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ}
    (w : Fin m → M) (P : Submodule A (⋀[A]^m M)) (hP : exteriorPower.ιMulti A m w ∈ P)
    (φ : Fin m → Fin m) : exteriorPower.ιMulti A m (w ∘ φ) ∈ P := by
  by_cases hφ : Function.Injective φ
  · have hbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφ
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective φ hbij
    have : (w ∘ φ) = w ∘ σ := rfl
    rw [this, AlternatingMap.map_perm]
    exact P.smul_of_tower_mem _ hP
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hφ
    have : exteriorPower.ιMulti A m (w ∘ φ) = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ (w ∘ φ) (by simp [hij]) hne
    rw [this]
    exact P.zero_mem

lemma ιMulti_mem_span_singleton {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    (g : Fin n → M) (a : Fin n → Fin n → A) :
    exteriorPower.ιMulti A n (fun t => ∑ k, a t k • g k) ∈ Submodule.span A {exteriorPower.ιMulti A n g} := by
  classical
  have hsum := (exteriorPower.ιMulti A n (M := M)).toMultilinearMap.map_sum (fun t k => a t k • g k)
  change exteriorPower.ιMulti A n (fun t => ∑ k, a t k • g k) = _ at hsum
  rw [hsum]
  refine Submodule.sum_mem _ fun r _ => ?_
  have hsm := (exteriorPower.ιMulti A n (M := M)).toMultilinearMap.map_smul_univ (fun t => a t (r t)) (fun t => g (r t))
  change exteriorPower.ιMulti A n (fun t => a t (r t) • g (r t)) =
    (∏ t, a t (r t)) • exteriorPower.ιMulti A n (fun t => g (r t)) at hsm
  change exteriorPower.ιMulti A n (fun t => a t (r t) • g (r t)) ∈ _
  rw [hsm]
  exact Submodule.smul_mem _ _ (ιMulti_comp_mem g _ (Submodule.subset_span (Set.mem_singleton _)) r)

section frame

variable {V : Y.Opens} (e : Fin n → Γ(E, V))

noncomputable def gsec {W : X.Opens} (hW : W ≤ ψ ⁻¹ᵁ V) : Fin n → Γ(F ψ E, W) :=
  fun j => res (F ψ E) hW (eta ψ E V (e j))

lemma res_gsec {W W' : X.Opens} (hW : W ≤ ψ ⁻¹ᵁ V) (h : W' ≤ W) (j : Fin n) :
    res (F ψ E) h (gsec ψ n E e hW j) = gsec ψ n E e (h.trans hW) j :=
  res_res _ _ _ _

variable (hb : ∀ (U' : Y.Opens) (hU' : U' ≤ V), ∃ b : Module.Basis (Fin n) Γ(Y, U') Γ(E, U'),
  ∀ i, b i = E.presheaf.map (homOfLE hU').op (e i))
variable {x : X} (hxV : ψ.base x ∈ V)

include hb hxV in

lemma sect {W : X.Opens} (s : Γ(F ψ E, W)) (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ≤ W) (j : W' ≤ ψ ⁻¹ᵁ V), x ∈ W' ∧ ∃ a : Fin n → Γ(X, W'),
      res (F ψ E) i s = ∑ k, a k • gsec ψ n E e j k := by
  obtain ⟨U, W', i, j, hUV, hxW', hmem⟩ := pullback_locally_mem_span_unit ψ E s hx hxV
  have j' : W' ≤ ψ ⁻¹ᵁ V := j.trans (ψ.preimage_mono hUV)
  refine ⟨W', i, j', hxW', ?_⟩
  obtain ⟨b, hb'⟩ := hb U hUV
  have hle : Submodule.span Γ(X, W') (Set.range fun e' : Γ(E, U) => res (F ψ E) j (eta ψ E U e')) ≤
      Submodule.span Γ(X, W') (Set.range (gsec ψ n E e j')) := by
    rw [Submodule.span_le]
    rintro _ ⟨e', rfl⟩
    have he' : e' = ∑ k, b.repr e' k • res E hUV (e k) := by
      conv_lhs => rw [← b.sum_repr e']
      simp only [hb']
    show res (F ψ E) j (eta ψ E U e') ∈ _
    rw [he', eta_sum, res_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [eta_smul, res_smul, ← res_eta, res_res]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hle hmem)
  exact ⟨c, hc.symm⟩

include hb hxV in

lemma sectFin : ∀ (m : ℕ) {W : X.Opens} (y : Fin m → Γ(F ψ E, W)) (_ : x ∈ W),
    ∃ (W' : X.Opens) (i : W' ≤ W) (j : W' ≤ ψ ⁻¹ᵁ V), x ∈ W' ∧ ∃ a : Fin m → Fin n → Γ(X, W'),
      ∀ t, res (F ψ E) i (y t) = ∑ k, a t k • gsec ψ n E e j k
  | 0, W, y, hx => ⟨W ⊓ ψ ⁻¹ᵁ V, inf_le_left, inf_le_right, ⟨hx, hxV⟩, fun t => t.elim0, fun t => t.elim0⟩
  | m + 1, W, y, hx => by
    obtain ⟨W₁, i₁, j₁, hx₁, a₁, ha₁⟩ := sectFin m (fun t => y t.succ) hx
    obtain ⟨W₂, i₂, j₂, hx₂, a₀, ha₀⟩ := sect ψ n E e hb hxV (res (F ψ E) i₁ (y 0)) hx₁
    refine ⟨W₂, i₂.trans i₁, j₂, hx₂,
      Fin.cons a₀ (fun t k => X.presheaf.map (homOfLE i₂).op (a₁ t k)), fun t => ?_⟩
    refine Fin.cases ?_ (fun t => ?_) t
    · rw [Fin.cons_zero, ← res_res (F ψ E) i₁ i₂]
      exact ha₀
    · rw [Fin.cons_succ, ← res_res (F ψ E) i₁ i₂, ha₁ t, res_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [res_smul, res_gsec]

include hb hxV in

lemma wedge_local {W : X.Opens} (w : ⋀[Γ(X, W)]^n Γ(F ψ E, W)) (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ≤ W) (j : W' ≤ ψ ⁻¹ᵁ V), x ∈ W' ∧ ∃ r : Γ(X, W'),
      preMap n (F ψ E) (homOfLE i) w = r • exteriorPower.ιMulti _ n (gsec ψ n E e j) := by
  have hw : w ∈ Submodule.span Γ(X, W) (Set.range (exteriorPower.ιMulti Γ(X, W) n (M := Γ(F ψ E, W)))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, rfl⟩ := hw
    obtain ⟨W', i, j, hx', a, ha⟩ := sectFin ψ n E e hb hxV n y hx
    refine ⟨W', i, j, hx', ?_⟩
    rw [preMap_ιMulti]
    have hfun : (fun t => ((F ψ E).presheaf.map (homOfLE i).op : Γ(F ψ E, W) ⟶ Γ(F ψ E, W')) (y t)) =
        fun t => ∑ k, a t k • gsec ψ n E e j k := funext ha
    rw [hfun]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (ιMulti_mem_span_singleton n (gsec ψ n E e j) a)
    exact ⟨c, hc.symm⟩
  | zero =>
    exact ⟨W ⊓ ψ ⁻¹ᵁ V, inf_le_left, inf_le_right, ⟨hx, hxV⟩, 0, by rw [preMap_zero, zero_smul]⟩
  | add w w' _ _ h h' =>
    obtain ⟨W₁, i₁, j₁, hx₁, r₁, hr₁⟩ := h
    obtain ⟨W₂, i₂, j₂, hx₂, r₂, hr₂⟩ := h'
    refine ⟨W₁ ⊓ W₂, inf_le_left.trans i₁, inf_le_left.trans j₁, ⟨hx₁, hx₂⟩,
      X.presheaf.map (homOfLE inf_le_left).op r₁ + X.presheaf.map (homOfLE inf_le_right).op r₂, ?_⟩
    rw [preMap_add, add_smul]
    congr 1
    · rw [← preMap_comp n (F ψ E) i₁ inf_le_left, hr₁, preMap_smul, preMap_ιMulti]
      congr 2
      funext k
      exact res_gsec ψ n E e j₁ inf_le_left k
    · rw [show (inf_le_left : W₁ ⊓ W₂ ≤ W₁).trans i₁ = (inf_le_right : W₁ ⊓ W₂ ≤ W₂).trans i₂ from rfl,
        ← preMap_comp n (F ψ E) i₂ inf_le_right, hr₂, preMap_smul, preMap_ιMulti]
      congr 2
      funext k
      exact res_gsec ψ n E e j₂ inf_le_right k
  | smul r w _ h =>
    obtain ⟨W₁, i₁, j₁, hx₁, r₁, hr₁⟩ := h
    refine ⟨W₁, i₁, j₁, hx₁, X.presheaf.map (homOfLE i₁).op r * r₁, ?_⟩
    rw [preMap_smul, hr₁, smul_smul]

end frame

lemma α_locallySurjective (hE : IsLocallyFreeOfRank n E) (W : X.Opens) (c : Γ(det n (F ψ E), W))
    (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ (det n (F ψ E)).presheaf.map (homOfLE i).op c ∈
      Set.range ((α ψ n E).app V) := by
  obtain ⟨VY, hxVY, e, hb⟩ := hE.exists_basis (ψ.base x)

  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n (F ψ E)).presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n (F ψ E)).presheaf))
  obtain ⟨W₁, ι₁, ⟨w, hw⟩, hx₁⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  obtain ⟨W₂, i₂, j₂, hx₂, r, hr⟩ :=
    wedge_local ψ n E e hb hxVY (show ⋀[Γ(X, W₁)]^n Γ(F ψ E, W₁) from w) hx₁
  refine ⟨W₂, i₂.trans ι₁, hx₂, ?_⟩

  let z : Γ((Modules.pullback ψ).obj (det n E), ψ ⁻¹ᵁ VY) :=
    ((pullbackPushforwardAdjunction ψ).unit.app (det n E)).app VY (toSh n E VY (exteriorPower.ιMulti _ n e))
  refine ⟨r • res ((Modules.pullback ψ).obj (det n E)) j₂ z, ?_⟩
  rw [Modules.Hom.app_smul, app_res, α_unit_toSh]

  have hc : res (det n (F ψ E)) ι₁ c = toSh n (F ψ E) W₁ (show ⋀[Γ(X, W₁)]^n Γ(F ψ E, W₁) from w) :=
    hw.symm
  change _ = res (det n (F ψ E)) (i₂.trans ι₁) c
  rw [← res_res (det n (F ψ E)) ι₁ i₂, hc, res_toSh, res_toSh, hr, toSh_smul, preMap_ιMulti]
  rfl

theorem nonempty_iso (hE : IsLocallyFreeOfRank n E) :
    Nonempty ((Modules.pullback ψ).obj (det n E) ≅ det n (F ψ E)) := by
  have hL : IsInvertible ((Modules.pullback ψ).obj (det n E)) :=
    (isInvertible_det_of_isLocallyFreeOfRank hE).pullback ψ
  have hL' : IsInvertible (det n (F ψ E)) := isInvertible_det_of_isLocallyFreeOfRank (hE.pullback ψ)
  have : IsIso (α ψ n E) :=
    IsInvertible.isIso_of_locallySurjective hL hL' (α ψ n E) (fun W c x hx => α_locallySurjective ψ n E hE W c x hx)
  exact ⟨asIso (α ψ n E)⟩

end DetPullback

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) (n : ℕ) {E : Y.Modules} (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Nonempty ((Scheme.Modules.pullback ψ).obj (Scheme.Modules.det n E) ≅
      Scheme.Modules.det n ((Scheme.Modules.pullback ψ).obj E)) :=
  AlgebraicGeometry.Scheme.Modules.DetPullback.nonempty_iso ψ n E hE

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback (solution)
