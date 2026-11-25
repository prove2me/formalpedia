-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:30.526801+00:00
-- url     : https://prove2.me/theorems/8b5cf48c-a95c-401b-9f09-ce9c928c9a4e
-- title:
--   Gt Act Iff Eq Gt Smul
-- statement:
--   Definitions and structural lemmas for Gt Act Iff Eq Gt Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Theorems.Thm_GlobalTheory_TorusExt_add_val
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ros_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Rosati
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
def IsRos (L : LB A.left) (f g : A ⟶ A) (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)
variable {L : LB A.left}
theorem IsRos.val_origin {f g : A ⟶ A} {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsRos L f g u)
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this
omit [IsCommMonObj A] in
theorem val_pull_pair {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (a b : T ⟶ A) :
    val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
theorem pair_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J)
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ A).left) {z : Z} {J} (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF ((snd A A).left ≫ A.hom) _
    (by rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)))
    (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) hu hu' h Z r z J hJ
variable (hG : GlobalFnsSt) (hA : IsAbelianScheme A)
include hG hA
theorem IsRos.unique (hL : L.IsLB) {f g : A ⟶ A} {u u' : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    (hu : IsRos L f g u) (hu' : IsRos L f g u') {T : Over S} {z : T.left} {J} (hJ : Good L z J) (x w : T ⟶ A) :
    val₂ u z J x w = val₂ u' z J x w :=
  pair_unique hG hA hL (fun _ _ _ => rfl) hu.1 hu'.1
    (fun _ _ hI => (hu.val_origin hI).trans (hu'.val_origin hI).symm) _ hJ
theorem IsRos.val_id (hL : L.IsLB) {f g : A ⟶ A} (hf : f = 𝟙 A) (hg : g = 𝟙 A)
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsRos L f g u) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x w : T ⟶ A) : val₂ u z J x w = 1 := by
  subst hf hg
  have := pair_unique hG hA hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (u := LB.pullGen L _ _ u (lift (fst A A) (snd A A)).left) (u' := LB.oneGen L) (fun U _ h => by
      rw [prod_ros, Category.comp_id, Category.comp_id, Fintype.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel) (pullGen_isGen _ _ _ _ hu.1 _)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    (fun y I hI => by rw [val_pull_pair u _ hI, lift_fst, lift_snd, hu.val_origin hI, val_one]) (lift x w).left hJ
  rwa [val_pull_pair u _ hJ, lift_fst, lift_snd, val_one] at this
theorem IsRos.val_comp (hL : L.IsLB) {f g f₁ g₁ f₂ g₂ : A ⟶ A} [IsMonHom f₁] [IsMonHom g₂] (hf : f = f₁ ≫ f₂)
    (hg : g = g₂ ≫ g₁) {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsRos L f g u) (hu₁ : IsRos L f₁ g₁ u₁) (hu₂ : IsRos L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x w : T ⟶ A) :
    val₂ u z J x w = val₂ u₂ z J (x ≫ f₁) w * val₂ u₁ z J x (w ≫ g₂) := by
  subst hf hg
  have ev : ∀ {T : Over S} {z : T.left} {J}, Good L z J → ∀ x w : T ⟶ A,
      val (LB.pullGen L _ _ u (lift (fst A A) (snd A A)).left) (lift x w).left z J = val₂ u z J x w ∧
      val (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u₂ (lift (fst A A ≫ f₁) (snd A A)).left)
        (LB.pullGen L _ _ u₁ (lift (fst A A) (snd A A ≫ g₂)).left)) (lift x w).left z J =
        val₂ u₂ z J (x ≫ f₁) w * val₂ u₁ z J x (w ≫ g₂) := fun hJ x w =>
    ⟨by rw [val_pull_pair u _ hJ, lift_fst, lift_snd], by
      rw [val_mul hJ, val_pull_pair u₂ _ hJ, val_pull_pair u₁ _ hJ, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]⟩
  refine (ev hJ x w).1.symm.trans (Eq.trans (pair_unique hG hA hL (fun U _ h => ?_) (pullGen_isGen _ _ _ _ hu.1 _)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₂.1 _) (pullGen_isGen _ _ _ _ hu₁.1 _))
    (fun y I hI => ?_) _ hJ) (ev hJ x w).2)
  · refine (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros _ _ _ _ h) (prod_ros _ _ _ _ h)).trans ?_
    rw [prod_ros, Category.assoc, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (ev hI 1 1).1.trans (Eq.trans ?_ (ev hI 1 1).2.symm)
    rw [MonObj.one_comp, MonObj.one_comp, hu.val_origin hI, hu₁.val_origin hI, hu₂.val_origin hI, _root_.mul_one]
theorem IsRos.val_sum {Lr : RigLB A} (c : CubicalStr A Lr) {f g f₁ g₁ f₂ g₂ : A ⟶ A} [IsMonHom f₁] [IsMonHom g₁]
    (hf : f = f₁ * f₂) (hg : g = g₁ * g₂) {u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsRos Lr.L f g u) (hu₁ : IsRos Lr.L f₁ g₁ u₁) (hu₂ : IsRos Lr.L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x w : T ⟶ A) :
    val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) =
      cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := by
  subst hf hg
  have ev : ∀ {T : Over S} {z : T.left} {J}, Good Lr.L z J → ∀ x w : T ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (fst A A) (snd A A)).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (snd A A ≫ g₁) (snd A A ≫ g₂))).left))
        (lift x w).left z J = val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) ∧
      val (LB.mulGen Lr.L _ _ _ _
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (lift (fst A A) (snd A A)).left)
          (LB.pullGen Lr.L _ _ u₂ (lift (fst A A) (snd A A)).left))) (lift x w).left z J =
        cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := fun hJ x w =>
    ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull_pair u _ hJ _ _) (val_cub c _ hJ _ _ _))).trans (by
      rw [lift_snd_assoc, lift_snd_assoc, lift_fst, lift_snd]),
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull_pair u₁ _ hJ _ _) (val_pull_pair u₂ _ hJ _ _))))).trans (by
      rw [lift_fst_assoc, lift_fst_assoc, lift_fst, lift_snd])⟩
  refine (ev hJ x w).1.symm.trans (Eq.trans (pair_unique hG hA Lr.isLB (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ c.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _)
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₁.1 _) (pullGen_isGen _ _ _ _ hu₂.1 _)))
    (fun y I hI => ?_) _ hJ) (ev hJ x w).2)
  · refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := U) _ (prod_cub _ _ _ h)
      (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros _ _ _ _ h) (prod_ros _ _ _ _ h))).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := U) _ (prod_ros _ _ _ _ h) (prod_cub _ _ _ h)).symm)
    rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV c y I) := isCub_cubV c hI
    refine (ev hI 1 1).1.trans (Eq.trans ?_ (ev hI 1 1).2.symm)
    rw [hu.val_origin hI, hu₁.val_origin hI, hu₂.val_origin hI, C.face, C.face₃, _root_.mul_one, _root_.mul_one]
end Rosati
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup
section Action
variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]
theorem cPoint_smul (oa : D.OAct O) (T : Over (Spec (CommRingCat.of R))) (a : O) (χ : D.X) :
    cP D T (a • χ) = cP D T χ ≫ oa.onB.act a := by
  rw [cP, oa.c_lin, ← Category.assoc]; rfl
theorem exists_isRos (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) :
    ∃ u, IsRos D.P.L (oa.onB.act (star a)) (oa.onB.act a) u := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  rw [star_star] at hr
  exact exists_ros hG D.P.isAb D.P.isLB _ _ hr
def rosGen (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) := (exists_isRos hG oa a).choose
theorem rosGen_isRos (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) :
    IsRos D.P.L (oa.onB.act (star a)) (oa.onB.act a) (rosGen hG oa a) := (exists_isRos hG oa a).choose_spec
theorem gtAct_iff_val (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      charVal g' χ y J = charVal g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ y J,
      Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := fun u χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · exact (val_corr hJ (h _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _).symm.trans (vv _ χ y J hJ)
  · exact (vv u χ y J hJ).trans ((congrArg₂ (· * ·) rfl
      (IsRos.unique hG D.P.isAb D.P.isLB ⟨hu, u₀⟩ (rosGen_isRos hG oa a) hJ _ _)).trans (h χ y J hJ).symm)
theorem rosGen_add (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J}
    (hJ : Good D.P.L z J) (x x' w : T ⟶ D.P.A) :
    val₂ (rosGen hG oa a) z J (x * x') w * th D z J x x' (w ≫ oa.onB.act a) =
        th D z J (x ≫ oa.onB.act (star a)) (x' ≫ oa.onB.act (star a)) w *
          (val₂ (rosGen hG oa a) z J x w * val₂ (rosGen hG oa a) z J x' w) ∧
      val₂ (rosGen hG oa a) z J w (x * x') * th D z J w (x ≫ oa.onB.act a) (x' ≫ oa.onB.act a) =
        th D z J (w ≫ oa.onB.act (star a)) x x' *
          (val₂ (rosGen hG oa a) z J w x * val₂ (rosGen hG oa a) z J w x') :=
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  ros_add D.cub hG D.P.isAb _ _ _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 hJ x x' w
theorem exists_gtAct (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) (g : GtPtF D F) : ∃ g', GtAct oa a g g' := by
  have := oa.onB.hom (star a)
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ (rosGen hG oa a) (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
      (LB.pullGen D.P.L _ _ (rosGen hG oa a) (lift (cP D _ χ) g.b).left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (rosGen_isRos hG oa a).1 _))
    (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
        (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
      rw [prod_gt, cPoint_smul oa]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      have e := (rosGen_add hG oa a hJ 1 1 g.b).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      refine (vv 0 y J hJ).trans ?_
      rw [smul_zero, cPoint_zero, mul_eq_left.1 e.symm, _root_.mul_one, charVal_zero g hJ]) (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ (cP D _ χ) (cP D _ χ') g.b).1
      have e := charVal_add g hJ (star a • χ) (star a • χ')
      rw [cPoint_smul oa, cPoint_smul oa] at e
      have e₂ := congrArg Additive.ofMul e
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [smul_add, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₂ ⊢
      linear_combination (norm := abel) e₁ + e₂)
  exact ⟨g', (gtAct_iff_val hG _ _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩
def gtSmul (hG : GlobalFnsSt) (oa : D.OAct O) (a : O) (g : GtPtF D F) : GtPtF D F := (exists_gtAct hG oa a g).choose
variable (hG : GlobalFnsSt) (oa : D.OAct O)
theorem gtAct_gtSmul (a : O) (g : GtPtF D F) : GtAct oa a g (gtSmul hG oa a g) := (exists_gtAct hG oa a g).choose_spec
theorem gtSmul_b (a : O) (g : GtPtF D F) : (gtSmul hG oa a g).b = g.b ≫ oa.onB.act a := (gtAct_gtSmul hG oa a g).1
theorem gtSmul_val (a : O) (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (gtSmul hG oa a g) χ y J = charVal g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b :=
  ((gtAct_iff_val hG _ _ _ _).1 (gtAct_gtSmul hG oa a g)).2 χ y J hJ
theorem gtSmul_add (a : O) (g g' : GtPtF D F) : gtSmul hG oa a (g + g') = gtSmul hG oa a g + gtSmul hG oa a g' := by
  have := oa.onB.hom a
  refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩)
  · rw [gtSmul_b, gtSmul_b, gtSmul_b, add_b, MonObj.mul_comp]
  · have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ g.b g'.b (cP D _ χ)).2
    have e := add_val g g' (star a • χ) hJ
    rw [cPoint_smul oa] at e
    have e₂ := congrArg Additive.ofMul e
    rw [gtSmul_val hG oa a _ χ hJ, gtSmul_val hG oa a _ χ hJ, gtSmul_val hG oa a _ χ hJ, gtSmul_b, gtSmul_b, add_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂
theorem one_gtSmul (g : GtPtF D F) : gtSmul hG oa 1 g = g :=
  gt_ext_val (by rw [gtSmul_b, oa.onB.map_one, Category.comp_id]) fun χ y J hJ => by
    rw [gtSmul_val hG oa _ _ χ hJ, IsRos.val_id hG D.P.isAb D.P.isLB (by rw [star_one, oa.onB.map_one])
      oa.onB.map_one (rosGen_isRos hG oa 1) hJ, star_one, one_smul, _root_.mul_one]
theorem mul_gtSmul (a a' : O) (g : GtPtF D F) : gtSmul hG oa (a * a') g = gtSmul hG oa a (gtSmul hG oa a' g) := by
  have := oa.onB.hom a'
  have := oa.onB.hom (star a)
  refine gt_ext_val (by rw [gtSmul_b, gtSmul_b, gtSmul_b, oa.onB.map_mul, Category.assoc]) fun χ y J hJ => ?_
  rw [gtSmul_val hG oa _ _ χ hJ, gtSmul_val hG oa _ _ χ hJ, gtSmul_val hG oa _ _ _ hJ,
    IsRos.val_comp hG D.P.isAb D.P.isLB (by rw [star_mul, oa.onB.map_mul]) (oa.onB.map_mul a a')
      (rosGen_isRos hG oa (a * a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ,
    gtSmul_b, cPoint_smul oa, star_mul, mul_smul, _root_.mul_assoc]
theorem add_gtSmul (a a' : O) (g : GtPtF D F) : gtSmul hG oa (a + a') g = gtSmul hG oa a g + gtSmul hG oa a' g := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩)
  · rw [gtSmul_b, gtSmul_b, gtSmul_b, oa.onB.map_add]; exact MonObj.comp_mul _ _ _
  · have e₁ := congrArg Additive.ofMul (IsRos.val_sum hG D.P.isAb D.cub
      (by rw [star_add]; exact oa.onB.map_add _ _) (oa.onB.map_add a a')
      (rosGen_isRos hG oa (a + a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ (cP D _ χ) g.b)
    have e := charVal_add g hJ (star a • χ) (star a' • χ)
    rw [cPoint_smul oa, cPoint_smul oa, ← add_smul, ← star_add] at e
    have e₂ := congrArg Additive.ofMul e
    rw [gtSmul_val hG oa _ _ χ hJ, gtSmul_val hG oa _ _ χ hJ, gtSmul_val hG oa _ _ χ hJ, gtSmul_b, gtSmul_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, th] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂
@[reducible] def gtModule (F : Type) [Field F] [Algebra (FractionRing R) F] : Module O (GtPtF D F) where
  smul := gtSmul hG oa
  one_smul := one_gtSmul hG oa
  mul_smul := mul_gtSmul hG oa
  smul_zero a := add_left_cancel (a := gtSmul hG oa a 0)
    ((gtSmul_add hG oa a 0 0).symm.trans ((congrArg _ (add_zero _)).trans (add_zero _).symm))
  smul_add := gtSmul_add hG oa
  add_smul := add_gtSmul hG oa
  zero_smul g := add_left_cancel (a := gtSmul hG oa 0 g)
    ((add_gtSmul hG oa 0 0 g).symm.trans ((congrArg (gtSmul hG oa · g) (add_zero _)).trans (add_zero _).symm))
def gtSmulHom (F : Type) [Field F] [Algebra (FractionRing R) F] (a : O) : GtPtF D F →+ GtPtF D F :=
  AddMonoidHom.mk' (gtSmul hG oa a) (gtSmul_add hG oa a)
end Action
section Extension
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
def extMap (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') :
    TF (R := R) F' ⟶ TF (R := R) F :=
  Over.homMk (spMap f) (by
    show spMap f ≫ jFK (R := R) F ≫ jK R = jFK (R := R) F' ≫ jK R
    rw [← Category.assoc, jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf])
variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
theorem exists_ext (g : GtPtF D F) : ∃ g' : GtPtF D F', g'.b = extMap f hf ≫ g.b ∧ ∀ χ y J, Good D.P.L y J →
    charVal g' χ y J = val (g.s χ) (extMap f hf).left y J := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (g.s χ) (extMap f hf).left)
      (𝟙 (TF (R := R) F').left) y J = val (g.s χ) (extMap f hf).left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g', hb, hv⟩ := exists_gt (extMap f hf ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) (extMap f hf).left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _) (fun χ U _ h => by
      refine (prod_gt g.b χ (fun q => h ((extMap f hf).left ≫ q))).trans ?_
      rw [prod_gt, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, comp_cP,
        MonObj.comp_one])
    (fun y J hJ => (vv 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _))) (fun χ χ' y J hJ =>
      (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans ((gt_mul (extMap f hf) hJ g χ χ').trans
        (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm))
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
def gtExt (D : DegPre R) (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') : GtPtF D F →+ GtPtF D F' :=
  AddMonoidHom.mk' (fun g => (exists_ext f hf g).choose) fun g g' => by
    obtain ⟨b, v⟩ := (exists_ext f hf g).choose_spec
    obtain ⟨b', v'⟩ := (exists_ext f hf g').choose_spec
    obtain ⟨b'', v''⟩ := (exists_ext f hf (g + g')).choose_spec
    refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2
      ⟨by rw [b, b', b'', add_b, MonObj.comp_mul], fun χ y J hJ => ?_⟩)
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (extMap f hf) hJ _ _ _))).symm.trans
      ((val_corr hJ ((isAdd_gtAdd g g').2 χ) (extMap f hf).left).trans (val_mul hJ _ _ _))
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', ← comp_cP D (extMap f hf)]
    exact e
end Extension
end GlobalTheory.TorusExt


