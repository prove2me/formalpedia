-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:25.104814+00:00
-- url     : https://prove2.me/theorems/3a79c75a-d191-4d7b-879c-1e6e61db945c
-- title:
--   Cubical Of Normalised
-- statement:
--   Definitions and structural lemmas for Cubical Of Normalised, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubicalOfNormalised.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
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
namespace GlobalTheory.AbLaw.Cube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
theorem corr_of_val_section {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {Y : Over S}
    (hY : Function.Surjective Y.hom.appTop.hom) (e : 𝟙_ (Over S) ⟶ Y) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y.left ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y.left ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good L y J → val u e.left y J = val u' e.left y J) : LB.Gen.Corr L φ ε φ' ε' u u' :=
  corr_of_val hL fun y J hJ => gen_unique' hL hF Y.hom e.left (Over.w e) hY hu hu' h _ _ y J hJ
theorem surj_tensor (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S}
    (hT : Function.Surjective T.hom.appTop.hom) : Function.Surjective (A ⊗ T).hom.appTop.hom := by
  rw [← Over.w (snd A T)]
  exact surj_comp (surj_snd hG hA T) hT
variable [IsCommMonObj A] {L : LB A.left}
omit [IsCommMonObj A] in
theorem prod_theta {U : Type} [CommGroup U] (h : ((G3 A).left ⟶ A.left) → U) :
    ∏ I : thK.{0}, h (thφ A (x3 A) I) ^ thε I =
      ∏ I : thK.{0}, h ((lift (x3 A 0) (lift (x3 A 1) (x3 A 2))).left ≫ thφ A (x3 A) I) ^ thε I := by
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by ext <;> simp [x3]
  rw [e]
  exact Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (Category.id_comp _).symm
omit [GrpObj A] [IsCommMonObj A] in
theorem oneGen_isGen {Y : Scheme.{0}} : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
def IsNormalised (t : LB.Gen (Theta A L)) : Prop :=
  ∀ (y : (𝟙_ (Over S)).left) J, Good L y J →
    val (L := L) (φ := thφ A (x3 A)) (ε := thε) t (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1
theorem IsNormalised.pull {t : LB.Gen (Theta A L)} (ht : IsNormalised t) {T : Over S} (e : 𝟙_ (Over S) ⟶ T)
    {a b c : T ⟶ A} (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) {y J} (hJ : Good L y J) :
    val (LB.pullGen L (thφ A (x3 A)) thε t (lift a (lift b c)).left) e.left y J = 1 := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift, ha, hb, hc]
  exact ht y J hJ
def cubicalOfNormalised (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (M : RigLB A) (t : LB.Gen (Theta A M.L))
    (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  have s₁ := (hG _ _ hA).2
  have s₂ := surj_tensor hG hA s₁
  have s₃ := surj_tensor hG hA s₂
  have s₄ := surj_tensor hG hA s₃
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }
end GlobalTheory.AbLaw.Cube


