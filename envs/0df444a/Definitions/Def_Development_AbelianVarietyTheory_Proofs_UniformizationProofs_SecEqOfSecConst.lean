-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:46:20.968273+00:00
-- url     : https://prove2.me/theorems/bfb1f26e-1e51-414e-8969-cece7e88b85a
-- title:
--   Sec Eq Of Sec Const
-- statement:
--   Definitions and structural lemmas for Sec Eq Of Sec Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res__07a02af1eb33
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_isConst_powGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UnifZero
open GlobalTheory.ToricData
section Const
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']
theorem gv_one (V : Y.Opens) : gv 1 V = 1 := map_one _
theorem res_eq_one {U V : Y.Opens} (h : V ≤ U) {x : Γ(Y, U)ˣ} (hx : x = 1) : res h x = 1 := by
  rw [hx, map_one]
theorem res_pullU_eq_one (f : Y' ⟶ Y) {U : Y.Opens} {V : Y'.Opens} (h : V ≤ f ⁻¹ᵁ U) {x : Γ(Y, U)ˣ}
    (hx : x = 1) : res h (pullU f U x) = 1 := by
  rw [hx, map_one, map_one]
theorem mul_eq_one_of {M : Type} [Monoid M] {a b : M} (ha : a = 1) (hb : b = 1) : a * b = 1 := by
  rw [ha, hb, _root_.mul_one]
theorem one_isGen_div {X' : Scheme.{0}} (φ : J → (Y ⟶ X)) (ε : J → ℤ) (φ' : J' → (Y ⟶ X')) (ε' : J' → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.div (LB.LinComb (trivLB X) φ ε) (LB.LinComb (trivLB X') φ' ε'))).IsGen := by
  intro i j
  simp only [LB.div, linComb_triv_g, map_one, inv_one, _root_.mul_one]
  exact (res_eq_one _ rfl).trans (mul_eq_one_of rfl (res_eq_one _ rfl)).symm
theorem charUnit_zero (S : Scheme.{0}) (M : Type) [AddCommGroup M] : charUnit S M 0 = 1 := by
  unfold charUnit
  refine res_pullU_eq_one _ _ ?_
  rw [ofAdd_zero, map_one, map_one, map_one]
  rfl
def SecConst {L : LB Y} (s : LB.Sec L) (a : Γ(Y, ⊤)) : Prop := ∀ j, s.f j = resTop (L.U j) a
def cs (φ : J → (Y ⟶ X)) (ε : J → ℤ) (a : Γ(Y, ⊤)) : LB.Sec (LB.LinComb (trivLB X) φ ε) where
  f := fun _ => resTop _ a
  compat := fun i j => by
    rw [linComb_triv_g, Units.val_one, _root_.one_mul, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res]
theorem cs_const (φ : J → (Y ⟶ X)) (ε : J → ℤ) (a : Γ(Y, ⊤)) : SecConst (cs φ ε a) a := fun _ => rfl
theorem app_resTop (f : Y' ⟶ Y) (V : Y.Opens) (a : Γ(Y, ⊤)) :
    (f.app V).hom (resTop V a) = resTop (f ⁻¹ᵁ V) (f.appTop.hom a) := app_res' f a V
theorem secRel_of {φ₁ : J → (Y' ⟶ X)} {ε₁ : J → ℤ} {s₁ : LB.Sec (LB.LinComb (trivLB X) φ₁ ε₁)}
    {φ₂ : J' → (Y ⟶ X)} {ε₂ : J' → ℤ} {s₂ : LB.Sec (LB.LinComb (trivLB X) φ₂ ε₂)} {a : Γ(Y', ⊤)}
    {b : Γ(Y, ⊤)} (ha : SecConst s₁ a) (hb : SecConst s₂ b) (h : Y' ⟶ Y)
    {φ₃ : J'' → (Y' ⟶ X)} {ε₃ : J'' → ℤ} {u : LB.Gen (LB.LinComb (trivLB X) φ₃ ε₃)}
    (hu : IsConst u 1) (H : a = h.appTop.hom b) :
    GeneratorPullback.SecRel (trivLB X) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u := by
  intro j₁ j₂ j₃ _
  erw [ha, hb, hu, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, H]
  erw [gv_one, Units.val_one, map_one, _root_.mul_one]
variable {A B : Type} [CommRing A] [CommRing B]
end Const
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
def zeroData : DegData R I where
  toPre := toricPre R PUnit (fun _ => 1)
  psi_even := psiEven _ fun _ => rfl
  tau_bimult := tauBimult _ fun _ _ _ => by simp [polar]
  psi_pos := fun _ h => (h rfl).elim
  psi_tendsto := fun _ => @Set.toFinite _ _ (@Subtype.finite _ (inferInstanceAs (Finite PUnit)) _)
def isTerminalPullback {S S' : Scheme.{0}} (f : S' ⟶ S) :
    IsTerminal ((Over.pullback f).obj (𝟙_ (Over S))) :=
  IsTerminal.isTerminalObj _ _ isTerminalTensorUnit
def zeroGt (e : ℕ) : GtCoord I (zeroData R I).toPre e (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  q := 𝟙 _
  q_hom := (inferInstance : IsMonHom (𝟙 (thickObj R I e (𝟙_ _))))
  q_flat := (inferInstance : Flat (𝟙 (thickObj R I e (𝟙_ _)).left))
  q_surj := (inferInstance : Surjective (𝟙 (thickObj R I e (𝟙_ _)).left))
  q_affine := (inferInstance : IsAffineHom (𝟙 (thickObj R I e (𝟙_ _)).left))
  i := toUnit _ ≫ η
  i_hom := inferInstance
  isKernel := by
    have : IsIso (toUnit (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (zeroData R I).toPre.X)) :=
      isIso_toUnit_splitTorus_punit _
    exact @IsPullback.of_vert_isIso _ _ _ _ _ _ _ _ _ _ this
      (inferInstance : IsIso (𝟙 (thickObj R I e (𝟙_ _)))) ⟨Category.comp_id _⟩
  t := fun _ => cg _ _ 1
  t_gen := fun _ => cg_isGen _ _ 1
  t_mul := fun _ _ => corr_of_isConst
    ((isConst_mulGen (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))))
    (isConst_mulGen (cg_isConst _ _ 1) (cg_isConst _ _ 1))
  t_unit := fun _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
    (isConst_oneGen _)
  t_weight := fun χ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
    ((isConst_mulGen (a := 1) (fun j => by
        obtain rfl : χ = 0 := rfl
        exact (res_pullU_eq_one _ _ (charUnit_zero _ _)).trans (gv_one _).symm)
      ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))
theorem zeroGt_pG (e : ℕ) :
    (zeroGt R I e).pG.left = pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) :=
  Category.id_comp _
def zeroPre : UnifPre I (zeroData R I) (zeroPolAV (Spec (CommRingCat.of (FractionRing R))))
    (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  smooth := (inferInstance : Smooth (𝟙 (Spec (CommRingCat.of R))))
  separated := (inferInstance : IsSeparated (𝟙 (Spec (CommRingCat.of R))))
  gen := (isTerminalPullback (jK R)).uniqueUpToIso isTerminalTensorUnit
  gen_hom := ⟨toUnit_unique _ _, toUnit_unique _ _⟩
  LG := ⟨trivLB _, (zeroData R I).toPre.rig, trivLB_isLB _, (zeroData R I).toPre.rig_gen⟩
  cubG := (zeroData R I).toPre.cub
  symG := (zeroData R I).toPre.sym
  symG_gen := (zeroData R I).toPre.sym_gen
  symG_rig := (zeroData R I).toPre.sym_rig
  ext := ⟨_, one_isGen_div _ _ _ _⟩
  gt := zeroGt R I
  gt_q := fun e => by
    rw [zeroGt_pG, zeroGt_pG]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  gt_t := fun _ _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
    (cg_isConst _ _ 1)
  w := fun _ => ⟨fun _ => 1⟩
  w_gen := fun _ => one_isGen_div _ _ _ _
  w_rig := fun e p V h₁ h₂ h₃ =>
    (mul_eq_one_of (res_pullU_eq_one _ h₁ rfl) (res_pullU_eq_one _ h₂ (gv_one _))).trans
      (res_pullU_eq_one _ h₃ (gv_one _)).symm
  w_even := fun e jS jT _ _ V h₁ h₂ h₃ h₄ =>
    (mul_eq_one_of (res_pullU_eq_one _ h₁ (gv_one _)) (res_eq_one h₂ rfl)).trans
      (mul_eq_one_of (res_pullU_eq_one _ h₃ rfl) (res_pullU_eq_one _ h₄ (gv_one _))).symm
  w_cub := fun e T x jL jM _ _ V hB hG hw =>
    (res_pullU_eq_one _ hB (gv_one _)).trans
      (mul_eq_one_of (Finset.prod_eq_one fun k _ =>
        (congrArg (· ^ thε k) (res_pullU_eq_one _ (hw k) rfl)).trans (one_zpow _))
        (res_pullU_eq_one _ hG (gv_one _))).symm
  w_compat := fun e p V h₁ h₂ => (res_pullU_eq_one _ h₁ rfl).trans (res_eq_one h₂ rfl).symm
variable {R I}
abbrev pGK : pullback (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (jK R) ⟶
    Spec (CommRingCat.of (FractionRing R)) := pullback.snd _ _
abbrev pBK : (DegPre.BF (zeroData R I).toPre (FractionRing R)).left ⟶
    Spec (CommRingCat.of (FractionRing R)) := (fst (TF (R := R) (FractionRing R)) _).left
instance : IsIso (pGK (R := R)) := (inferInstance : IsIso (pullback.snd (𝟙 _) (jK R)))
instance : IsIso (pBK (R := R) (I := I)) :=
  (inferInstance : IsIso (pullback.fst (TF (R := R) (FractionRing R)).hom (𝟙 _)))
def constFam (k : ℕ) (c : Γ((DegPre.BF (zeroData R I).toPre (FractionRing R)).left, ⊤)) :
    Fam (zeroData R I).toPre (FractionRing R) k where
  s := fun _ => cs _ _ c
  fe := fun mu α u _ hu => by
    have hz : IsIso (DegPre.zF (zeroData R I).toPre (FractionRing R)).left := by
      have : (DegPre.zF (zeroData R I).toPre (FractionRing R)).left ≫ pBK = 𝟙 _ :=
        congrArg Over.Hom.left (lift_fst (𝟙 (TF (R := R) (FractionRing R)))
          (toUnit _ ≫ η[(zeroData R I).toPre.P.A]))
      exact IsIso.of_isIso_fac_right this
    have ht : DegPre.trF (zeroData R I).toPre (FractionRing R) mu = 𝟙 _ :=
      CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm)
        (toUnit_unique _ _)
    have hm : IsConst (DegPre.famMult (zeroData R I).toPre (FractionRing R) k mu α) 1 :=
      (isConst_pullGen (isConst_mulGen (isConst_mulGen (isConst_powGen (psi_isConst _ mu) k)
        (tau_isConst _ mu α)) (isConst_powGen (rigK_isConst _) k)) _).of_eq (by
          simp only [polar, inv_one, _root_.mul_one, unitOn_one, one_pow, map_one])
    obtain ⟨v, hv⟩ := exists_isConst u
    have hv1 : v = 1 := pullTop_injective (DegPre.zF (zeroData R I).toPre (FractionRing R)).left
      ((eq_of_corr (isConst_pullGen hv _) hm hu).trans (map_one _).symm)
    refine secRel_of (cs_const _ _ _) (cs_const _ _ _) _ (hv.of_eq hv1) ?_
    rw [ht, Over.id_left, Scheme.Hom.id_appTop]
    rfl
end GlobalTheory.UnifZero


