-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_IsIsoPullbackHom
-- name    : Development_AbelianVarietyTheory_Statements_SemistableTorsion_IsIsoPullbackHom
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:04.185794+00:00
-- url     : https://prove2.me/theorems/6c4fc06b-b059-5f0b-82a2-84deeba1b51d
-- title:
--   Is Iso Pullback Hom
-- statement:
--   Definitions and structural lemmas for Is Iso Pullback Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/SemistableTorsion/IsIsoPullbackHom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_GlobalTheory_UnifZero_appTop_scal
import Theorems.Thm_GlobalTheory_UnifZero_app_mul_unit
import Theorems.Thm_GlobalTheory_UnifZero_exists_secConst
import Theorems.Thm_GlobalTheory_UnifZero_expBij
import Theorems.Thm_GlobalTheory_UnifZero_expandsAt_iff
import Theorems.Thm_GlobalTheory_UnifZero_expands_iff
import Theorems.Thm_GlobalTheory_UnifZero_resTop_inj
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_GlobalTheory_UnifZero_scal_mul
import Theorems.Thm_GlobalTheory_UnifZero_scal_specMap
import Theorems.Thm_GlobalTheory_UnifZero_secScal_iff
import Theorems.Thm_GlobalTheory_UnifZero_sec_eq_of_secConst
import Theorems.Thm_GlobalTheory_UnifZero_unit_pow_mul_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
namespace GlobalTheory.ZH.GenusZero
open GlobalTheory.ToricData GlobalTheory.UnifZero
def isTerminalOfIsIso {S : Scheme.{0}} (G : Over S) [IsIso G.hom] : IsTerminal G :=
  IsTerminal.ofIso Over.mkIdTerminal (Over.isoMk (asIso G.hom) (by simp) : G ≅ Over.mk (𝟙 S)).symm
instance isIso_pullback_hom {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [IsIso G.hom] :
    IsIso ((Over.pullback f).obj G).hom := (inferInstance : IsIso (pullback.snd G.hom f))
instance isIso_unit_hom (S : Scheme.{0}) : IsIso (𝟙_ (Over S)).hom := (inferInstance : IsIso (𝟙 S))
theorem hom_unique {S : Scheme.{0}} {T G : Over S} [IsIso G.hom] (f g : T ⟶ G) : f = g :=
  (isTerminalOfIsIso G).hom_ext f g
theorem isMonHom_of_isIso {S : Scheme.{0}} {T G : Over S} [MonObj T] [MonObj G] [IsIso G.hom] (f : T ⟶ G) :
    IsMonHom f := ⟨hom_unique _ _, hom_unique _ _⟩
theorem isIso_left {S : Scheme.{0}} {T G : Over S} [IsIso T.hom] [IsIso G.hom] (f : T ⟶ G) : IsIso f.left :=
  IsIso.of_isIso_fac_right (Over.w f)
def trivRig {S : Scheme.{0}} (G : Over S) [GrpObj G] : RigLB G := ⟨trivLB _, cg _ _ 1, trivLB_isLB _, cg_isGen _ _ 1⟩
def trivCub {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubicalStr G (trivRig G) where
  t := cg _ _ 1
  isGen := cg_isGen _ _ 1
  face := fun _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)
  cubeSymmetric_swap_first := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
  cubeSymmetric_swap_last := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
  cocycle := corr_of_isConst
    ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))
    ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  [IsCommMonObj G] [IsIso G.hom]
instance (e : ℕ) : IsIso (thickObj R I e G).hom := isIso_pullback_hom _ _
instance (e : ℕ) : IsIso (thickObj R I e (zeroData R I).toPre.P.A).hom := isIso_pullback_hom _ (𝟙_ _)
instance : IsIso (zeroData R I).toPre.P.A.hom := isIso_unit_hom _
def trivGt (e : ℕ) : GtCoord I (zeroData R I).toPre e G where
  q := (isTerminalOfIsIso _).from _
  q_hom := isMonHom_of_isIso _
  q_flat := by have := isIso_left ((isTerminalOfIsIso (thickObj R I e (zeroData R I).toPre.P.A)).from (thickObj R I e G)); infer_instance
  q_surj := by have := isIso_left ((isTerminalOfIsIso (thickObj R I e (zeroData R I).toPre.P.A)).from (thickObj R I e G)); infer_instance
  q_affine := by have := isIso_left ((isTerminalOfIsIso (thickObj R I e (zeroData R I).toPre.P.A)).from (thickObj R I e G)); infer_instance
  i := toUnit _ ≫ η
  i_hom := inferInstance
  isKernel := by
    have h1 : IsIso (toUnit (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (zeroData R I).toPre.X)) :=
      isIso_toUnit_splitTorus_punit _
    have h2 : IsIso ((isTerminalOfIsIso (thickObj R I e (zeroData R I).toPre.P.A)).from (thickObj R I e G)) :=
      isIso_of_isTerminal (isTerminalOfIsIso _) (isTerminalOfIsIso _) _
    exact @IsPullback.of_vert_isIso _ _ _ _ _ _ _ _ _ _ h1 h2 ⟨hom_unique _ _⟩
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
theorem trivGt_pG (e : ℕ) : (trivGt R I G e).pG.left = pullback.fst G.hom (thick R I e) ≫ G.hom :=
  ((Category.comp_id _).symm.trans (Over.w (trivGt R I G e).pG)).trans pullback.condition.symm
def trivPre : UnifPre I (zeroData R I) (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))) G where
  smooth := inferInstance
  separated := inferInstance
  gen := (isTerminalOfIsIso _).uniqueUpToIso isTerminalTensorUnit
  gen_hom := ⟨toUnit_unique _ _, toUnit_unique _ _⟩
  LG := trivRig G
  cubG := trivCub G
  symG := cg _ _ 1
  symG_gen := cg_isGen _ _ 1
  symG_rig := corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)
  ext := ⟨_, one_isGen_div _ _ _ _⟩
  gt := trivGt R I G
  gt_q := fun e => by
    rw [trivGt_pG, trivGt_pG]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ G.hom) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))
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
variable {R I G}
theorem expandsAt_iff (e k : ℕ)
    {σ : LB.Sec (LB.LinComb (trivPre R I G).LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))}
    {f : ∀ α : (zeroData R I).toPre.X, (zeroData R I).toPre.SecB k α} {a b : R}
    (ha : SecConst σ (scal G.hom a)) (hb : SecConst (f PUnit.unit) (scal (𝟙 _) b)) :
    (trivPre R I G).ExpandsAt e k σ f ↔ a - b ∈ I ^ (e + 1) := by
  let p := pullback.fst G.hom (thick R I e) ≫ G.hom
  let q := pullback.snd G.hom (thick R I e)
  have hp : ∀ x : R, scal p x = scal q (Ideal.Quotient.mk _ x) := fun x => by
    rw [← scal_specMap]
    exact congrArg (scal · x) pullback.condition
  have hG : ∀ x : R, (fstG I e G).left.appTop.hom (scal G.hom x) = scal p x := fun x => appTop_scal _ _ _
  have hB : ∀ x : R, ((trivPre R I G).gt e).pG.left.appTop.hom (scal (𝟙 _) x) = scal p x := fun x =>
    (appTop_scal _ _ _).trans (congrArg (scal · x) ((Category.comp_id _).trans (trivGt_pG R I G e)))
  rw [← Ideal.Quotient.eq, ← (scal_bijective q).1.eq_iff, ← hp, ← hp]
  have hpre : ∀ {Y Y' : Scheme.{0}} (g : Y' ⟶ Y) {U : Y.Opens}, U = ⊤ → ⊤ ≤ g ⁻¹ᵁ U := by
    rintro _ _ g _ rfl
    exact le_rfl
  have key : ∀ S p' j₁ jf jt, (trivPre R I G).expW e p' j₁ S jf jt = ⊤ := fun S p' j₁ jf jt =>
    top_unique (le_inf (le_inf (le_inf (wchart_triv _ _).ge (wchart_triv _ _).ge)
      (hpre _ (wchart_triv _ _))) (Finset.le_inf fun α _ =>
        le_inf (hpre _ (wchart_triv _ _)) (wchart_triv _ _).ge))
  constructor
  · rintro ⟨S, h0, h⟩
    have h1 := h (fun _ => PUnit.unit, fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ => PUnit.unit)
      (fun _ _ => PUnit.unit) rfl (fun _ _ _ => @Subsingleton.elim PUnit _ _ _)
    have h2 := ((unit_pow_mul_app _ _ _ rfl (ha _) k).symm.trans h1).trans
      (Finset.sum_congr rfl fun α _ => app_mul_unit _ _ _ (gv_one _) (hb _))
    rw [hG, hB, Finset.sum_const, Finset.card_attach] at h2
    by_cases hS : PUnit.unit ∈ S
    · obtain rfl : S = {PUnit.unit} := Finset.eq_singleton_iff_unique_mem.2 ⟨hS, fun _ _ => rfl⟩
      exact resTop_inj (key _ _ _ _ _) (h2.trans (one_nsmul _))
    · obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun _ => hS
      rw [Finset.card_empty, zero_smul] at h2
      have h3 := ((app_resTop _ _ _).symm.trans
        (congrArg _ (hb (fun _ => PUnit.unit)).symm)).trans (h0 PUnit.unit hS _)
      rw [hB] at h3
      exact (resTop_inj (key _ _ _ _ _) (h2.trans (map_zero _).symm)).trans
        (resTop_inj (top_unique (hpre _ (wchart_triv _ _))) (h3.trans (map_zero _).symm)).symm
  · intro H
    refine ⟨{PUnit.unit}, fun α hα => (hα (Finset.mem_singleton_self _)).elim, ?_⟩
    intro p' j₁ jf jt _ _
    refine (unit_pow_mul_app _ _ _ rfl (ha _) k).trans
      (Eq.trans ?_ (Finset.sum_congr rfl fun α _ => app_mul_unit _ _ _ (gv_one _) (hb _)).symm)
    rw [hG, hB, Finset.sum_const, Finset.card_attach, H]
    exact (one_nsmul _).symm
theorem expands_iff [IsHausdorff I R] (k : ℕ) {s : (trivPre R I G).SecK k}
    {F : Fam (zeroData R I).toPre (FractionRing R) k} {x y : FractionRing R}
    (hs : SecConst s (scal (pullback.snd G.hom (jK R)) x)) (hF : SecConst (F.s PUnit.unit) (scal pBK y)) :
    (trivPre R I G).Expands k s F ↔ x = y := by
  have e1 : ∀ a r : R, (pullback.fst G.hom (jK R)).appTop.hom (scal G.hom a) =
      scal (pullback.snd G.hom (jK R) ≫ jK R) r * scal (pullback.snd G.hom (jK R)) x ↔
        algebraMap R _ a = algebraMap R _ r * x := fun a r => by
    rw [← (scal_bijective (pullback.snd G.hom (jK R))).1.eq_iff, scal_mul, ← scal_specMap, ← scal_specMap]
    exact Eq.congr_left ((appTop_scal _ _ _).trans (congrArg (scal · a) pullback.condition))
  have hB : ∀ a : R, scal (DegPre.BF (zeroData R I).toPre (FractionRing R)).hom a =
      scal pBK (algebraMap R (FractionRing R) a) := fun a => by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) _)]
    exact (congrArg (scal · a) (Category.assoc _ _ _).symm).trans
      ((scal_specMap _ _ _).trans (scal_specMap _ _ _))
  have e2 : ∀ a r : R, (DegPre.prB (zeroData R I).toPre (FractionRing R)).left.appTop.hom (scal (𝟙 _) a) =
      scal (DegPre.BF (zeroData R I).toPre (FractionRing R)).hom r * scal pBK y ↔
      algebraMap R _ a = algebraMap R _ r * y := fun a r => by
    rw [← (scal_bijective (pBK (I := I))).1.eq_iff, scal_mul, ← hB, ← hB]
    exact Eq.congr_left ((appTop_scal _ _ _).trans (congrArg (scal · a)
      (Over.w (DegPre.prB (zeroData R I).toPre (FractionRing R)))))
  constructor
  · rintro ⟨r, hr, σ, f, h1, h2, h3⟩
    obtain ⟨a', ha⟩ := exists_secConst σ
    obtain ⟨a, rfl⟩ := (scal_bijective G.hom).2 a'
    obtain ⟨b', hb⟩ := exists_secConst (f PUnit.unit)
    obtain ⟨b, rfl⟩ := (scal_bijective (𝟙 (Spec (CommRingCat.of R)))).2 b'
    have hab : a = b := by
      rw [← sub_eq_zero]
      refine IsHausdorff.haus' (I := I) _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) ((expandsAt_iff n k ha hb).1 (h3 n))
    have hx := (e1 a r).1 ((secScal_iff hs ha _ _).1 h1)
    have hy := (e2 b r).1 ((secScal_iff hF hb _ _).1 (h2 PUnit.unit))
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
      (hx.symm.trans (hab ▸ hy))
  · rintro rfl
    obtain ⟨⟨a, r⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
    have h' : algebraMap R (FractionRing R) a = algebraMap R _ r * x := h.symm.trans (mul_comm _ _)
    exact ⟨r, nonZeroDivisors.ne_zero r.2, cs _ _ (scal G.hom a), fun _ => cs _ _ (scal (𝟙 _) a),
      (secScal_iff hs (cs_const _ _ _) _ _).2 ((e1 a r).2 h'),
      fun _ => (secScal_iff hF (cs_const _ _ _) _ _).2 ((e2 a r).2 h'),
      fun e => (expandsAt_iff e k (cs_const _ _ _) (cs_const _ _ _)).2 (by rw [sub_self]; exact zero_mem _)⟩
theorem expBij [IsHausdorff I R] (k : ℕ) : (trivPre R I G).ExpBij k := by
  have hS : ∀ s : (trivPre R I G).SecK k, ∃ x, SecConst s (scal (pullback.snd G.hom (jK R)) x) := fun s => by
    obtain ⟨a, ha⟩ := exists_secConst s
    obtain ⟨x, rfl⟩ := (scal_bijective (pullback.snd G.hom (jK R))).2 a
    exact ⟨x, ha⟩
  have hF : ∀ F : Fam (zeroData R I).toPre (FractionRing R) k,
      ∃ y, SecConst (F.s PUnit.unit) (scal pBK y) := fun F => by
    obtain ⟨a, ha⟩ := exists_secConst (F.s PUnit.unit)
    obtain ⟨y, rfl⟩ := (scal_bijective (pBK (R := R) (I := I))).2 a
    exact ⟨y, ha⟩
  constructor
  · intro s
    obtain ⟨x, hx⟩ := hS s
    refine ⟨constFam k (scal pBK x), (expands_iff k hx (cs_const _ _ _)).2 rfl, fun F h => ?_⟩
    obtain ⟨y, hy⟩ := hF F
    obtain rfl := (expands_iff k hx hy).1 h
    exact DVR.fam_ext fun _ j => hy j
  · intro F
    obtain ⟨y, hy⟩ := hF F
    refine ⟨cs _ _ (scal (pullback.snd G.hom (jK R)) y), (expands_iff k (cs_const _ _ _) hy).2 rfl, fun s h => ?_⟩
    obtain ⟨x, hx⟩ := hS s
    obtain rfl := (expands_iff k hx hy).1 h
    exact sec_eq_of_secConst hx (cs_const _ _ _)
variable (R I G) in

def trivUnif [IsHausdorff I R] : Unif I (zeroData R I) (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))) G :=
  ⟨trivPre R I G, fun k _ => expBij k⟩
end GlobalTheory.ZH.GenusZero
end


