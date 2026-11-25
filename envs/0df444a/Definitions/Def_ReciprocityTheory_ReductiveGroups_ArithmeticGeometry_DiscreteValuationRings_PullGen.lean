-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:52:26.279234+00:00
-- url     : https://prove2.me/theorems/54932bd2-6f0d-5599-9648-3a7281b7fd2f
-- title:
--   Pull Gen
-- statement:
--   Definitions and structural lemmas for Pull Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_add__7f610987c414
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_single__0fef72d07d07
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_sub__7ba063a12c3d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_of_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_mulGen_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_one_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_normalized
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_sumElim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_of_local_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_pullMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_rosati
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
abbrev cPB (χ : D.toPre.X) : DegPre.BF D.toPre F ⟶ D.toPre.P.A := toUnit _ ≫ D.toPre.c χ
lemma aF_prB (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := by
  unfold aF
  exact lift_snd _ _
lemma aF_cP (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) : aF D F oa a ≫ cPB D F χ = cPB D F χ := by
  unfold cPB
  rw [← Category.assoc, toUnit_unique (aF D F oa a ≫ toUnit _) (toUnit _)]
lemma aF_one (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ (toUnit _ ≫ η[D.toPre.P.A]) = toUnit _ ≫ η[D.toPre.P.A] := by
  rw [← Category.assoc, toUnit_unique (aF D F oa a ≫ toUnit _) (toUnit _)]
def pullSum (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    (DegPre.BF D.toPre F ⟶ D.toPre.P.A) →₀ ℤ :=
  ((((k * N : ℕ) : ℤ) - 1) • Finsupp.single (DegPre.prB D.toPre F) 1 +
      (1 : ℤ) • Finsupp.single (DegPre.prB D.toPre F * cPB D F (star a • χ)) 1 +
      (-1 : ℤ) • Finsupp.single (cPB D F (star a • χ)) 1 + (1 : ℤ) • Finsupp.single 1 1) +
    ((-((k : ℤ) - 1)) • Finsupp.single (DegPre.prB D.toPre F ≫ oa.onB.act a) 1 +
      (-1 : ℤ) • Finsupp.single ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ) 1 +
      (1 : ℤ) • Finsupp.single (cPB D F χ) 1 + (-1 : ℤ) • Finsupp.single 1 1)
lemma fsum_pull (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    fsum (pullφ D F oa a χ) (pullε k N) = lf (pullSum D F oa a k N χ) := by
  have h1 : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F ≫ oa.onB.act a).left := by
    rw [← Over.comp_left, aF_prB]
  have h2 : (aF D F oa a).left ≫
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ)).left =
      ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ).left := by
    rw [← Over.comp_left]
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, aF_prB, aF_cP]
    rfl
  have h3 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ).left = (cPB D F χ).left := by
    rw [← Over.comp_left, aF_cP]
  have h4 : (aF D F oa a).left ≫ (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left (aF_one D F oa a)
  have h5 : (padd D.toPre.P.A (DegPre.prB D.toPre F)
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ))).left =
      (DegPre.prB D.toPre F * cPB D F (star a • χ)).left := rfl
  have h6 : (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := rfl
  have h7 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left = (cPB D F (star a • χ)).left := rfl
  simp only [fsum, lf, pullφ, pullε, DegPre.famφ, DegPre.famε, pullSum, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
    h1, h2, h3, h4, h5, h6, h7, neg_neg, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    Finsupp.mapDomain_single, Finsupp.smul_single_one]
  clear h1 h2 h3 h4 h5 h6 h7
  congr 1
  · simp only [add_assoc]
  · simp only [add_assoc]
lemma mapDomain_zsmul' {α β : Type} (f : α → β) (n : ℤ) (F' : α →₀ ℤ) :
    Finsupp.mapDomain f (n • F') = n • Finsupp.mapDomain f F' := by
  rw [Finsupp.mapDomain_smul]
theorem hasGen_pull (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (k : ℕ) (χ : D.toPre.X) :
    HasGen D.toPre.P.L (lf (pullSum D F oa a k N χ)) := by
  have hA := oa.onB.rosati a
  have hA' := oa.onB.rosati (star a)
  rw [star_star] at hA'
  obtain ⟨uR, huR⟩ := gen_of_local_base hL (Out.rosatiφ D.toPre.P.A (oa.onB.act a) (oa.onB.act (star a))) Out.rosatiε hA
  obtain ⟨uR', huR'⟩ :=
    gen_of_local_base hL (Out.rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε hA'
  have hPM := hasGen_pullMul oa.onB.toRingAct w0 a N hN uΨ huΨ uR huR D.toPre.cub.t D.toPre.cub.isGen
  have h1 := hPM.pull (DegPre.prB D.toPre F).left
  rw [lf_pull] at h1
  have h2 := hasGen_rosati (oa.onB.act (star a)) (oa.onB.act a) uR' huR' (cPB D F χ) (DegPre.prB D.toPre F)
  have h3 : HasGen D.toPre.P.L (lf (Finsupp.single (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A) 1)) := by
    have := HasGen.of_gen (LB.pullGen D.toPre.P.L _ _ D.toPre.rig (toUnit (DegPre.BF D.toPre F)).left)
      (pullGen_isGen_of_isGen _ _ D.toPre.rig D.toPre.rig_gen _)
    convert this using 1
    simp only [fsum, Fintype.univ_punit, Finset.sum_singleton, lf_single]
    rfl
  have h := (h1.zsmul (-(k : ℤ))).add (h2.add (h3.zsmul ((k : ℤ) * ((N : ℤ) - 1))))
  simp only [← lf_smul, ← lf_add] at h
  convert h using 2
  have hc : cPB D F χ ≫ oa.onB.act (star a) = cPB D F (star a • χ) := by
    simp only [cPB, Category.assoc, oa.c_lin]
  simp only [pullSum, mapDomain_add', mapDomain_sub', mapDomain_zsmul', mapDomain_single', Category.comp_id,
    MonObj.comp_one, lamP, hc]
  rw [mul_comm (cPB D F (star a • χ)), mul_comm (cPB D F χ)]
  push_cast
  module
lemma zF_prB : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := by
  unfold DegPre.zF
  exact lift_snd _ _
lemma zF_prB_mul (x : DegPre.BF D.toPre F ⟶ D.toPre.P.A) :
    DegPre.zF D.toPre F ≫ (DegPre.prB D.toPre F * x) = DegPre.zF D.toPre F ≫ x := by
  show DegPre.zF D.toPre F ≫ (lift (DegPre.prB D.toPre F) x ≫ μ[D.toPre.P.A]) = _
  rw [← Category.assoc, comp_lift, zF_prB]
  exact one_mul _
lemma zF_prB_mul' (oa : D.toPre.OAct O) (a : O) (x : DegPre.BF D.toPre F ⟶ D.toPre.P.A) :
    DegPre.zF D.toPre F ≫ ((DegPre.prB D.toPre F ≫ oa.onB.act a) * x) = DegPre.zF D.toPre F ≫ x := by
  haveI := oa.onB.hom a
  show DegPre.zF D.toPre F ≫ (lift (DegPre.prB D.toPre F ≫ oa.onB.act a) x ≫ μ[D.toPre.P.A]) = _
  rw [← Category.assoc, comp_lift, ← Category.assoc, zF_prB]
  rw [show (1 : TF (R := V) F ⟶ D.toPre.P.A) ≫ oa.onB.act a = 1 from ?_]
  · exact one_mul _
  · show (toUnit _ ≫ η[D.toPre.P.A]) ≫ oa.onB.act a = toUnit _ ≫ η[D.toPre.P.A]
    rw [Category.assoc, IsMonHom.one_hom]
lemma zF_cP (χ : D.toPre.X) : DegPre.zF D.toPre F ≫ cPB D F χ = toUnit _ ≫ D.toPre.c χ := by
  unfold cPB
  rw [← Category.assoc, toUnit_unique (DegPre.zF D.toPre F ≫ toUnit _) (toUnit _)]
lemma zF_fst : DegPre.zF D.toPre F ≫ fst (TF (R := V) F) D.toPre.P.A = 𝟙 _ := by
  unfold DegPre.zF
  exact lift_fst _ _
lemma one_left_TF : (1 : TF (R := V) F ⟶ D.toPre.P.A).left =
    jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A := by
  unfold eSec
  show (toUnit (TF (R := V) F) ≫ η[D.toPre.P.A]).left = _
  rw [Over.comp_left, ← Category.assoc]
  rfl
lemma fsum_pull_zF (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN1 : 1 ≤ N) (χ : D.toPre.X) :
    fsum (fun i => (DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) (pullε k N) =
      ((k * (N - 1) : ℕ) : ℤ) • Finsupp.single (1 : TF (R := V) F ⟶ D.toPre.P.A).left 1 := by
  haveI := oa.onB.hom a
  have h1 : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F ≫ oa.onB.act a).left := by
    rw [← Over.comp_left, aF_prB]
  have h2 : (aF D F oa a).left ≫
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ)).left =
      ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ).left := by
    rw [← Over.comp_left]
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, aF_prB, aF_cP]
    rfl
  have h3 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ).left = (cPB D F χ).left := by
    rw [← Over.comp_left, aF_cP]
  have h4 : (aF D F oa a).left ≫ (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left (aF_one D F oa a)
  have h5 : (padd D.toPre.P.A (DegPre.prB D.toPre F)
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ))).left =
      (DegPre.prB D.toPre F * cPB D F (star a • χ)).left := rfl
  have h6 : (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := rfl
  have h7 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left = (cPB D F (star a • χ)).left := rfl
  have g1 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left =
      (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, zF_prB]
  have g2 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F * cPB D F (star a • χ)).left =
      (toUnit (TF (R := V) F) ≫ D.toPre.c (star a • χ)).left := by
    rw [← Over.comp_left, zF_prB_mul, zF_cP]
  have g3 : ∀ y, (DegPre.zF D.toPre F).left ≫ (cPB D F y).left =
      (toUnit (TF (R := V) F) ≫ D.toPre.c y).left := by
    intro y
    rw [← Over.comp_left, zF_cP]
  have g4 : (DegPre.zF D.toPre F).left ≫ (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left =
      (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left]
    congr 1
    show DegPre.zF D.toPre F ≫ (toUnit _ ≫ η[D.toPre.P.A]) = toUnit _ ≫ η[D.toPre.P.A]
    rw [← Category.assoc, toUnit_unique (DegPre.zF D.toPre F ≫ toUnit _) (toUnit _)]
  have g5 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F ≫ oa.onB.act a).left =
      (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, zF_prB]
    congr 1
    show (toUnit _ ≫ η[D.toPre.P.A]) ≫ oa.onB.act a = toUnit _ ≫ η[D.toPre.P.A]
    rw [Category.assoc, IsMonHom.one_hom]
  have g6 : (DegPre.zF D.toPre F).left ≫ ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ).left =
      (toUnit (TF (R := V) F) ≫ D.toPre.c χ).left := by
    rw [← Over.comp_left, zF_prB_mul', zF_cP]
  simp only [fsum, pullφ, pullε, DegPre.famφ, DegPre.famε, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
    h1, h2, h3, h4, h5, h6, h7, neg_neg, g1, g2, g3, g4, g5, g6]
  clear h1 h2 h3 h4 h5 h6 h7 g1 g2 g3 g4 g5 g6
  ext y
  classical
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs <;> (try push_cast [Nat.cast_sub hN1]) <;> ring
theorem exists_pullGen (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ) (χ : D.toPre.X) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) := by
  set n := k * (N - 1)

  set r := LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK n) (jFK (R := V) F)
  have hrig : (D.toPre.rigK).IsGen := pullGen_isGen_of_isGen _ _ D.toPre.rig D.toPre.rig_gen _
  have hr : r.IsGen := pullGen_isGen_of_isGen _ _ _ (powGen_isGen_of_isGen _ hrig n) _
  set p := (fst (TF (R := V) F) D.toPre.P.A).left
  set z := (DegPre.zF D.toPre F).left
  have hzp : z ≫ p = 𝟙 _ := by
    simp only [z, p]
    rw [← Over.comp_left, zF_fst]
    rfl
  set rT := LB.pullGen D.toPre.P.L _ _ r p
  have hrT : rT.IsGen := pullGen_isGen_of_isGen _ _ r hr p

  obtain ⟨u0, hu0⟩ := (hasGen_pull D F hL oa w0 uΨ huΨ a N hN k χ).gen hL _ _ (fsum_pull D F oa a k N χ)
  set v := LB.mulGen D.toPre.P.L _ _ _ _ u0 (LB.invGen D.toPre.P.L _ _ rT)
  have hv : v.IsGen := mulGen_isGen_of_isGen _ hu0 _ (invGen_isGen_of_isGen _ hrT)

  have hφr : fsum (fun _ : PUnit => jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A)
      (fun _ : PUnit => (n : ℤ) * 1) = (n : ℤ) • Finsupp.single (1 : TF (R := V) F ⟶ D.toPre.P.A).left 1 := by
    rw [one_left_TF]
    simp [fsum, Finsupp.smul_single_one]
  have h0 : fsum (fun i => z ≫ Sum.elim (pullφ D F oa a χ)
        (fun _ : PUnit => p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A) i)
      (Sum.elim (pullε k N) (fun _ : PUnit => -((n : ℤ) * 1))) = 0 := by
    rw [fsum_comp, fsum_sumElim, mapDomain_add', ← fsum_comp, fsum_pull_zF D F oa a k N hN1 χ, ← fsum_comp]
    have e : (fun _ : PUnit => z ≫ p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A) =
        fun _ => jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A := by
      funext _
      rw [← Category.assoc, hzp, Category.id_comp]
    rw [e, fsum_neg, hφr, add_neg_cancel]
  obtain ⟨v', hv', hv1⟩ := exists_normalized hL _ _ v hv p z hzp h0
  have hW := mulGen_isGen_of_isGen _ hv' _ hrT
  have hsW : LB.SameSum
      (Sum.elim (Sum.elim (pullφ D F oa a χ)
        (fun _ : PUnit => p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A))
        (fun _ : PUnit => p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A))
      (Sum.elim (Sum.elim (pullε k N) (fun _ : PUnit => -((n : ℤ) * 1))) (fun _ : PUnit => (n : ℤ) * 1))
      (pullφ D F oa a χ) (pullε k N) := by
    rw [sameSum_iff_fsum, fsum_sumElim, fsum_sumElim, fsum_neg]
    abel
  obtain ⟨u, hu, hcW⟩ := gen_transport hL hsW _ hW
  refine ⟨u, hu, ?_⟩
  have c1 := corr_pullGen (corr_symm hcW) z
  have c2 := corr_pullGen_mulGen v' rT z
  have c4 := corr_trans hL (corr_pullGen_comp r p z)
    (corr_trans hL (corr_pullGen_of_eq r hr _ _ hzp) (corr_pullGen_id r))
  have c3 := corr_mulGen (corr_one_of (fun j hj => hv1 j hj)) c4
  have c5 := corr_mulGen_one r
  exact corr_trans hL c1 (corr_trans hL c2 (corr_trans hL c3 c5))
section PullFam
variable (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
  (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
  (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
def uPull (χ : D.toPre.X) : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)) :=
  Classical.choose (exists_pullGen D F hL oa w0 uΨ huΨ a N hN hN1 k χ)
lemma uPull_spec (χ : D.toPre.X) :
    (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ).IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ)
        (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) := Classical.choose_spec (exists_pullGen D F hL oa w0 uΨ huΨ a N hN hN1 k χ)
def pullProd (s : Fam D.toPre F k) (χ : D.toPre.X) :=
  mulSec D.toPre.P.L _ _ _ _ (genSec (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ) (uPull_spec D F hL oa w0 uΨ huΨ a N hN hN1 k χ).1)
    (pullSec D.toPre.P.L _ _ (s.s χ) (aF D F oa a).left)
lemma pullProd_sameSum (χ : D.toPre.X) (β : D.toPre.X) (hβ : star a • χ = β) :
    LB.SameSum (Sum.elim (pullφ D F oa a χ) (fun i => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i))
      (Sum.elim (pullε k N) (DegPre.famε k)) (DegPre.famφ D.toPre F β) (DegPre.famε (k * N)) := by
  subst hβ
  intro ψ
  classical
  have hz : ∀ x : Fin 4, ((if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then -DegPre.famε k x else 0) +
      if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then DegPre.famε k x else 0) = 0 := by
    intro x
    split_ifs <;> simp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc, ← Finset.sum_add_distrib]
  show (∑ x : Fin 4, if DegPre.famφ D.toPre F (star a • χ) x = ψ then DegPre.famε (k * N) x else 0) +
      ∑ x : Fin 4, ((if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then -DegPre.famε k x else 0) +
        if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then DegPre.famε k x else 0) =
      ∑ x : Fin 4, if DegPre.famφ D.toPre F (star a • χ) x = ψ then DegPre.famε (k * N) x else 0
  rw [Finset.sum_eq_zero (fun x _ => hz x), add_zero]
open scoped Classical in

def pullSecs (s : Fam D.toPre F k) (β : D.toPre.X) :
    LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F β) (DegPre.famε (k * N))) :=
  if h : ∃ χ, star a • χ = β then
    Classical.choose (sec_transport hL (pullProd_sameSum D F oa a N k h.choose β h.choose_spec)
      (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s h.choose))
  else SecOps.secZero
end PullFam
end ReciprocityTheory.ChartRestriction.G.DVR


