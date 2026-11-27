-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:43:21.541936+00:00
-- url     : https://prove2.me/theorems/c161dffd-3089-4c85-8b17-9112243e56cc
-- title:
--   Int SOf Mul Eq One
-- statement:
--   Definitions and structural lemmas for Int SOf Mul Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntSOfMulEqOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CocycleIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_GlobalTheory_GaugeCocycle_intS_iff_ig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.GaugeCocycle ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
namespace GlobalTheory.RowVal
open MvPowerSeries
variable {C : Type} [Field C]
theorem mvExp_eq_subst [CharZero C] {σ : Type} {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    mvExp F = PowerSeries.subst F (PowerSeries.exp C) := by
  classical
  ext m
  have hS : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show (∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hk'
    apply hk
    have h1 : m.degree < k := by simpa using hk'
    have h0 : coeff m (F ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hF)
      exact_mod_cast h1
    rw [h0, smul_zero]
theorem mvExp_add [CharZero C] {σ : Type} {F G : MvPowerSeries σ C} (hF : constantCoeff F = 0)
    (hG : constantCoeff G = 0) : mvExp (F + G) = mvExp F * mvExp G := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst hG, mvExp_eq_subst (by rw [map_add, hF, hG, add_zero]),
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hF hG]
theorem mvExp_zero' [CharZero C] {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  rw [mvExp_eq_subst (map_zero _), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
theorem intS_one {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (one_mem _)
theorem intS_mul {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) :=
  (intS_iff_ig V _).2 (mul_mem ((intS_iff_ig V _).1 hF) ((intS_iff_ig V _).1 hG))
theorem intS_of_mul_eq_one {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F)
    (h1 : constantCoeff F = 1) (hFG : F * G = 1) : IntS V G := by
  obtain ⟨U, hU⟩ := RingHom.mem_range.1 ((intS_iff_ig V _).1 hF)
  have hU1 : constantCoeff U = 1 := by
    apply Subtype.ext
    have e := congrArg constantCoeff hU
    rw [constantCoeff_map, h1] at e
    exact e
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 := MvPowerSeries.mul_invOfUnit U 1 (by simp [hU1])
  have e : G = MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1) := by
    have h2 := congrArg (MvPowerSeries.map (σ := σ) (algebraMap (valRing V) C)) hinv
    rw [map_mul, map_one, hU] at h2
    calc G = G * (F * MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1)) := by
          rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm G F, hFG, one_mul]
  rw [e]
  exact (intS_iff_ig V _).2 (ig_map _)
def logInt [CharZero C] (V : VF C) (σ : Type) : AddSubgroup (MvPowerSeries σ C) where
  carrier := {F | constantCoeff F = 0 ∧ IntS V (mvExp F)}
  zero_mem' := ⟨map_zero _, by rw [mvExp_zero']; exact intS_one⟩
  add_mem' := fun {F G} hF hG => ⟨by rw [map_add, hF.1, hG.1, add_zero], by
    rw [mvExp_add hF.1 hG.1]; exact intS_mul hF.2 hG.2⟩
  neg_mem' := fun {F} hF => ⟨by rw [map_neg, hF.1, neg_zero], by
    refine intS_of_mul_eq_one hF.2 ?_ ?_
    · rw [mvExp_eq_subst hF.1, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp hF.1]
    · rw [← mvExp_add hF.1 (by rw [map_neg, hF.1, neg_zero]), add_neg_cancel, mvExp_zero']⟩
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
def IntEnd (X : RawChart C d I κ) (V : VF C) (A : Matrix κ κ C) : Prop :=
  ∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)
def hEnd (X : RawChart C d I κ) (A B : Matrix κ κ C) : MvPowerSeries κ C :=
  hAt X (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C)) (endP X B (MvPowerSeries.X : κ → MvPowerSeries κ C))
end GlobalTheory.RowVal


