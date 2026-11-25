-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:20.063433+00:00
-- url     : https://prove2.me/theorems/89403ff0-4b36-4fe8-9b82-8c323a34bd2b
-- title:
--   Multiplication Biadditive Holds
-- statement:
--   Definitions and structural lemmas for Multiplication Biadditive Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/MultiplicationBiadditiveHolds.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_add
import Theorems.Thm_Formalism_L2_Th1_B_integral_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_invExists
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_subst_zero
import Theorems.Thm_Formalism_L2_Th1_B_simeqInt
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B.Mul
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')
section Grp
variable {A : Type} [AddCommGroup A]
end Grp
section Quot
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}
def lam (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] :
    AddSubgroup (MvPowerSeries ι K) where
  carrier := {h | Simeq h 0}
  zero_mem' := (equivalence_rules K ι).1 0
  add_mem' := fun {a b} ha hb => by
    have e := (equivalence_rules K ι).2.2.2.1 a 0 b 0 ha hb
    rwa [add_zero] at e
  neg_mem' := fun {a} ha => by
    have e := (simeqInt K ι a 0 a 0 ha ha).2.1
    rwa [neg_zero] at e
def cl (f : MvPowerSeries ι K) : MvPowerSeries ι K ⧸ lam K ι := QuotientAddGroup.mk' (lam K ι) f
end Quot
section Law
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
def IsMul (l : PowerSeries K) (n : ℤ) (N : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff N = 0 ∧ Integral (ι := Unit) N ∧
    PowerSeries.subst N l = PowerSeries.C (n : K) * l
theorem subst_X_self (f : PowerSeries K) : PowerSeries.subst (PowerSeries.X : PowerSeries K) f = f :=
  PowerSeries.X_subst f
theorem isMul_zero {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0) : IsMul l 0 0 := by
  refine ⟨map_zero _, law_integral_zero, ?_⟩
  rw [law_subst_zero l hl]
  simp
theorem isMul_one (l : PowerSeries K) : IsMul l 1 PowerSeries.X := by
  refine ⟨PowerSeries.constantCoeff_X, law_integral_X (), ?_⟩
  rw [subst_X_self]
  simp
theorem isMul_neg_one {l i : PowerSeries K} (hi : IsInv l i) : IsMul l (-1) i := by
  refine ⟨hi.1, hi.2.1, ?_⟩
  rw [hi.2.2]
  simp
theorem isMul_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) {n m : ℤ}
    {N M : PowerSeries K} (hN : IsMul l n N) (hM : IsMul l m M) :
    IsMul l (n + m) (MvPowerSeries.subst ![N, M] F) := by
  refine ⟨constantCoeff_subst_two_variables F h.1 N M hN.1 hM.1, integral_subst_two_variables h.2.1 N M hN.1 hM.1 hN.2.1 hM.2.1, ?_⟩
  rw [cube_log_add h N M hN.1 hM.1, hN.2.2, hM.2.2]
  push_cast
  rw [map_add]
  ring
theorem isMul_exists {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n : ℤ) :
    ∃ N, IsMul l n N := by
  obtain ⟨i, hi⟩ := invExists K F l h
  induction n using Int.induction_on with
  | zero => exact ⟨0, isMul_zero h.2.2.1⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨_, isMul_add h hN (isMul_one l)⟩
  | pred k ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨_, isMul_add h hN (isMul_neg_one hi)⟩
def mulN {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n : ℤ) :
    PowerSeries K := (isMul_exists h n).choose
end Law
section Two
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}
end Two
end Formalism.L2.Th1.B.Mul


