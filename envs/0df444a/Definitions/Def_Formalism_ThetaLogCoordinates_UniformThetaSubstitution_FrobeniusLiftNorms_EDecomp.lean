-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:51.805709+00:00
-- url     : https://prove2.me/theorems/058287d3-0721-4a33-ba0d-f643972ec43d
-- title:
--   EDecomp
-- statement:
--   Definitions and structural lemmas for EDecomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EDecomp.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_of_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_symm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_sPos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral low_subst_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_mul low_pow low_one_iff low_mul_sub
  low_of_zero)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow cg_frob_add cg_frob_sum
  integral_add integral_neg integral_sum integral_C integral_X integral_zero coeff_sPos pinv_nonneg)
namespace EDec
section LowGe
variable {K Tp Lw : Type} [Field K] [Fintype Lw]
def LowGe (m : ℕ) (f : MvPowerSeries (Tp ⊕ Lw) K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → m ≤ lowDeg n
end LowGe
section Cong
variable {K ι : Type} [NormedField K] [IsUltrametricDist K]
end Cong
section Trunc
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
def sT (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ l ∈ range E, MvPowerSeries.C ((-1 : K) ^ l) *
    MvPowerSeries.X (s - 2 * (l : ZMod (2 * ν)), ab) ^ ((p ^ 2) ^ l)
def hhT [NeZero ν] (p E : ℕ) (u : ZMod (2 * ν) → K) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) *
    ∑ ab : Fin r0 × Fin r1, sT p E s ab ^ p * sT p E (s + 1) ab
end Trunc
section Sub
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
def tpS (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (x : ZV ν r0 r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  if x.1 ∈ TT then MvPowerSeries.C (ξ x.1 x.2.1) * MvPowerSeries.X (Sum.inl (x.1, x.2.2)) else 0
def zlS (x : ZV ν r0 r1) : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K := MvPowerSeries.X (Sum.inr x)
def Zs1 (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * zlS (s - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l))
def Ts1 (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ) (s : ZMod (2 * ν))
    (ab : Fin r0 × Fin r1) : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * tpS TT ξ (s - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l))
def Zs2 (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * zlS (s + 1 - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (2 * l))
def Ts2 (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ) (s : ZMod (2 * ν))
    (ab : Fin r0 × Fin r1) : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * tpS TT ξ (s + 1 - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (2 * l))
def Zs2' (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, if l = 0 then 0
    else (-1) ^ l * zlS (s + 1 - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (2 * l))
end Sub
section Terms
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
end Terms
section Rest
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
end Rest
end EDec
end Formalism.InvariantFactorPaths.G7


