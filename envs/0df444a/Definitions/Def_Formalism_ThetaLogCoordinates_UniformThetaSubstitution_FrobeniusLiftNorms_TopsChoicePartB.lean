-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:54.90251+00:00
-- url     : https://prove2.me/theorems/a50f1806-4f7c-450c-baa0-fbbc161db759
-- title:
--   Tops Choice Part B
-- statement:
--   Definitions and structural lemmas for Tops Choice Part B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartB.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low WtGe MonoWtGe dot dot_const substitution_weight_bound)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
def clSum {K ι : Type} [Field K] (pp : K) (hh : MvPowerSeries ι K) (U : ℕ → MvPowerSeries ι K)
    (M : ℕ) : MvPowerSeries ι K :=
  ∑ i ∈ range M, MvPowerSeries.C ((pp ^ i)⁻¹) * (hh ^ i * U i)
def chT {K ι : Type} [Field K] (Y : MvPowerSeries ι K) (U : ℕ → MvPowerSeries ι K) (b a : ℕ) :
    MvPowerSeries ι K :=
  MvPowerSeries.C (((b + a).choose b : ℕ) : K) * ((-Y) ^ a * U (b + a))
def chU {K ι : Type} [Field K] (Y : MvPowerSeries ι K) (U : ℕ → MvPowerSeries ι K) (b : ℕ) :
    MvPowerSeries ι K :=
  fun n => ∑ a ∈ range (n.degree + 1), MvPowerSeries.coeff n (chT Y U b a)
def expSum {K ι : Type} [Field K] (f : MvPowerSeries ι K) (M : ℕ) : MvPowerSeries ι K :=
  ∑ k ∈ range M, MvPowerSeries.C ((k.factorial : K)⁻¹) * f ^ k
def leadT (K : Type) [Field K] (p : ℕ) (x y : Fin 2) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C ((p : K)⁻¹) * (MvPowerSeries.X x * MvPowerSeries.X y ^ p)
def G1 {K : Type} [Field K] (p : ℕ) (c c' : K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C c * (AA K p 0 1 - leadT K p 0 1) -
    MvPowerSeries.C c' * (AA K p 1 0 - leadT K p 1 0)
end Formalism.InvariantFactorPaths.G7


