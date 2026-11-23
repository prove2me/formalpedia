-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:47.836049+00:00
-- url     : https://prove2.me/theorems/b3c730c9-6bbb-4f25-b39a-f700a4b25fa3
-- title:
--   Local Component GL
-- statement:
--   Definitions and structural lemmas for Local Component GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
namespace DworkIntegrality
section Bd
variable {K ι : Type} [NormedField K] [IsUltrametricDist K]
def Bd (c : ℝ) (f : MvPowerSeries ι K) : Prop := ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ c
end Bd
section Trunc
variable {K ι : Type} [Field K] [Finite ι]
def truncD (d : ℕ) (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  ∑ m ∈ (Finsupp.finite_of_degree_lt (σ := ι) d).toFinset,
    MvPowerSeries.monomial m (MvPowerSeries.coeff m f)
end Trunc
section Induct
variable {K ι : Type} [NormedField K] [Finite ι]
variable [IsUltrametricDist K]
end Induct
section Frob
variable {K ι : Type} [Field K]
def PhiH {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) : MvPowerSeries ι K →+* MvPowerSeries ι K :=
  ((MvPowerSeries.expand p hp : MvPowerSeries ι K →ₐ[K] MvPowerSeries ι K) :
    MvPowerSeries ι K →+* MvPowerSeries ι K).comp (MvPowerSeries.map σ)
end Frob
section Congr
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
end Congr
section ExpS
variable {K ι : Type} [NormedField K] [CharZero K]
variable [IsUltrametricDist K] {p : ℕ}
end ExpS
section Mult
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [Finite ι] {p : ℕ} {σ : K →+* K}
end Mult
section Rel
variable {K ι : Type} [NormedField K] [CharZero K]
end Rel
end DworkIntegrality
end Formalism.InvariantFactorPaths.G7


