-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:35.767842+00:00
-- url     : https://prove2.me/theorems/8d4ab92d-f93d-44a1-96fa-230b9108bbe6
-- title:
--   Theorem SFrom KOne Of
-- statement:
--   Definitions and structural lemmas for Theorem SFrom KOne Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
namespace TwoS
section Cong
variable {K ι : Type} [NormedField K] [IsUltrametricDist K]
def Cg (p : ℕ) (f g : MvPowerSeries ι K) : Prop :=
  ∀ n, ‖MvPowerSeries.coeff n (f - g)‖ ≤ (p : ℝ)⁻¹
end Cong
section Alt
variable {K : Type} [Field K]
variable {ν r0 r1 : ℕ}
def linW [NeZero ν] (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (w s) * MvPowerSeries.X (s, ab)
def posW [NeZero ν] (p : ℕ) (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (w s) * sPos p s ab
end Alt
section AltN
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
end AltN
section Par
variable {ν : ℕ}
variable {K : Type}
def wE [Zero K] (u : ZMod (2 * ν) → K) (k : ℕ) (s : ZMod (2 * ν)) : K :=
  if s.val % 2 = k then u s else 0
def wE' [Zero K] (u : ZMod (2 * ν) → K) (k : ℕ) (s : ZMod (2 * ν)) : K :=
  if s.val % 2 = k then u (s + 1) else 0
variable [NormedField K] [IsUltrametricDist K]
variable {r0 r1 : ℕ}
def posW' [NeZero ν] (p : ℕ) (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (w s) * sPos p s ab ^ p
end Par
section Sub
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ} [NeZero ν]
end Sub
end TwoS
open TwoS
namespace TwoS
end TwoS
end Formalism.InvariantFactorPaths.G7


