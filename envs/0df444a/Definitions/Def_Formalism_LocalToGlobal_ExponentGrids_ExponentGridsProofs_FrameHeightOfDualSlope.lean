-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
-- name    : Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:32.608262+00:00
-- url     : https://prove2.me/theorems/d8f499cd-25ba-4dec-89b5-939467d60e22
-- title:
--   Frame Height Of Dual Slope
-- statement:
--   Definitions and structural lemmas for Frame Height Of Dual Slope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ExponentGridsProofs/FrameHeightOfDualSlope.lean

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Lemmata_PlaneOverMembership_PlOverOfMem
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_valuation_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
namespace Formalism.AtG
open Classical in

def fR {K : Type} [Field K] [NumberField K] (w : Pl K) (a : K) : WithTop ℝ :=
  if a = 0 then ⊤ else (((vw w a : ℤ) : ℝ) : WithTop ℝ)
theorem fR_ne {K : Type} [Field K] [NumberField K] (w : Pl K) (a : K) (ha : a ≠ 0) :
    fR w a = (((vw w a : ℤ) : ℝ) : WithTop ℝ) := by
  unfold fR
  exact if_neg ha
theorem fR_zero {K : Type} [Field K] [NumberField K] (w : Pl K) : fR w (0 : K) = ⊤ := by
  unfold fR
  exact if_pos rfl
def valR {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) : AddValuation K (WithTop ℝ) :=
  AddValuation.of (fR w) (fR_zero w)
    (by rw [fR_ne w 1 one_ne_zero, Formalism.DivisionValues.ValuationRepresentative.vw_one]; simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · rw [hxy]; simp [fR]
      rw [fR_ne w x hx, fR_ne w y hy, fR_ne w _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
      have h := Formalism.PairingDivisionLocalBalance.valuation_add K w x y hx hy hxy
      rcases min_le_iff.mp h with h | h
      · exact le_trans (min_le_left _ _) (by exact_mod_cast h)
      · exact le_trans (min_le_right _ _) (by exact_mod_cast h))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp [fR]
      by_cases hy : y = 0
      · subst hy; simp [fR]
      rw [fR_ne w x hx, fR_ne w y hy, fR_ne w _ (mul_ne_zero hx hy), Formalism.DivisionValues.ValuationRepresentative.vw_mul w x y hx hy,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring)
end Formalism.AtG


