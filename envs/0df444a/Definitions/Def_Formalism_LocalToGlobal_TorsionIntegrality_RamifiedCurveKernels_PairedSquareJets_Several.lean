-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:02:09.316896+00:00
-- url     : https://prove2.me/theorems/c531839a-7160-4b16-b7c2-b7c8554f43f9
-- title:
--   Several
-- statement:
--   Definitions and structural lemmas for Several, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Several.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst

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
namespace Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
section Hom
variable {K : Type} [Field K]
theorem cc_linForm {m : Type} [Fintype m] (v : m → K) :
    MvPowerSeries.constantCoeff (∑ x, MvPowerSeries.C (v x) * MvPowerSeries.X x :
      MvPowerSeries m K) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
theorem hasSubst_lin {n m : Type} [Finite n] [Fintype m] (A : n → m → K) :
    MvPowerSeries.HasSubst
      (fun i => (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x : MvPowerSeries m K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_linForm (A i)
def linSubHom {n m : Type} [Finite n] [Fintype m] (A : n → m → K) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries m K :=
  MvPowerSeries.substAlgHom (hasSubst_lin A)
theorem cc_zPt {n : Type} {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) linv h0
theorem hasSubst_zPt {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries.HasSubst (fun i : n =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_zPt h0 i
def toZHom {n : Type} [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries n K :=
  MvPowerSeries.substAlgHom (hasSubst_zPt h0)
end Hom
end Formalism.L2.Th1.G


