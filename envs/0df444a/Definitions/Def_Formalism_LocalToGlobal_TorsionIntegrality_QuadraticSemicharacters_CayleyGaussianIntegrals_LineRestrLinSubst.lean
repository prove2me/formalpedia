-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:15.4008+00:00
-- url     : https://prove2.me/theorems/62b5b289-6ad4-416f-830d-eb3795da3c7f
-- title:
--   Line Restr Lin Subst
-- statement:
--   Definitions and structural lemmas for Line Restr Lin Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LineRestrLinSubst.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Theorems.Thm_Formalism_L2_Th1_F_taylorDeriv
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
namespace TMv
open Formalism.L2.Th1.F (taylor0 taylorRing taylorDeriv)
section Formal
variable {K : Type*} [CommRing K] {n : Type*} [Finite n]
theorem hasSubst_line (v : n → K) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    change PowerSeries.constantCoeff (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K) = 0
    simp
def lineHom (v : n → K) : MvPowerSeries n K →+* PowerSeries K :=
  (MvPowerSeries.substAlgHom (R := K) (hasSubst_line v)).toRingHom
end Formal
section Analytic
variable {n : Type} [Fintype n]
end Analytic
end TMv
open TMv Formalism.L2.Th1.F
end Formalism.L2.Th1.H


