-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_AlgebraicIndependentFreeVar
-- name    : Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_AlgebraicIndependentFreeVar
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:21:15.125731+00:00
-- url     : https://prove2.me/theorems/1bda388f-9289-47bd-8357-2c8389d097c0
-- title:
--   Algebraic Independent Free Var
-- statement:
--   Definitions and structural lemmas for Algebraic Independent Free Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/AlgebraicIndependentFreeVar.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
open MvPolynomial
namespace SectionPoint
def freeVarIndex {D N : ℕ} (j₀ : Fin (N + 1)) : SVar D N → TVar D N :=
  Sum.elim (fun _ => ((0 : Fin (D + 1)), j₀)) (fun ik => (ik.1, j₀.succAbove ik.2))
end SectionPoint
end GlobalTheory


