-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_BddOfMemHolSub
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_BddOfMemHolSub
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:25.568616+00:00
-- url     : https://prove2.me/theorems/c4c92eb2-305e-46da-abac-dc0136aa6611
-- title:
--   Bdd Of Mem Hol Sub
-- statement:
--   Definitions and structural lemmas for Bdd Of Mem Hol Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Theorems.Thm_Formalism_L2_Pj_evalAt_mul
import Theorems.Thm_Formalism_L2_Pj_evalAt_one
import Theorems.Thm_Formalism_L2_Pj_evalAt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
noncomputable section
namespace GlobalTheory
namespace IntegralCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
def evHom {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ))
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    Rul Xo c →+* ℂ where
  toFun f := Formalism.L2.PjFree.toC (evR Xo c f y)
  map_one' := evalAt_one _ _ y hy
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y
end IntegralCusp
end GlobalTheory


