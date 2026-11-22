-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:23.426651+00:00
-- url     : https://prove2.me/theorems/ad274367-2790-4e9e-b150-7865e4b520bb
-- title:
--   Growth Of Basic
-- statement:
--   Definitions and structural lemmas for Growth Of Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
section Num1
open Formalism.FourierDecayAlt.PB Finset
end Num1
section Num2
open Formalism.FourierDecayAlt.PB Finset
end Num2
section Num3
open Formalism.FourierDecayAlt.PB Finset
end Num3
section Num4
open Formalism.FourierDecayAlt.PB
end Num4
section Hil1
open Formalism.FourierDecayAlt.PB Finset
end Hil1
section Hil2
open Formalism.FourierDecayAlt.PB Finset
section
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁)
end
end Hil2
section Hil3
open Formalism.FourierDecayAlt.PB Finset
end Hil3
section Hil4
open Formalism.FourierDecayAlt.PB Finset
open Classical
open scoped ComplexOrder
end Hil4
section Hil5
open Formalism.FourierDecayAlt.PB Finset
open Classical
section
variable {τ H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
noncomputable def reInner (w : H₁) : H₁ →+ ℝ :=
  AddMonoidHom.mk' (fun x => (inner ℂ w x).re) (by intro a b; simp)
end
end Hil5
section Hil6
open Formalism.FourierDecayAlt.PB
end Hil6
section LocA
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
variable {E : Type} [Field E]
end LocA
section LocB
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
variable {E : Type} [Field E]
end LocB
section Loc
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
end Loc
section Lat
open NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
end Lat
section Main
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
end Main
section Loops
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset
end Loops
section From
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset NumberField
end From
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


