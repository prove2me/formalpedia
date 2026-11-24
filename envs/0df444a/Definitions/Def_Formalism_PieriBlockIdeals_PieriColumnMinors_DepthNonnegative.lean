-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:45.607204+00:00
-- url     : https://prove2.me/theorems/59cd646e-20c7-4cf5-b179-6c5c9850b7d5
-- title:
--   Depth Nonnegative
-- statement:
--   Definitions and structural lemmas for Depth Nonnegative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
namespace Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
section SizeData₂
open Formalism.RankGapBounds.ChebyshevFactorialBounds
end SizeData₂
section Subquotients
open CategoryTheory CategoryTheory.Limits
def mulOntoScaledSubmodule {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : V →ₗ[A] scaleSub A V c where
  toFun v := ⟨c • v, v, rfl⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' b x := Subtype.ext (smul_comm c b x)
end Subquotients
end Formalism.CohomologicalDescent.DepthNonnegative


