-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:38.813522+00:00
-- url     : https://prove2.me/theorems/1fb52d9b-549c-47b9-b00c-235aa0aa58c7
-- title:
--   PSemiloc Rank Frac
-- statement:
--   Definitions and structural lemmas for PSemiloc Rank Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace SemilocRankFrac
section Scale
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
end Scale
section Eval
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
  (x' : (Σ k, ι' k) → Ω) (P' : Ideal (MRing ι')) [P'.IsPrime]
  (h : RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) = P')
def quotEval : MRing ι' ⧸ P' →+* Ω :=
  Ideal.Quotient.lift P' (aeval x' : MRing ι' →ₐ[ℤ] Ω).toRingHom fun f hf => by
    rw [← h] at hf
    exact RingHom.mem_ker.1 hf
theorem quotEval_injective : Function.Injective (quotEval x' P' h) :=
  (Ideal.injective_lift_iff _).2 h
def fracEval : FractionRing (MRing ι' ⧸ P') →+* Ω :=
  IsFractionRing.lift (quotEval_injective x' P' h)
end Eval
end SemilocRankFrac
end GroundTheory.Heights₂.Heights.Inter


