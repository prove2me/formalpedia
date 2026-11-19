-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_StoppedProcess_F000
-- name    : BrownianMotion_Auxiliary_StoppedProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:06:37.305337+00:00
-- url     : https://prove2.me/theorems/ce6acd8b-374c-4ae0-91c5-fae20c65360f
-- title:
--   Source declarations: BrownianMotion.Auxiliary.StoppedProcess
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.StoppedProcess, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Process.Stopping


@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Nonempty ι]

namespace stoppedValue

@[simp] lemma add [Add E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u + v) τ = stoppedValue u τ + stoppedValue v τ := rfl
@[simp] lemma neg [Neg E] {u : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl
@[simp] lemma sub [Sub E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u - v) τ = stoppedValue u τ - stoppedValue v τ := rfl
end stoppedValue

end MeasureTheory


