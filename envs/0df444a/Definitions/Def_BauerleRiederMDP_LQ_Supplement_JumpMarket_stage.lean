-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_stage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:14:47.646079+00:00
-- url     : https://prove2.me/theorems/08d592b4-fb21-5ec5-8e52-5fc7feefcefe
-- title:
--   The discrete-time model of the terminal wealth problem
-- statement:
--   **The discrete-time model of the terminal wealth problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.282, PDF 292): the model `relaxedStage` restricted to the action space `A = {α : [0, T] → U measurable}` of (9.12), whose elements enter as one-point relaxed controls; its maximal reward operator is (9.15).
--
--   **Formalization Note.** $A$ is the published `ControlFn (Ufrac d)` (read on $[0, T]$).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, p.282, PDF 292

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_relaxedStage

open BauerleRiederMDP.PDMDP (ControlFn StageModel)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The discrete-time model of the terminal wealth problem** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §9.3, p.282, PDF 292): the model `relaxedStage`
restricted to the action space `A = {α : [0, T] → U measurable}` of (9.12), whose elements enter as
one-point relaxed controls; its maximal reward operator is (9.15).

**Formalization Note.** `A` is the published `ControlFn (Ufrac d)` (read on `[0, T]`). -/
noncomputable def JumpMarket.stage {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ) :
    StageModel (ℝ × ℝ) (ControlFn (Ufrac d)) where
  rew p α := (Mk.relaxedStage U).rew p α.toRelaxed
  kern p α := (Mk.relaxedStage U).kern p α.toRelaxed

end BauerleRiederMDP.LQ.Supplement


