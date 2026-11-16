-- Prove2me | Definitions.Def_BatchMaxService_Metric_Supplement_Automatic
-- name    : BatchMaxService_Metric_Supplement_Automatic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:59:20.728922+00:00
-- url     : https://prove2.me/theorems/f0abc4ed-b320-4800-b619-7355e091dd2a
-- title:
--   Automatic service and its unrestricted offline value
-- statement:
--   Let $I$ be a finite family of distinct request identities with nonnegative real arrival times in a known finite metric, and let $\sigma$ be a finite schedule of instantaneous walks from its prescribed start. An automatic event serves exactly the pending identities at its listed vertices, including during a repositioning walk. Every complete epoch at the parked server is served in one batch before movement. These requirements refine the published elective feasibility predicate without imposing consecutive arrival blocks.
--
--   $$\operatorname{OPT}_{\rm auto}(I)=\inf_{\sigma\text{ automatically feasible}}\operatorname{cost}_I(\sigma).$$
--
--   Infima take values in the extended nonnegative reals; the empty feasible family has infimum $+\infty$. The published movement and per-event maximum-delay objective are reused. This supplies the comparator for the automatic companion theorems.
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Section 2, Definition 2.2, printed p. 4 / PDF p. 5; Section 3.2, printed p. 6 / PDF p. 7

import Mathlib
import Definitions.Def_BatchMaxService_Metric_RequestInput

namespace BatchMaxService.Metric.Supplement

variable {n : ℕ}

inductive Rule where
  | elective | automatic
  deriving DecidableEq

/-- Literal visited-vertex hits, including on pure repositioning walks. -/
noncomputable def hits (I : RequestInput n) (pending : Finset ℕ)
    (w : List (Fin n)) : Finset ℕ := by
  classical
  exact pending.filter fun q => I.location q ∈ w

/-- Automatic batches, and immediate parked service before any further movement.
    No consecutive-block condition is imposed. `served` contains earlier events only. -/
noncomputable def autoSteps (I : RequestInput n) : Fin n → Finset ℕ → Schedule n → Prop
  | _, _, [] => True
  | s, served, e :: rest =>
      (let pending := I.ids.filter fun q => q ∉ served ∧ I.arrival q ≤ e.time
       e.batch = hits I pending e.walk) ∧
      (∀ q ∈ I.ids, q ∉ served → I.location q = s → I.arrival q < e.time → False) ∧
      ((∃ q ∈ I.ids, q ∉ served ∧ I.location q = s ∧ I.arrival q = e.time) →
        ∀ v ∈ e.walk, v = s) ∧
      autoSteps I (e.walk.getLast?.getD s) (served ∪ e.batch) rest

noncomputable def AutomaticFeasible (I : RequestInput n) (σ : Schedule n) : Prop :=
  Feasible I σ ∧ autoSteps I I.start ∅ σ

noncomputable def RuleFeasible (r : Rule) (I : RequestInput n) (σ : Schedule n) : Prop :=
  match r with
  | .elective => Feasible I σ
  | .automatic => AutomaticFeasible I σ

noncomputable def OPTauto [MetricSpace (Fin n)] (I : RequestInput n) : ENNReal :=
  ⨅ σ : {σ : Schedule n // AutomaticFeasible I σ}, ENNReal.ofReal (cost I σ.val)

noncomputable def ruleOPT [MetricSpace (Fin n)] (r : Rule) (I : RequestInput n) : ENNReal :=
  match r with
  | .elective => OPT I
  | .automatic => OPTauto I

end BatchMaxService.Metric.Supplement


