-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Majority
-- name    : WatsonPseudodeterminism_MASeparation_Majority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:18.364228+00:00
-- url     : https://prove2.me/theorems/69e6ab75-168a-4338-a1dc-74be7344a178
-- title:
--   Sequential majority trees and independent repetition
-- statement:
--   Given a list of deterministic trees, execute them in sequence. Each reached leaf chooses the continuation using its fixed public output label. After the final tree, output one exactly when strictly more than half the recorded labels are one. Ties output zero. Final output never reads either private input.
--
--   For a randomized protocol $D$, form a list of $2d$ independent samples from $D$ using the PMF product law, then map the list to its sequential majority tree:
--
--   $$D'_d=\operatorname{Law}\bigl(\operatorname{Maj}(P_1,\ldots,P_{2d})\bigr),\qquad P_i\overset{\mathrm{iid}}\sim D.$$
--
--   The law is an actual distribution of communication trees. Its depth bound and error estimates are separate theorem conclusions, so the definition assumes neither amplification nor correctness. This construction also specifies the dependence and tie conventions needed to interpret the paper's preprocessing step.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §4, p. 11 (majority vote of 2d independent runs); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Protocol

namespace WatsonPseudodeterminism.MASeparation

/-- Replace each leaf by a continuation selected only by its publicly known label. -/
def Protocol.bind {X Y : Type} (P : Protocol X Y) (next : Bool → Protocol X Y) :
    Protocol X Y :=
  match P with
  | .leaf b => next b
  | .alice bit p q => .alice bit (p.bind next) (q.bind next)
  | .bob bit p q => .bob bit (p.bind next) (q.bind next)

/-- Run every tree in sequence, remembering its leaf label, then take strict majority.
Ties output false. No evaluation on the private inputs occurs at the final leaf. -/
def majorityProtocol {X Y : Type} (ps : List (Protocol X Y)) (answers : List Bool := []) :
    Protocol X Y :=
  match ps with
  | [] => .leaf (decide (answers.length < 2 * (answers.filter (fun b => b)).length))
  | p :: rest => p.bind (fun b => majorityProtocol rest (b :: answers))

/-- A list of independent samples from D, in order. -/
noncomputable def independentRuns {X Y : Type} (D : RandomProtocol X Y) :
    ℕ → PMF (List (Protocol X Y))
  | 0 => PMF.pure []
  | r + 1 => D.bind (fun p => (independentRuns D r).map (fun ps => p :: ps))

/-- §4, p. 11: the actual law of the majority of 2d independent runs. -/
noncomputable def majorityLaw {X Y : Type} (D : RandomProtocol X Y) (d : ℕ) :
    RandomProtocol X Y :=
  (independentRuns D (2 * d)).map (fun ps => majorityProtocol ps)

end WatsonPseudodeterminism.MASeparation


