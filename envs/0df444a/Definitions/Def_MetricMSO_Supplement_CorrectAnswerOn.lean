-- Prove2me | Definitions.Def_MetricMSO_Supplement_CorrectAnswerOn
-- name    : MetricMSO_Supplement_CorrectAnswerOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:54:26.954278+00:00
-- url     : https://prove2.me/theorems/32828fa6-513b-471d-bd6b-e40710634806
-- title:
--   Correct answers of the six tasks for an arbitrary solution set
-- statement:
--   For a set $\mathcal S$ of assignments of the free set variables and weights $w_i$, this definition fixes the correct outputs of the six tasks, with the conventions of the published `MetricMSO.CorrectAnswer` (Definitions 2.6 and 2.7):
--
--   1. decide: whether $\mathcal S\ne\emptyset$;
--   2. minimize (maximize): "none" if $\mathcal S=\emptyset$, otherwise the optimum of $w(S_1,\dots,S_r)=\sum_i\sum_{a\in S_i}w_i(a)$ in signed binary together with an assignment attaining it;
--   3. count: $|\mathcal S|$ in binary;
--   4. count minimum (maximum): the number of optimum assignments in binary, $0$ when $\mathcal S=\emptyset$.
--
--   It is used for the satisfying assignments of packing-covering templates, one-cover formulas and nearest-label formulas (Theorems 1.7, 1.9, 1.10).
--
--   **Formalization Note** On the solution set of a published formula this relation coincides with the published `CorrectAnswer` (checked in the sanity file).
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Definitions 2.6, 2.7, p.17 (PDF 19); p.30 (PDF 32)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MetricMSO_CorrectAnswer

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO
open ExponomialAssortment.FPTAS (encodeNat encodeInt)

/-- The minimum-weight elements of a set of assignments. -/
def MinOf {I : Instance} {rV rE : ℕ} (Sols : Set (Assignment I rV rE)) (w : Weights I rV rE) :
    Set (Assignment I rV rE) :=
  {A | A ∈ Sols ∧ ∀ B ∈ Sols, weight w A ≤ weight w B}

/-- The maximum-weight elements of a set of assignments. -/
def MaxOf {I : Instance} {rV rE : ℕ} (Sols : Set (Assignment I rV rE)) (w : Weights I rV rE) :
    Set (Assignment I rV rE) :=
  {A | A ∈ Sols ∧ ∀ B ∈ Sols, weight w B ≤ weight w A}

open Classical in
/-- **Correct answers of the six tasks for an arbitrary solution set** `Sols` (the satisfying
assignments of a packing-covering template, a one-cover formula or a nearest-label formula), with
exactly the conventions of the published `MetricMSO.CorrectAnswer` (Definitions 2.6, 2.7, p.17
(PDF 19)):
* `decide`: `[true]` if a satisfying assignment exists, `[false]` otherwise;
* `minimize` (`maximize`): `[false]` if there is none; otherwise `true`, the signed binary code of
  the optimum value and the code of an assignment attaining it;
* `count`: the number of satisfying assignments in binary;
* `countMin` (`countMax`): the number of minimum-weight (maximum-weight) satisfying assignments
  in binary, `0` when there is no satisfying assignment.

**Formalization Note** `CorrectAnswerOn task (Sol I φ rV rE) w = CorrectAnswer task I φ rV rE w`
(checked in the sanity file). -/
noncomputable def CorrectAnswerOn (task : Task) {I : Instance} {rV rE : ℕ}
    (Sols : Set (Assignment I rV rE)) (w : Weights I rV rE) (out : List Bool) : Prop :=
  match task with
  | .decide => out = [decide Sols.Nonempty]
  | .minimize =>
      (Sols = ∅ ∧ out = [false]) ∨
      ∃ A ∈ MinOf Sols w, out = true :: (encodeInt (weight w A) ++ encodeAssignment A)
  | .maximize =>
      (Sols = ∅ ∧ out = [false]) ∨
      ∃ A ∈ MaxOf Sols w, out = true :: (encodeInt (weight w A) ++ encodeAssignment A)
  | .count => out = encodeNat Sols.ncard
  | .countMin => out = encodeNat (MinOf Sols w).ncard
  | .countMax => out = encodeNat (MaxOf Sols w).ncard

end MetricMSO.Supplement


