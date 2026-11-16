-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Supplement_DecisionTree
-- name    : ParityBarrier563_Trilinear_Supplement_DecisionTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:40:47.280226+00:00
-- url     : https://prove2.me/theorems/c5f42dd6-1214-4a22-a096-da0dc19d8dbf
-- title:
--   Decision trees with CNF or DNF leaves
-- statement:
--   A finite binary decision tree queries one input variable at an internal node and has a Boolean function on the whole input cube at each leaf. Evaluation follows queried bits and evaluates the reached leaf on the same input. Define
--   $$\operatorname{depth}(\text{leaf})=0,\quad\operatorname{depth}(\text{query}(v,T_0,T_1))=1+\max(\operatorname{depth}T_0,\operatorname{depth}T_1).$$
--   GoodLeaves means that every leaf function is a k-CNF or a k-DNF; the alternatives may be mixed. Equality of tree evaluation with F requires agreement only on each leaf's path subcube. This is the representation used in Lemma 6.1, including depth zero.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), §2, printed p.11 / PDF 13; Lemma 6.1, printed p.26 / PDF 28

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_CNF

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- A finite decision tree with Boolean functions at its leaves, not necessarily constants. -/
inductive LeafTree (V : Type)
  | leaf (F : BoolFn V)
  | query (v : V) (zero one : LeafTree V)

namespace LeafTree
variable {V : Type}
/-- Evaluation follows the queried bit and evaluates the reached leaf function on that input. -/
def eval : LeafTree V → BoolFn V
  | .leaf F => F
  | .query v zero one => fun x => if x v then one.eval x else zero.eval x

/-- Depth counts queries, so a leaf has depth zero. -/
def depth : LeafTree V → ℕ
  | .leaf _ => 0
  | .query _ zero one => 1 + max zero.depth one.depth

/-- Leaf types may be mixed; agreement with the target is required only along reached paths
by equality with eval, not by a global equality of every leaf with the target. -/
def GoodLeaves [DecidableEq V] (k : ℕ) : LeafTree V → Prop
  | .leaf F => IsCNF k F ∨ IsDNF k F
  | .query _ zero one => zero.GoodLeaves k ∧ one.GoodLeaves k
end LeafTree

end ParityBarrier563.Trilinear.Supplement


