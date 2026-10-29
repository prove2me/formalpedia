-- Prove2me | Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
-- name    : ZhangTangLabelCut_LP2_LabelCut
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:11:58.765466+00:00
-- url     : https://prove2.me/theorems/4f4e107c-0f5b-403b-aa4f-f95f3639065b
-- title:
--   Label cuts, distinct-label LP2 and the integrality ratio
-- statement:
--   A label-cut instance consists of a finite graph, a finite label set $L$, exactly one label per edge, and distinct terminals $s,t$. A subset $S\subseteq L$ is a label cut when it meets the label set of every simple $s$–$t$ path. The integral optimum is the minimum of $|S|$ over such cuts. The all-label set is always a cut, so this minimum is well-defined and attained.
--
--   For each simple terminal path $P$, let $L(P)$ be the set of its distinct labels. LP2 is the covering program
--   $$\min\sum_{\ell\in L}x_\ell\quad\text{subject to }x_\ell\ge0,\quad\sum_{\ell\in L(P)}x_\ell\ge1\text{ for every }P.$$
--   Repeated path-label sets give identical rows and are stored once. Repeated labels along a path are counted once. There is no upper bound on a variable. The real fractional value is the real part of the extended-real LP value. These particular LPs always have a finite, attained value: the all-ones vector is feasible and costs are nonnegative. A disconnected instance has value zero.
--
--   An admissible ratio witness is a simple graph with a terminal path and a finite strictly positive LP value. Its ratio is $\operatorname{OPT}/\operatorname{OPT}_f$. The explicit admissibility requirement excludes division by zero and any use of the totalized real part at infinity.
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), pp. 2, 4, 7, Definition 1.1, integrality gap and LP2

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP

namespace ZhangTangLabelCut.LP2

structure LabelCut where
  graph : FiniteGraph
  L : Type
  finiteL : Fintype L
  label : graph.E → L
  s : graph.V
  t : graph.V
  distinct : s ≠ t

attribute [instance] LabelCut.finiteL

noncomputable def LabelCut.pathLabels (I : LabelCut) (p : Path I.graph I.s I.t) : Finset I.L :=
  by classical exact Finset.univ.image (fun e => I.label (p.edge e))

/-- Removing a set of labels must hit every simple terminal path. -/
def LabelCut.Cut (I : LabelCut) (S : Finset I.L) : Prop :=
  ∀ p : Path I.graph I.s I.t, ∃ j, I.label (p.edge j) ∈ S

/-- The minimum number of removed labels, computed over all label subsets. -/
noncomputable def LabelCut.opt (I : LabelCut) : ℕ :=
  sInf {c | ∃ S : Finset I.L, I.Cut S ∧ S.card = c}

/-- LP2 has one row for each distinct path-label set; no coordinate upper bounds. -/
noncomputable def LabelCut.lp (I : LabelCut) : CoveringLP I.L := by
  classical
  exact { rows := Finset.univ.filter (fun R => ∃ p : Path I.graph I.s I.t, I.pathLabels p = R)
          cost := fun _ => 1
          rhs := fun _ => 1 }

noncomputable def LabelCut.frac (I : LabelCut) : ℝ := I.lp.value.toReal

/-- Ratio witnesses must be simple, connected and have a finite positive LP value. -/
def LabelCut.Admissible (I : LabelCut) : Prop :=
  I.graph.Simple ∧ Nonempty (Path I.graph I.s I.t) ∧
  (∃ v : ℝ, 0 < v ∧ I.lp.value = (v : EReal))

noncomputable def LabelCut.ratio (I : LabelCut) : ℝ := (I.opt : ℝ) / I.frac

end ZhangTangLabelCut.LP2


