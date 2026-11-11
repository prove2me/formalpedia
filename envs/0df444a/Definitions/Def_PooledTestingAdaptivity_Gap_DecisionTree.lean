-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_DecisionTree
-- name    : PooledTestingAdaptivity_Gap_DecisionTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:36.287412+00:00
-- url     : https://prove2.me/theorems/5bbcf5e4-502a-457c-b595-e24c1967f868
-- title:
--   Binary testing trees: operations on the published query-tree type
-- statement:
--   A finite binary decision tree either stops or asks a question labelled by an element of a type $L$. Its two continuations correspond to the Boolean reply. Given a reply function $r:L\to\{0,1\}$, the ordered path is
--
--   $$P_{\mathrm{stop}}(r)=(),\qquad P_{\mathrm{query}(t,k)}(r)=(t)\mathbin{+\!+}P_{k(r(t))}(r).$$
--
--   The general tree type and query transcript are reused from the published definition `UniqueOptScores_QTree`, with unit-valued leaves. The additional operation checks a predicate on every internal label, including unreachable nodes. These operations separate the general decision tree from its pooled-testing interpretation.
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), §2, printed p. 4, PDF p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_UniqueOptScores_QTree

namespace PooledTestingAdaptivity.Gap

/-- Reuse the published general binary query tree; leaves only stop. -/
abbrev DecisionTree (Label : Type) := UniqueOptScores.QTree Label Unit

/-- The published query transcript preserves order and repetitions. -/
def DecisionTree.path {Label : Type} (observe : Label → Bool)
    (T : DecisionTree Label) : List Label := T.queries observe

/-- Predicate on all internal labels, including unreachable nodes. -/
def DecisionTree.allLabels {Label : Type} (p : Label → Prop) : DecisionTree Label → Prop
  | .leaf _ => True
  | .query t k => p t ∧ DecisionTree.allLabels p (k true) ∧ DecisionTree.allLabels p (k false)

end PooledTestingAdaptivity.Gap


