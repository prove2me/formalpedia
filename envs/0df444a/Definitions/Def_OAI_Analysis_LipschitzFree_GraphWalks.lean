-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
-- name    : OAI_Analysis_LipschitzFree_GraphWalks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:13:03.399992+00:00
-- url     : https://prove2.me/theorems/0295b0ca-62e0-4edb-9440-01c47329591d
-- title:
--   Walks matched to state sequences, good vertices and record lengths in port graphs
-- statement:
--   Let $X$ be the vertex set of a port graph with port set $D$ (moves $x\mapsto x\cdot e$, each undone by the reverse port $\bar e$), let $S$ be a set of states, $\kappa$ a compatibility relation between vertices and states, and $\tau$ a transition relation on $S$. For a word $w=e_1\cdots e_m$ of ports and $x\in X$ let $x_0=x$ and $x_t=x_{t-1}\cdot e_t$ be the vertices visited by the walk from $x$ along $w$. The word is *reduced* if $e_{t+1}\neq\bar e_t$ for $1\le t<m$.
--
--   1. **Matched walks.** The walk from $x$ along $w$ is *matched* starting from the state $j$ if there are states $j=j_0,j_1,\dots,j_m$ with
--   $$\kappa(x_t,j_t)\ \text{ for } 0\le t\le m\qquad\text{and}\qquad \tau(j_{t-1},j_t)\ \text{ for } 1\le t\le m .$$
--   2. **Good vertices.** For $n\in\mathbb{N}$, a vertex $x$ is *$n$-good* if for every state $j$ and every reduced word $w$ of length exactly $n$, the walk from $x$ along $w$ is not matched starting from $j$.
--   3. **Records.** For $x\in X$, a port $e\in D$, a state $j\in S$ and $n\in\mathbb{N}$, the record $\operatorname{rec}_n(x,e,j)$ is the largest $t\le n$ such that $t=0$ or some reduced word of length $t$ with first letter $e$ gives a walk from $x$ that is matched starting from $j$:
--   $$\operatorname{rec}_n(x,e,j)=\max\Bigl(\{0\}\cup\bigl\{\,t\le n:\ \exists\,w' \text{ with } |e\,w'|=t,\ e\,w' \text{ reduced and matched from } (x,j)\,\bigr\}\Bigr).$$
--
--   These notions formalize following a walk in the graph by a chain of states. In the construction the states are points of a finite subset of the metric block, compatibility means that the label of the vertex is close to the label of the state, and transitions join nearby points; the record measures how long a matched reduced walk leaving $x$ through the port $e$ can be continued, up to the horizon $n$.
--
--   **Formalization Note** `PortGraph.Matched` is defined by recursion on the word (`compatible x j` for the empty word, and `compatible x j ∧ ∃ k, trans j k ∧ Matched (move x e) k w` for `e :: w`); `Good n x` quantifies over all `j` and all `w` with `w.length = n` and `G.Reduced w`; `RecordLength x e j t` is `t = 0 ∨ …`; and `record` is `Nat.findGreatest (RecordLength x e j) n`, the largest $t\le n$ satisfying it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphWalks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphWalks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests

namespace OAI

/-!
# Matched graph walks and exceptional record estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

def Matched : X → S → List D → Prop
  | x, j, [] => compatible x j
  | x, j, e::w => compatible x j ∧ ∃ k, trans j k ∧ Matched (G.move x e) k w

def Good (n : ℕ) (x : X) : Prop :=
  ∀ j w, w.length = n → G.Reduced w → ¬ G.Matched compatible trans x j w

def RecordLength (x : X) (e : D) (j : S) (t : ℕ) : Prop :=
  t = 0 ∨ ∃ w : List D, (e::w).length = t ∧ G.Reduced (e::w) ∧
    G.Matched compatible trans x j (e::w)

def record (n : ℕ) (x : X) (e : D) (j : S) : ℕ :=
  Nat.findGreatest (G.RecordLength compatible trans x e j) n

end DiscreteFree.PortGraph
end

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

end DiscreteFree.PortGraph
end

end

end OAI


