-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:10:28.793573+00:00
-- url     : https://prove2.me/theorems/5ca6d54d-4178-4f92-b017-cf3fbcfa2786
-- title:
--   Walks in a port graph matched by state sequences, good vertices and record lengths
-- statement:
--   Let $G$ be a port graph with vertex set $X$ and port set $D$: an involution $e\mapsto\bar e$ of $D$ and moves $(x,e)\mapsto x\cdot e$ with $(x\cdot e)\cdot\bar e=x$. A word $e_1\cdots e_m$ over $D$ is reduced if $e_{t+1}\neq\bar e_t$ for $1\le t<m$. Let $S$ be a set of states, $\mathrm{comp}\subseteq X\times S$ a compatibility relation between vertices and states, and $\mathrm{tr}\subseteq S\times S$ a transition relation.
--
--   1. **Matched walks.** A vertex $x$, a state $j$ and a word $w=e_1\cdots e_m$ are matched if there are states $j=j_0,j_1,\dots,j_m$ such that, along the walk $x_0=x$, $x_t=x_{t-1}\cdot e_t$,
--   $$\mathrm{comp}(x_t,j_t)\ \ (0\le t\le m)\qquad\text{and}\qquad \mathrm{tr}(j_{t-1},j_t)\ \ (1\le t\le m).$$
--   2. **Good vertices.** For $n\in\mathbb{N}$, a vertex $x$ is $n$-good if there is no state $j$ and no reduced word $w$ of length exactly $n$ such that $x$, $j$, $w$ are matched.
--   3. **Record lengths.** For a vertex $x$, a port $e$ and a state $j$, a number $t\in\mathbb{N}$ is a record length if $t=0$ or there is a reduced word of length $t$ beginning with $e$ that is matched with $x$ and $j$.
--   4. **Record.** For $n\in\mathbb{N}$, the record $\mathrm{rec}_n(x,e,j)$ is the largest record length not exceeding $n$:
--   $$\mathrm{rec}_n(x,e,j)=\max\Bigl(\{0\}\cup\bigl\{\,|w| : |w|\le n,\ w=e\,w'\text{ reduced},\ (x,j,w)\text{ matched}\,\bigr\}\Bigr).$$
--
--   These notions track how far a reduced walk from $x$ can be shadowed by a chain of states with allowed transitions. In the construction the states are points of a metric block, compatibility is defined through distances between labels and transitions through distances in the block, and the record function determines the exceptional ports at each state.
--
--   **Formalization Note** `PortGraph.Matched comp tr x j w` is defined by recursion on the word: for the empty word it is $\mathrm{comp}(x,j)$, and for $e::w$ it is $\mathrm{comp}(x,j)$ together with some $k$ with $\mathrm{tr}(j,k)$ and `Matched (move x e) k w`. `Good`, `RecordLength` and `record` are as above; `record` uses `Nat.findGreatest`, which is well defined because $t=0$ is always a record length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphWalks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphWalks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming

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


