-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
-- name    : OAI_Analysis_LipschitzFree_ScalarTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:22:23.673425+00:00
-- url     : https://prove2.me/theorems/45292a58-a3c5-4620-951a-29d5a7c54629
-- title:
--   Compatibility, transitions, support colours and exception sets on a metric block
-- statement:
--   Setting: a port graph with vertex set $X$ and a finite port set $E$ (moves $x\mapsto x\cdot e$, each undone by its reverse port), a finite set $C$ of colours with a colouring $\chi:X\to C$, natural numbers $\mathrm{cap}$, $R>0$, $L$ and $K$, and the associated metric block: the point set $P=X\sqcup\mathcal{A}$ of vertices and label anchors with its integer shortest-path metric $d$. Every point $j\in P$ has a box label $\lambda(j)\in\{0,\dots,\mathrm{cap}\}^C$ (for a vertex $x$, $\lambda_i(x)$ is the length of a shortest walk from $x$ to colour $i$, truncated at $\mathrm{cap}$; an anchor is its own label), and $\rho(a,b)=\max_{i\in C}|a_i-b_i|$ is the supremum distance of box labels.
--
--   1. **Compatibility.** A vertex $x\in X$ is compatible with a point $j\in P$ if $\rho(\lambda(x),\lambda(j))\le K+2L+1$.
--   2. **Transitions.** Two points $j,k\in P$ form a transition if $d(j,k)\le 2L$.
--   3. **Support colours.** The support colours of $j\in P$ are the colours $i\in C$ with $\lambda_i(j)<\mathrm{cap}$.
--   4. **Exception sets.** Fix a finite set $S\subseteq P$ of states and a horizon $n\in\mathbb{N}$. A walk from $x$ along a word $e_1\cdots e_m$ of ports, visiting $x=x_0,x_1,\dots,x_m$, is *matched* from $j\in S$ if there are $j=j_0,\dots,j_m\in S$ with each $x_t$ compatible with $j_t$ and each $(j_{t-1},j_t)$ a transition. A word is reduced if no port is immediately followed by its reverse. The vertex $x$ is *$n$-good* if no reduced word of length exactly $n$ gives a walk from $x$ matched from some state, and the record $\operatorname{rec}_n(x,e,j)$ is the largest $t\le n$ such that $t=0$ or some reduced word of length $t$ starting with the port $e$ gives a walk from $x$ matched from $j$. For $x\in X$ and a port $e\in E$ the exception set is
--   $$\mathcal{E}_n(x,e)=\bigl\{\,j\in S:\ x \text{ is not } n\text{-good, or } \operatorname{rec}_n(x,g,j)<\operatorname{rec}_n(x,e,j)\ \text{for every port } g\neq e\,\bigr\}.$$
--   Thus $\mathcal{E}_n(x,e)=S$ when $x$ is not $n$-good, and otherwise it consists of the states at which the port $e$ holds the strict record.
--
--   These are the finite-state data from which the scalar Lipschitz tests along an edge $(x,x\cdot e)$ of the graph are built. At an $n$-good vertex the exception sets of different ports are disjoint, which is what allows the mass of the coefficient vectors on exception sets to be averaged over all edges.
--
--   **Formalization Note** `MetricBlock.Compatible G color cap R L K x j` uses the `dist` of `BoxLabel C cap` with the bound $K+2L+1$ cast from $\mathbb{N}$; `Transition` uses the block metric, which requires `Fact (0 < R)`; `supportColors` is a `Finset C`; and `exceptionSet S n x e` is a `Set` of elements of the finset subtype `S`, built from `PortGraph.Good`, `PortGraph.record` and `Exceptional`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ScalarTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/ScalarTests.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps

namespace OAI

/-!
# Finite-state records and opposing scalar Lipschitz tests
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X E C : Type*} [Fintype C] [Fintype E]
    (G : PortGraph X E) (color : X → C) (cap R L K : ℕ) [Fact (0 < R)]

def Compatible (x : X) (j : Point G color cap R) : Prop :=
  dist (originalLabel G color cap x) (label G color cap R j) ≤ (K+2*L+1 : ℕ)

def Transition (j k : Point G color cap R) : Prop := dist j k ≤ (2*L : ℕ)

def supportColors (j : Point G color cap R) : Finset C :=
  Finset.univ.filter (fun i => (label G color cap R j i).val < cap)

def exceptionSet (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E) : Set S :=
  {j | ¬ G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x ∨
    Exceptional (G.record (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x) e j}

end DiscreteFree.MetricBlock
end

end

end OAI


