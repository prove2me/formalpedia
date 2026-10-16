-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:16:19.282277+00:00
-- url     : https://prove2.me/theorems/018d9141-f8e7-4ba4-92d7-46230dd6f50f
-- title:
--   Compatibility, transitions, support colors and exception sets for finite state sets in a metric block
-- statement:
--   Let $G$ be a port graph with vertex set $X$ and a finite set $E$ of ports: every port $e$ has a reverse port $\bar e$ with $\bar{\bar e}=e$, and every vertex $x$ has a neighbor $x\cdot e$ with $(x\cdot e)\cdot\bar e=x$. A word $w=e_1e_2\cdots e_m$ of ports moves $x$ along the walk $x_0=x$, $x_t=x_{t-1}\cdot e_t$; the word is *reduced* if no port is immediately followed by its reverse, i.e. $e_{t+1}\neq\bar e_t$. Let $C$ be a finite set of colors, $\chi\colon X\to C$ a coloring, and $\mathrm{cap},R,L,K\in\mathbb{N}$ with $R>0$.
--
--   These data determine a metric block $P=X\sqcup\mathcal{A}$ whose points are the vertices and the anchors. For a vertex $x$ and a color $i$, the capped label $\lambda_i(x)\in\{0,\dots,\mathrm{cap}\}$ is the least $n$ such that $n=\mathrm{cap}$ or some port word of length $n$ leads from $x$ to a vertex of color $i$. The anchors $\mathcal{A}$ are the label vectors $\lambda(x)=(\lambda_i(x))_{i\in C}$ that occur, and an anchor $a$ has label $\lambda(a)=a$. Label vectors are compared in the supremum distance $\rho(a,b)=\max_{i\in C}|a_i-b_i|$. The metric $d$ on $P$ is the integer-valued shortest-chain metric for the weights $1$ between adjacent vertices, $R$ between a vertex and its own label anchor, $2R+\rho(a,b)$ between distinct anchors $a,b$, and $4R+\mathrm{cap}$ between all other pairs of distinct points.
--
--   The module defines four objects on such a block.
--
--   1. **Compatibility.** A vertex $x\in X$ is compatible with a point $j\in P$ when $\rho\bigl(\lambda(x),\lambda(j)\bigr)\le K+2L+1$.
--   2. **Transitions.** Two points $j,k\in P$ form a transition when $d(j,k)\le 2L$.
--   3. **Support colors.** The support colors of $j\in P$ are the colors $i\in C$ with $\lambda_i(j)<\mathrm{cap}$.
--   4. **Exception sets.** Fix a finite set $S\subseteq P$ of states and $n\in\mathbb{N}$, and use compatibility and transitions only for states in $S$. A port word $w=e_1\cdots e_m$ is *matched* at $(x,j)$, where $j\in S$, if there are states $j_0=j,j_1,\dots,j_m\in S$ such that $x_t$ is compatible with $j_t$ for $0\le t\le m$ and $(j_{t-1},j_t)$ is a transition for $1\le t\le m$. The vertex $x$ is *$n$-good* if no reduced word of length exactly $n$ is matched at $(x,j)$ for any $j\in S$. For a port $e$ and a state $j\in S$, the record $r_n(x,e,j)$ is the largest $t\le n$ such that $t=0$ or some reduced word of length $t$ beginning with $e$ is matched at $(x,j)$. The exception set of a vertex $x\in X$ and a port $e\in E$ is
--   $$
--   \mathcal{E}_{S,n}(x,e)=\bigl\{\,j\in S:\ x\ \text{is not } n\text{-good, or } r_n(x,g,j)<r_n(x,e,j)\ \text{for every port } g\neq e\,\bigr\}.
--   $$
--   Thus $\mathcal{E}_{S,n}(x,e)=S$ when $x$ is not $n$-good; otherwise it is the set of states at which the port $e$ holds the strict record.
--
--   These are the finite-state data used to build opposing scalar Lipschitz test functions along the edges $\{x,x\cdot e\}$ of a metric block. By definition, at an $n$-good vertex a state belongs to the exception sets of at most one port, which is what allows the mass that coefficient vectors put on exception sets to be averaged over all edges. This averaging is the key step in showing that the Lipschitz-free space of a metric block fails the bounded approximation property with a prescribed constant.
--
--   **Formalization Note** The definitions `Compatible`, `Transition`, `supportColors` and `exceptionSet` live in `DiscreteFree.MetricBlock`. The point type `Point G color cap R` is `X ⊕ Anchor G color cap`, and its metric instance requires `Fact (0 < R)`. `Compatible` compares the `dist` of box labels (the natural-number supremum distance, cast to the reals) with the cast of $K+2L+1$. `exceptionSet S n x e` is a `Set` of elements of the finset subtype `S`, built from `PortGraph.Good`, `PortGraph.record` (a `Nat.findGreatest` over $t\le n$) and `Exceptional`, with compatibility and transitions restricted to `S`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ScalarTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/ScalarTests.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming

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


