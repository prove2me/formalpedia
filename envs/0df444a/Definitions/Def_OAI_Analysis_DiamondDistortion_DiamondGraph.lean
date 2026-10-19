-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
-- name    : OAI_Analysis_DiamondDistortion_DiamondGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:04:06.45595+00:00
-- url     : https://prove2.me/theorems/bc60fa08-2304-481c-952b-db1aa1851e2b
-- title:
--   Countably branching diamond graphs: distortion hypothesis, slopes, midpoint deviations and the quadratic lens property
-- statement:
--   **Diamond graphs.** The stage-$n$ graph $G_n$ is built recursively. $G_0$ has two vertices $\bot,\top$ and one edge between them. Given $G_n$, in which every edge $e$ has a lower endpoint $e^-$ and an upper endpoint $e^+$, the graph $G_{n+1}$ keeps all vertices of $G_n$ and adds, for every edge $e$ of $G_n$ and every $i\in\mathbb{N}$, a new vertex $m_{e,i}$; its edges are $(e,i,-)$, from $e^-$ to $m_{e,i}$, and $(e,i,+)$, from $m_{e,i}$ to $e^+$. Thus every edge is replaced by countably many parallel paths of length two. Write $V_n$ for the vertex set of $G_n$, regard $G_n$ as an undirected simple graph, and let
--
--   $$
--   d_n(u,v)=\frac{\mathrm{dist}_{G_n}(u,v)}{2^n}\qquad(u,v\in V_n)
--   $$
--
--   be the shortest-path distance rescaled so that the edges of $G_n$ have length $2^{-n}$. The file defines:
--
--   1. **Base edge.** $\epsilon_0$ is the edge of $G_0$ and $\epsilon_{n+1}=(\epsilon_n,0,-)$; its lower endpoint is $\bot$ at every stage.
--
--   2. **Extended potential.** For $\varphi:V_n\to\mathbb{R}$, the function $\tilde\varphi:V_{n+1}\to\mathbb{R}$ with $\tilde\varphi(u)=2\varphi(u)$ for old vertices $u\in V_n$ and $\tilde\varphi(m_{e,i})=\varphi(e^-)+\varphi(e^+)$.
--
--   3. **Distortion hypothesis.** For a normed abelian group $X$, $k\in\mathbb{N}$, $f:V_k\to X$ and reals $D,s$, the statement $\mathrm{Dist}(k,f,D,s)$ means: $D\ge1$, $s>0$, and for all $u,v\in V_k$
--   $$
--   s\,d_k(u,v)\le\|f(u)-f(v)\|\le D\,s\,d_k(u,v).
--   $$
--
--   4. **Slopes and midpoint deviations.** Let $X$ be a real normed space. For $f:V_n\to X$ and an edge $e$ of $G_n$, the slope is $\mathrm{sl}_f(e)=2^n\big(f(e^+)-f(e^-)\big)$. For $f:V_{n+1}\to X$, an edge $e$ of $G_n$ and $i\in\mathbb{N}$, the midpoint deviation is
--   $$
--   \mathrm{dev}_f(e,i)=2^n\big(2f(m_{e,i})-f(e^-)-f(e^+)\big).
--   $$
--   If $g$ is the restriction of $f$ to $V_n$, then $\mathrm{sl}_g(e)+\mathrm{dev}_f(e,i)$ and $\mathrm{sl}_g(e)-\mathrm{dev}_f(e,i)$ are the slopes of $f$ on the two halves $(e,i,-)$ and $(e,i,+)$.
--
--   5. **Quadratic lens property.** A normed abelian group $X$ has this property if for every $x\in X$, every sequence $(z_i)_{i\in\mathbb{N}}$ in $X$ and all reals $R\ge0$ and $\delta>0$ the following holds: if $\|x+z_i\|\le R$ and $\|x-z_i\|\le R$ for all $i$, and $\|z_i-z_j\|\ge\delta$ for all $i\neq j$, then
--   $$
--   \|x\|^2+\frac{\delta^2}{16}\le R^2.
--   $$
--
--   6. **Headline.** The proposition that for each of the two spaces $X=\mathcal D_{\mathrm{forest}}$ and $X=\mathcal P_{\mathrm{tree}}$ described below, for every $k\in\mathbb{N}$, every $f:V_k\to X$ and all reals $D,s$ with $\mathrm{Dist}(k,f,D,s)$, one has $1+k/4\le D^2$.
--
--   The two spaces come from segment norms. For a set $\iota$ with a partial order in which the predecessors of every vertex form a chain, the segments are the finite order intervals $[a,b]$ with $a\le b$, and the segment norm of a finitely supported $u:\iota\to\mathbb{R}$ is the supremum of $\big(\sum_i(\sum_{v\in S_i}u(v))^2\big)^{1/2}$ over finite families of pairwise disjoint segments; let $J_\iota$ be the completion, $J_\iota^*$ its continuous dual and $e_v^*\in J_\iota^*$ the continuous extension of $u\mapsto u(v)$. $\mathcal D_{\mathrm{forest}}$ is the full dual $J_\iota^*$ for $\iota$ the forest of pairs $(h,w)$, $h\ge1$, $w$ a word over $\mathbb{N}$ of length at most $h$, with $(h,w)\le(h',w')$ iff $h=h'$ and $w$ is a prefix of $w'$. $\mathcal P_{\mathrm{tree}}$ is the norm closure of the linear span of the $e_w^*$ in $J_\iota^*$ for $\iota$ the tree of all finite words over $\mathbb{N}$ under the prefix order.
--
--   In the surrounding development the quadratic lens property is the geometric input of the distortion argument: for a space with this property, applying it stage by stage to slopes and midpoint deviations shows $1+k/4\le D^2$ whenever $\mathrm{Dist}(k,f,D,s)$ holds, and both model spaces are shown to have the property. The extended potential serves as a test function showing that one subdivision preserves the rescaled distance between old vertices, $d_{n+1}(u,v)=d_n(u,v)$ for $u,v\in V_n$, and the base edge is a canonical edge of $G_k$ for every $k$.
--
--   **Formalization Note** Vertices and edges are the recursive types `Diamond.Vertex n` and `Diamond.Edge n`: stage-$0$ vertices are `false` ($\bot$) and `true` ($\top$), and at stage $n+1$ old vertices are `Sum.inl u` and new ones `Sum.inr (e, i)`; `endpoint n e false` and `endpoint n e true` are $e^-$ and $e^+$, and $d_n$ is `Diamond.distance n`. The condition $D\ge1$ is part of `HasDistortion`; since $G_k$ is connected, $d_k(u,v)>0$ for $u\neq v$, so given $s>0$ it also follows from the two inequalities. `Headline` is stated for `ForestDual` and `InfinitePredual`, the latter being a closed subspace with the induced norm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

def baseEdge : (n : ℕ) → Edge n
  | 0 => ()
  | n+1 => (baseEdge n,0,false)

def extendPotential {n : ℕ} (φ : Vertex n → ℝ) : Vertex (n+1) → ℝ
  | Sum.inl u => 2*φ u
  | Sum.inr (e,_) => φ (endpoint n e false)+φ (endpoint n e true)

/-- The standing all-pairs distortion hypothesis, with its positive arbitrary scale. -/
def HasDistortion {X : Type*} [NormedAddCommGroup X]
    (k : ℕ) (f : Vertex k → X) (D s : ℝ) : Prop :=
  1 ≤ D ∧ 0 < s ∧ ∀ u v,
    s * distance k u v ≤ ‖f u - f v‖ ∧
    ‖f u - f v‖ ≤ D * s * distance k u v

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The oriented slope of a stage edge in the normalized metric. -/
def slope {n : ℕ} (f : Vertex n → X) (e : Edge n) : X :=
  (2:ℝ)^n • (f (endpoint n e true)-f (endpoint n e false))

/-- Midpoint deviations normalized by the lengths of the parent edges. -/
def deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) : X :=
  (2:ℝ)^n • ((2:ℝ) • f (Sum.inr (e,i))-
    f (Sum.inl (endpoint n e false))-f (Sum.inl (endpoint n e true)))

/-- An infinite separated symmetric lens with the exact quadratic constant. -/
def QuadraticLens (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∀ (x : X) (z : ℕ → X) (R ε : ℝ),0 ≤ R → 0 < ε →
    (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
    (∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖^2+ε^2/16 ≤ R^2

end Diamond

/-- The exact two-model unconditional headline; neither intrinsic estimate is a hypothesis. -/
def Headline : Prop :=
  (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
    Diamond.HasDistortion k f D s → 1 + (k : ℝ) / 4 ≤ D ^ 2) ∧
  (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
    Diamond.HasDistortion k f D s → 1 + (k : ℝ) / 4 ≤ D ^ 2)

end DiamondDistortion

end

end OAI


