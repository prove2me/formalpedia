-- Prove2me | Definitions.Def_DirTeleMC_Supplement_TEArb
-- name    : DirTeleMC_Supplement_TEArb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:37:57.476471+00:00
-- url     : https://prove2.me/theorems/a4ecf20f-1a40-492b-9570-9967fc87643f
-- title:
--   The time-expanded digraph $G_\theta$ and its DB-DST solutions
-- statement:
--   Let $G=(V,E)$ be the digraph of an instance, $s$ its source and $K$ its terminal set, and let $\theta\ge1$. The **time-expanded digraph** $G_\theta$ has
--
--   1. a **state node** $(v,t)$ for every $v\in V$ and $0\le t\le\theta$ (vertex $v$ at the end of round $t$);
--   2. a **call node** $c(v,t)$ for every $v\in V$ and $0\le t<\theta$ (the call of $v$ in round $t+1$);
--   3. a **sink** $\hat x$ for every terminal $x\in K$.
--
--   Its arcs are $(v,t)\to(v,t+1)$ and $(v,t)\to c(v,t)$ for $t<\theta$, $c(v,t)\to(w,t+1)$ for every arc $(v,w)\in E$ and $t<\theta$, and $(x,\theta)\to\hat x$ for $x\in K$. The root is $(s,0)$; state nodes have degree bound $2$ and call nodes degree bound $1$, and all costs are $0$.
--
--   An **out-arborescence of $G_\theta$ rooted at $(s,0)$ containing all sinks** is a set of nodes of $G_\theta$ containing $(s,0)$ and every sink, with a parent for every other node such that $(\text{parent},\text{node})$ is an arc of $G_\theta$ and following parents always leads back to $(s,0)$. It is a **solution of DB-DST** if every state node has at most two children and every call node at most one.
--
--   These objects carry the reduction from directed telephone multicast to degree-bounded directed Steiner tree of Theorem B.8.
--
--   **Formalization Note** Nodes are an inductive type over all vertices and all times; `IsTENode` cuts out the nodes of $G_\theta$. The parent of the root is not used.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Definition B.7, p.33 (PDF p.34); Theorem B.8, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_DirTeleMC_Inst

namespace DirTeleMC.Supplement

open DirTeleMC

/-- **Nodes of the time-expanded digraph** `G_θ` (Definition B.7).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Definition B.7, p.33: "a state node (v, t) for every v ∈ V and 0 ≤ t ≤ θ (vertex v
at the end of round t), a call node c(v, t) for every v ∈ V and 0 ≤ t < θ (the call of v in round t + 1), and a
sink x̂ for every terminal x ∈ K".

**Formalization Note.** The type contains a node for every vertex and every time; `IsTENode I θ` below cuts out the
nodes of `G_θ` (`t ≤ θ` for state nodes, `t < θ` for call nodes, `x ∈ K` for sinks). -/
inductive TENode (n : ℕ) where
  | state (v : Fin n) (t : ℕ)
  | call (v : Fin n) (t : ℕ)
  | sink (x : Fin n)
  deriving DecidableEq

/-- `z` is a node of `G_θ` (Definition B.7, p.33). -/
def IsTENode (I : Inst) (θ : ℕ) : TENode I.n → Prop
  | .state _ t => t ≤ θ
  | .call _ t => t < θ
  | .sink x => x ∈ I.K

/-- **The arcs of `G_θ`** (Definition B.7, p.33): "(v, t) → (v, t + 1) and (v, t) → c(v, t) for every v ∈ V and
t < θ, c(v, t) → (w, t + 1) for every arc (v, w) ∈ E(G) and t < θ, and (x, θ) → x̂ for every x ∈ K". -/
def teArc (I : Inst) (θ : ℕ) : TENode I.n → TENode I.n → Prop
  | .state v t, .state w t' => w = v ∧ t' = t + 1 ∧ t < θ
  | .state v t, .call w t' => w = v ∧ t' = t ∧ t < θ
  | .call v t, .state w t' => I.adj v w = true ∧ t' = t + 1 ∧ t < θ
  | .state v t, .sink x => x = v ∧ t = θ ∧ x ∈ I.K
  | _, _ => False

/-- A finite set of nodes of `G_θ` with a parent map (a candidate out-arborescence of `G_θ`). -/
structure TEArb (n : ℕ) where
  verts : Finset (TENode n)
  parent : TENode n → TENode n

namespace TEArb

/-- The root `(s, 0)` of `G_θ` (Definition B.7, p.33: "The root is (s, 0)"). -/
def root (I : Inst) : TENode I.n := .state I.s 0

/-- **`A` is an out-arborescence of `G_θ` rooted at `(s, 0)` that contains all sinks** (Definition B.7 and
Theorem B.8, pp.33–34). Its nodes are nodes of `G_θ`, the root `(s, 0)` is one of them, every other node is entered
by the arc `(parent z, z)` of `G_θ` from a node of `A`, iterating the parent map from every node reaches the root
(so `A` has no cycle), and every sink `x̂`, `x ∈ K`, is a node of `A`.

**Formalization Note.** The parent of the root is not used. -/
def IsOutArbSinks (I : Inst) (θ : ℕ) (A : TEArb I.n) : Prop :=
  (∀ z ∈ A.verts, IsTENode I θ z) ∧ root I ∈ A.verts ∧
    (∀ z ∈ A.verts, z ≠ root I → A.parent z ∈ A.verts ∧ teArc I θ (A.parent z) z) ∧
    (∀ z ∈ A.verts, ∃ m, A.parent^[m] z = root I) ∧
    ∀ x ∈ I.K, TENode.sink x ∈ A.verts

/-- The children of a node `z` of `A`: the non-root nodes of `A` whose parent is `z`. -/
def children (I : Inst) (A : TEArb I.n) (z : TENode I.n) : Finset (TENode I.n) :=
  A.verts.filter fun c => c ≠ root I ∧ A.parent c = z

/-- `A` respects the degree bounds of Definition B.7 (p.33: "state nodes have degree bound 2 and call nodes have
degree bound 1"): every state node has at most two children and every call node at most one. -/
def RespectsDegreeBounds (I : Inst) (A : TEArb I.n) : Prop :=
  ∀ z ∈ A.verts,
    match z with
    | .state _ _ => (A.children I z).card ≤ 2
    | .call _ _ => (A.children I z).card ≤ 1
    | .sink _ => True

end TEArb

/-- **`G_θ` has a solution of DB-DST** (Theorem B.8(i), p.34: "an out-arborescence rooted at (s, 0) that contains
all sinks and respects all degree bounds"). All costs of `G_θ` are `0` (Definition B.7), so a solution is any
feasible arborescence. -/
def HasDBDSTSol (I : Inst) (θ : ℕ) : Prop :=
  ∃ A : TEArb I.n, A.IsOutArbSinks I θ ∧ A.RespectsDegreeBounds I

end DirTeleMC.Supplement


