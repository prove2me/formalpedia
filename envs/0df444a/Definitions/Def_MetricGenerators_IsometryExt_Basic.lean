-- Prove2me | Definitions.Def_MetricGenerators_IsometryExt_Basic
-- name    : MetricGenerators_IsometryExt_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:05.633993+00:00
-- url     : https://prove2.me/theorems/5a2a42c1-cb8d-4521-8acf-6dda45009141
-- title:
--   Metric generators, strong metric generators, graph isometries and extensions (pp. 383, 385, 386)
-- statement:
--   Throughout, graphs are finite, simple, undirected and connected. For a graph $G$ and vertices $x,y$, $\mu_G(x,y)$ denotes the length of a shortest path between $x$ and $y$.
--
--   1. **Metric generator** (p. 383). A vertex $t$ *distinguishes* $x$ and $y$ if $\mu_G(t,x)\ne\mu_G(t,y)$. A set $T\subseteq V(G)$ is a *metric generator* of $G$ if every pair of distinct vertices is distinguished by some element of $T$:
--   $$\forall x\ne y\in V(G)\ \exists t\in T:\ \mu_G(t,x)\ne\mu_G(t,y).$$
--   2. **Strong metric generator** (p. 386). A set $S\subseteq V(G)$ is a *strong metric generator* of the connected graph $G$ if for every pair $x,y\in V(G)$ there is $s\in S$ such that some shortest path from $s$ to $x$ contains $y$, or some shortest path from $s$ to $y$ contains $x$; equivalently,
--   $$\mu_G(s,x)=\mu_G(s,y)+\mu_G(y,x)\quad\text{or}\quad \mu_G(s,y)=\mu_G(s,x)+\mu_G(x,y).$$
--   3. **Isometry** (p. 385). A map $\varphi:V(H)\to V(G)$ is an *isometry from $H$ to $G$* if $\mu_G(\varphi(u),\varphi(v))=\mu_H(u,v)$ for all $u,v\in V(H)$.
--   4. **Isometry on a subset** (pp. 385–387). For $T\subseteq V(H)$, a map $f:T\to V(G)$ is an *isometry $f:(T,\mu_H|_T)\to G$* if $\mu_G(f(s),f(t))=\mu_H(s,t)$ for all $s,t\in T$.
--   5. **Extension** (p. 385). A map $\varphi:V(H)\to V(G)$ *extends* $f:T\to V(G)$ if $\varphi(t)=f(t)$ for every $t\in T$.
--
--   These notions set up the problem of §2: given an isometry on a subset $T$ of the vertices of $H$, decide whether it extends to an isometry of all of $H$ into $G$.
--
--   **Formalization Note** Distances are Mathlib's `SimpleGraph.dist`, valued in $\mathbb N$ and equal to $0$ for unreachable pairs, so every theorem assumes both graphs connected (the paper's standing assumption). The equivalence of "a shortest $s$–$x$ path contains $y$" with $\mu_G(s,x)=\mu_G(s,y)+\mu_G(y,x)$ holds in connected graphs. The page's "$T\in V(G)$" is read as $T\subseteq V(G)$, and "any pair of vertices" in the metric generator definition as any pair of distinct vertices. A map on $T$ is a function on the subtype of $T$, so it has no values off $T$.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 383 (Introduction: metric generator), p. 385 (§2: isometry, extension), p. 386 (§2: strong metric generator)

import Mathlib

namespace MetricGenerators.IsometryExt

/-- **Metric generator** (Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res.
29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, Introduction, p. 383).
A set `T` of vertices of `G` is a metric generator if any two distinct vertices `x ≠ y` are
distinguished by some `t ∈ T`, i.e. `μ_G(t, x) ≠ μ_G(t, y)`.

Formalization Note: `μ_G` is `SimpleGraph.dist`, valued in `ℕ` (it is `0` on unreachable pairs,
so theorems carry `G.Connected`, the paper's standing assumption). The page writes "T ∈ V(G)"
(a typo for `T ⊆ V(G)`) and "any pair of vertices"; the pair is of distinct vertices. -/
def IsMetricGenerator {V : Type*} (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ t ∈ T, G.dist t x ≠ G.dist t y

/-- **Strong metric generator** (ibid., §2, p. 386). A set `S` of vertices of a connected
graph `G` such that for any pair `x, y` (equal or not) there is `s ∈ S` such that some shortest
path from `s` to `x` contains `y`, or some shortest path from `s` to `y` contains `x`.

Formalization Note: in a connected graph, "some shortest `s`–`x` path contains `y`" is
equivalent to `μ_G(s, x) = μ_G(s, y) + μ_G(y, x)`; this distance form is used. -/
def IsStrongMetricGenerator {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x y : V, ∃ s ∈ S,
    G.dist s x = G.dist s y + G.dist y x ∨ G.dist s y = G.dist s x + G.dist x y

/-- **Isometry** between graphs (ibid., §2, p. 385): a map `φ : V(H) → V(G)` with
`μ_H(u, v) = μ_G(φ u, φ v)` for all `u, v`. Not to be confused with a graph homomorphism. -/
def IsIsometry {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG) (φ : VH → VG) : Prop :=
  ∀ u v : VH, G.dist (φ u) (φ v) = H.dist u v

/-- **Isometry `f : (T, μ_H|T) → G`** (ibid., §2, pp. 385–387): a map defined on the vertex set
`T ⊆ V(H)` only (a function on the subtype `↥T`), with `μ_G(f s, f t) = μ_H(s, t)` for all
`s, t ∈ T`. -/
def IsIsometryOn {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG) (T : Finset VH)
    (f : ↥T → VG) : Prop :=
  ∀ s t : ↥T, G.dist (f s) (f t) = H.dist s t

/-- **Extension** (ibid., §2, p. 385): `φ : V(H) → V(G)` extends `f : T → V(G)` if
`φ t = f t` for every `t ∈ T`. -/
def Extends {VH VG : Type*} (T : Finset VH) (f : ↥T → VG) (φ : VH → VG) : Prop :=
  ∀ t : ↥T, φ t = f t

end MetricGenerators.IsometryExt


