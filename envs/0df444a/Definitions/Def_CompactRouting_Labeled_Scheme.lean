-- Prove2me | Definitions.Def_CompactRouting_Labeled_Scheme
-- name    : CompactRouting_Labeled_Scheme
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:05:31.266554+00:00
-- url     : https://prove2.me/theorems/fdf3ed96-15f5-41ac-8a76-272bf2c10907
-- title:
--   Labeled routing schemes with randomized source, fixed ports and expected stretch (§1, §2)
-- statement:
--   A **routing instance** is a weighted undirected graph $G$ on the vertices $\{0,\dots,n-1\}$ (vertex $x$ has identifier $\mathrm{id}(x)=x+1$) together with a **port numbering**: at every vertex $x$ the $\deg(x)$ edges at $x$ are numbered $1,\dots,\deg(x)$ by an arbitrary bijection, fixed in advance (the fixed-port model). The instances of the main theorem are **valid for the exponent $a$**: $G$ is connected and simple (no loops, no parallel edges) and every edge weight is an integer in $[1,n^a]$.
--
--   A **labeled routing scheme with randomized source** consists of
--   - a deterministic **preprocessing** that maps the whole instance to a routing table $RT(x)$ and a label $L(x)$ for every vertex, both bit strings;
--   - a **source rule** that maps $(RT(u),L(v))$ to a finitely supported probability distribution with rational masses on pairs (first port, header);
--   - a deterministic **forwarding rule** that maps $(RT(x),L(v),h)$, for the current vertex $x$ and the header $h$, to a port and a new header.
--
--   The source and forwarding rules are fixed functions of bit strings: they do not see the graph or the port numbering. For an outcome $o=(q_0,h_0)$ of the source's coins the message leaves $u$ through port $q_0$ with header $h_0$; at every later vertex $x$ the forwarding rule chooses the next port and header. The walk stops at its **first arrival** at $v$; the message is **delivered** if this happens after finitely many hops, and $\hat d(u,v)$ is the sum of the weights of the traversed edges up to that arrival (edges counted with repetition). The size of a table, label or header is its length in bits. The **expected length** is
--   $$\mathbb E[\hat d(u,v)]=\sum_{o}\Pr[o]\,\hat d_o(u,v),$$
--   the expectation over the source's coins only; the scheme has **$\alpha$-expected stretch** if $\mathbb E[\hat d(u,v)]\le\alpha\, d(u,v)$ for every $u,v$.
--
--   **Formalization Note.** The graph is the published edge list `TZLevelsADO.Graph`; an oriented edge leaving $x$ is a pair (edge, orientation) whose tail is $x$, and `port x` is a bijection from these to `Fin (deg x)`, port $q\in\{1,\dots,\deg x\}$ being the edge numbered $q-1$. `state t` is the state before hop $t$ (vertex, port, header), or `none` after an invalid port. `walkLength` is $0$ for an undelivered outcome (never used: delivery is required). `HeadersBounded` bounds every header carried on a hop before the first arrival.
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 2 (§1, routing model and expected stretch), p. 5 (§2, graphs, identifiers, fixed ports, fn. 5), p. 14 (fn. 6)

import Mathlib
import Definitions.Def_TZLevelsADO_Graph

/-!
# Labeled routing schemes with a randomized source, fixed ports and expected stretch

Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), §1 p. 2 (the routing model, expected
stretch), §2 p. 5 (graphs, identifiers, fixed ports, footnote 5), p. 14 footnote 6.

Conventions.
* A graph is the published edge-list graph `TZLevelsADO.Graph` on `Fin n` with real weights;
  `IsSimple` excludes loops and parallel edges, `IntWeights G a` asks for integer weights in
  `[1, n^a]` (footnote 5). The identifier of vertex `x : Fin n` is `x + 1`.
* Ports: at every vertex `x` the oriented edges leaving `x` are numbered by a bijection with
  `Fin (deg x)`; port `q ∈ {1, …, deg x}` is the oriented edge numbered `q - 1`. An `Instance`
  is a graph together with an arbitrary port numbering.
* A scheme is a deterministic preprocessing (`table`, `label`: functions of the whole instance,
  bit strings), a randomized source rule `src` (from the source's table and the destination's
  label to a finitely supported distribution with rational masses on pairs
  (first port, header)) and a deterministic forwarding rule `fwd` (from the current vertex's
  table, the destination's label and the header to a port and a new header). `src` and `fwd`
  do not see the instance.
* The walk starts at the source and stops at its first arrival at the destination; `walkLength`
  is the sum of the weights of the traversed edges up to that arrival.
-/

namespace CompactRouting.Labeled

open TZLevelsADO

/-- §2, p. 5: the graph is simple: no loops and no two edges with the same pair of endpoints. -/
def IsSimple (G : Graph) : Prop :=
  (∀ e, G.src e ≠ G.dst e) ∧
    ∀ e e', e ≠ e' →
      ¬ ((G.src e = G.src e' ∧ G.dst e = G.dst e') ∨ (G.src e = G.dst e' ∧ G.dst e = G.src e'))

/-- Footnote 5, p. 5: every edge weight is an integer in `[1, n^a]`. -/
def IntWeights (G : Graph) (a : ℕ) : Prop :=
  ∀ e, ∃ z : ℕ, 1 ≤ z ∧ z ≤ G.n ^ a ∧ G.wt e = (z : ℝ)

/-- The oriented edges leaving the vertex `x`. -/
abbrev OutEdge (G : Graph) (x : Fin G.n) : Type :=
  {s : Fin G.m × Bool // G.tail s = x}

/-- The degree of `x`: the number of oriented edges leaving `x`. -/
def deg (G : Graph) (x : Fin G.n) : ℕ :=
  Fintype.card (OutEdge G x)

/-- §2, p. 5 (fixed-port model): a graph together with a numbering of the edges at every
vertex; the numbering is arbitrary and fixed in advance. -/
structure Instance where
  /-- the graph -/
  G : Graph
  /-- the port numbering at every vertex (port `q` is the edge numbered `q - 1`) -/
  port : ∀ x : Fin G.n, OutEdge G x ≃ Fin (deg G x)

/-- The oriented edge behind port `q` of vertex `x`, if `1 ≤ q ≤ deg x`. -/
def Instance.portEdge (I : Instance) (x : Fin I.G.n) (q : ℕ) : Option (Fin I.G.m × Bool) :=
  if h : 1 ≤ q ∧ q ≤ deg I.G x then
    some ((I.port x).symm ⟨q - 1, by omega⟩).1
  else none

/-- The instances of Theorem 1 for the weight exponent `a`: a connected simple graph with
integer weights in `[1, n^a]` (§2, p. 5 and footnote 5), with any port numbering. -/
def Instance.Valid (I : Instance) (a : ℕ) : Prop :=
  I.G.Connected ∧ IsSimple I.G ∧ IntWeights I.G a

/-- A finitely supported probability distribution with rational masses (footnote 6, p. 14). -/
structure RatDist (α : Type) where
  /-- the mass of every outcome -/
  mass : α →₀ ℚ
  /-- masses are nonnegative -/
  nonneg : ∀ x, 0 ≤ mass x
  /-- masses sum to one -/
  total : (mass.sum fun _ q => q) = 1

/-- §1, p. 2: a labeled routing scheme whose source flips coins. -/
structure Scheme where
  /-- preprocessing: the routing table `RT(x)` of every vertex, a bit string -/
  table : (I : Instance) → Fin I.G.n → List Bool
  /-- preprocessing: the label `L(x)` of every vertex, a bit string -/
  label : (I : Instance) → Fin I.G.n → List Bool
  /-- the source rule: `(RT(u), L(v))` ↦ distribution of (first port, header) -/
  src : List Bool → List Bool → RatDist (ℕ × List Bool)
  /-- the forwarding rule: `(RT(x), L(v), header)` ↦ (port, new header) -/
  fwd : List Bool → List Bool → List Bool → ℕ × List Bool

/-- The routing walk from `u` towards `v` for the source outcome `o = (q₀, h₀)`:
`S.state I u v o t` is the state before hop `t`, namely `some (x_t, q_t, h_t)` with the current
vertex `x_t`, the port `q_t` it forwards to and the header `h_t` attached to that hop, or `none`
once an invalid port has been used. At every vertex after the source the forwarding rule
chooses the next port and header. -/
def Scheme.state (S : Scheme) (I : Instance) (u v : Fin I.G.n) (o : ℕ × List Bool) :
    ℕ → Option (Fin I.G.n × ℕ × List Bool)
  | 0 => some (u, o.1, o.2)
  | t + 1 => (S.state I u v o t).bind fun st =>
      (I.portEdge st.1 st.2.1).map fun s =>
        (I.G.head s, (S.fwd (S.table I (I.G.head s)) (S.label I v) st.2.2).1,
          (S.fwd (S.table I (I.G.head s)) (S.label I v) st.2.2).2)

/-- The walk is at the destination `v` before hop `t`. -/
def Scheme.ArrivesAt (S : Scheme) (I : Instance) (u v : Fin I.G.n) (o : ℕ × List Bool)
    (t : ℕ) : Prop :=
  ∃ st, S.state I u v o t = some st ∧ st.1 = v

/-- The message is delivered: the walk reaches `v` after finitely many hops. -/
def Scheme.Delivered (S : Scheme) (I : Instance) (u v : Fin I.G.n) (o : ℕ × List Bool) :
    Prop :=
  ∃ t, S.ArrivesAt I u v o t

/-- The weight of hop `t` (`0` if hop `t` does not exist). -/
noncomputable def Scheme.hopWeight (S : Scheme) (I : Instance) (u v : Fin I.G.n)
    (o : ℕ × List Bool) (t : ℕ) : ℝ :=
  ((S.state I u v o t).bind fun st => I.portEdge st.1 st.2.1).elim 0 fun s => I.G.wt s.1

/-- `d̂(u, v)` for the outcome `o`: the weighted length of the walk up to its first arrival
at `v` (edges counted with repetition). It is only used for delivered outcomes. -/
noncomputable def Scheme.walkLength (S : Scheme) (I : Instance) (u v : Fin I.G.n)
    (o : ℕ × List Bool) : ℝ := by
  classical
  exact if h : S.Delivered I u v o then
    ∑ t ∈ Finset.range (Nat.find h), S.hopWeight I u v o t
  else 0

/-- Every header attached to a hop before the first arrival at `v` has at most `b` bits. -/
def Scheme.HeadersBounded (S : Scheme) (I : Instance) (u v : Fin I.G.n) (o : ℕ × List Bool)
    (b : ℝ) : Prop :=
  ∀ t, (∀ t' ≤ t, ¬ S.ArrivesAt I u v o t') →
    ∀ st, S.state I u v o t = some st → ((st.2.2.length : ℕ) : ℝ) ≤ b

/-- The outcomes the source chooses with positive probability. -/
def Scheme.srcSupport (S : Scheme) (I : Instance) (u v : Fin I.G.n) : Finset (ℕ × List Bool) :=
  (S.src (S.table I u) (S.label I v)).mass.support

/-- `E[d̂(u, v)]`: the expected walk length over the source's coins. -/
noncomputable def Scheme.expectedLength (S : Scheme) (I : Instance) (u v : Fin I.G.n) : ℝ :=
  ∑ o ∈ S.srcSupport I u v,
    ((S.src (S.table I u) (S.label I v)).mass o : ℝ) * S.walkLength I u v o

end CompactRouting.Labeled


