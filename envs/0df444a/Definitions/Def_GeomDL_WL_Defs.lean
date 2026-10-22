-- Prove2me | Definitions.Def_GeomDL_WL_Defs
-- name    : GeomDL_WL_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:13.666628+00:00
-- url     : https://prove2.me/theorems/0b711dcd-1c18-4bfe-8323-f3f066b5ded6
-- title:
--   §4.1, §5.3, Ch. 7 — neighbourhoods, the local layer (13), message-passing GNNs (35), C₆ and 2K₃, max and mean aggregators
-- statement:
--   This file fixes the objects used in the mission on the expressive power of graph neural networks. Graphs are the finite simple undirected graphs $G = (V, E)$ of the reused definition `WLIdentification`, with node set $V = \{0, \dots, n-1\}$.
--
--   1. **Neighbourhood** (eq. (11), p. 34). For a node $u$, $\mathcal N_u = \{v : (u, v) \in E\}$. Graphs are loopless, so $u \notin \mathcal N_u$.
--   2. **Local layer** (eq. (13), p. 34). Given a shared local function $\phi : F \times \mathrm{Multiset}(F) \to F$ and node features $h : V \to F$, the layer returns at node $u$
--   $$
--   \phi\big(h_u, \{\!\{ h_v : v \in \mathcal N_u \}\!\}\big).
--   $$
--   3. **Message-passing layer** (eq. (35), p. 79). A layer has a message function $\psi : F \times F \to M$, a permutation-invariant aggregator $\bigoplus$, given as a function $\mathrm{Multiset}(M) \to A$, and an update $\phi : F \times A \to F$; it maps $h$ to
--   $$
--   h_u \leftarrow \phi\Big(h_u, \bigoplus_{v \in \mathcal N_u} \psi(h_u, h_v)\Big).
--   $$
--   4. **Message-passing GNN** on featureless graphs: a constant initial feature $c \in F$ (so $h^0_u = c$ for every node of every graph) and layer parameters $(\psi_t, \bigoplus_t, \phi_t)$ for rounds $t = 0, 1, \dots$; $h^{t+1}$ is layer $t$ applied to $h^t$. The parameters are the same for every graph. A $T$-layer GNN uses rounds $0, \dots, T-1$. Its graph-level output after $T$ rounds is $\mathrm{readout}(\{\!\{h^T_u : u \in V\}\!\})$ for a read-out function on multisets of features.
--   5. **The 6-cycle** $C_6$ on $\{0, \dots, 5\}$, with $u \sim v$ iff $v \equiv u \pm 1 \pmod 6$, and **two triangles** $2K_3$ on $\{0,1,2\} \cup \{3,4,5\}$.
--   6. **Maximisation and averaging** of a multiset $S$ of vectors in $\mathbb R^d$: the coordinatewise maximum $\max S$ (with value $\bot$ on the empty multiset) and the mean $\frac{1}{|S|}\sum_{x \in S} x$ (with value $0$ on the empty multiset).
--
--   These are the book's three objects of study in its account of GNN expressivity: the GNN layer, the WL colour refinement it is compared with, and the standard counterexamples.
--
--   **Formalization Note** The aggregator is a function of the multiset of messages, so permutation invariance holds by construction. Message, aggregate and feature types are one type each across all layers; a family with layer-dependent types embeds into this one by taking disjoint unions.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, eqs. (11)–(13), p. 34; §5.3, eq. (35), p. 79; Ch. 7, side-notes p. 120

import Mathlib
import Definitions.Def_WLIdentification

namespace GeomDL.WL

open OAI.WLIdentification

universe uF uM uA

/-- The 1-hop neighbourhood `N_u = {v : (u, v) ∈ E}` of a node `u` (eq. (11), p. 34). The graph is
loopless, so `u ∉ N_u`; this is the same neighbourhood `neighborColor` uses. -/
def nbhd (G : Graph) (u : Fin G.order) : Finset (Fin G.order) :=
  Finset.univ.filter (fun w => G.edge u w = true)

/-- The local permutation-equivariant layer (13) of §4.1, p. 34: a shared local function
`φ(x_u, X_{N_u})` applied to the feature of every node and the multiset of its neighbours' features. -/
def localLayer {F : Type uF} (φ : F → Multiset F → F) (G : Graph) (h : Fin G.order → F) :
    Fin G.order → F :=
  fun u => φ (h u) ((nbhd G u).val.map h)

/-- The parameters of one message-passing GNN layer (35), p. 79: a message function `ψ`, a
permutation-invariant aggregator `⊕`, encoded as a function of the multiset of messages, and an
update function `φ`. The parameters do not depend on the graph. -/
structure MPLayer (F : Type uF) (M : Type uM) (A : Type uA) where
  ψ : F → F → M
  agg : Multiset M → A
  φ : F → A → F

/-- One application of the message-passing layer (35):
`h_u ← φ(h_u, ⊕_{v ∈ N_u} ψ(h_u, h_v))`. -/
def MPLayer.apply {F : Type uF} {M : Type uM} {A : Type uA} (L : MPLayer F M A) (G : Graph)
    (h : Fin G.order → F) : Fin G.order → F :=
  fun u => L.φ (h u) (L.agg ((nbhd G u).val.map (fun v => L.ψ (h u) (h v))))

/-- A message-passing GNN on featureless graphs: a constant initial feature `init` and the layer
parameters `layer t` used at round `t`. A `T`-layer GNN uses the first `T` entries of `layer`. -/
structure GNN (F : Type uF) (M : Type uM) (A : Type uA) where
  init : F
  layer : ℕ → MPLayer F M A

/-- The node features `h^t_u` after `t` rounds on the graph `G`. -/
def GNN.features {F : Type uF} {M : Type uM} {A : Type uA} (N : GNN F M A) (G : Graph) :
    ℕ → Fin G.order → F
  | 0 => fun _ => N.init
  | t + 1 => (N.layer t).apply G (N.features G t)

/-- The graph-level output after `T` rounds: a read-out of the multiset of final node features. -/
def GNN.output {F : Type uF} {M : Type uM} {A : Type uA} {Y : Type*} (N : GNN F M A)
    (readout : Multiset F → Y) (G : Graph) (T : ℕ) : Y :=
  readout (Finset.univ.val.map (N.features G T))

/-- The 6-cycle `C₆` on nodes `0, …, 5`: `u ~ v` iff `v = u ± 1 mod 6`. -/
def cycle6 : Graph where
  order := 6
  edge u v := decide ((u.val + 1) % 6 = v.val ∨ (v.val + 1) % 6 = u.val)
  symmetric := by decide
  loopless := by decide

/-- Two disjoint triangles `2K₃` on nodes `{0,1,2}` and `{3,4,5}`. -/
def twoTriangles : Graph where
  order := 6
  edge u v := decide (u ≠ v ∧ u.val / 3 = v.val / 3)
  symmetric := by decide
  loopless := by decide

/-- The maximisation aggregator: the coordinatewise maximum of a multiset of feature vectors in
`ℝ^d`, valued in `WithBot (Fin d → ℝ)` so that the empty multiset has the value `⊥`. -/
def maxAgg {d : ℕ} (s : Multiset (Fin d → ℝ)) : WithBot (Fin d → ℝ) :=
  (s.map (fun x => (x : WithBot (Fin d → ℝ)))).sup

/-- The averaging aggregator: `(1/|s|) Σ_{x ∈ s} x` (the empty multiset gives `0`). -/
noncomputable def meanAgg {d : ℕ} (s : Multiset (Fin d → ℝ)) : Fin d → ℝ :=
  (s.card : ℝ)⁻¹ • s.sum

end GeomDL.WL


