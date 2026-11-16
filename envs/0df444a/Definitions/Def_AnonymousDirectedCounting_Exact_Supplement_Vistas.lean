-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Vistas
-- name    : AnonymousDirectedCounting_Exact_Supplement_Vistas
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:53.671951+00:00
-- url     : https://prove2.me/theorems/4c6248e9-c776-4f94-87ea-4ddef6d104f8
-- title:
--   Explicit binary vistas, order spectra, AtMostOneVista, the fixed-order language, network-prefix inputs and SomeAgentKnows
-- statement:
--   These objects carry the network-wise decision problems of Section 4 and Appendix E, on top of the published network model and history trees of the mission.
--
--   1. **Explicit vistas.** An explicit vista lists node ids for its levels $L_0,\dots,L_t$, a leader or nonleader status for each level-0 node, the parent and outdegree label $d_r(v)$ of each node $v$ of a level $r\ge1$, and every positive red multiplicity $\mu_r(u,v)$ with $u\in L_{r-1}$; unlisted multiplicities are zero, and the root at level $-1$ is implicit. It is **well formed** when the levels are listed exactly once with one bottom node at level $t$, every level-0 node has exactly one status and each status occurs at most once, every later node has a parent one level up, red entries are positive, listed once, and join consecutive levels, children of a common parent have distinct signatures $(d_r(v),(\mu_r(u,v))_u)$, and every listed node is reached from the bottom by following parents and positive red edges backward. Well-formedness is syntax only; it does not assert that a network realizes the vista. A table decodes to the published vista value (equal values are exactly isomorphic vistas).
--   2. **Binary inputs.** Every number (ids, labels, multiplicities, the depth, the leader count $\ell$) is written in a self-delimiting binary code; $s$ denotes the length of the encoding of $\langle\mathcal V,\ell\rangle$.
--   3. **Order spectrum.** A realization of $\mathcal V$ with $\ell$ leaders is a network on $N$ agents with $\ell$ leaders, strongly connected in every round, in which some agent's round-$t$ vista equals $\mathcal V$; the observer need not be a leader. $\operatorname{Spec}_\ell(\mathcal V)$ is the set of orders $N$ of all realizations; it is empty for a malformed table or $\ell=0$.
--   4. **AtMostOneVista** is the set of binary strings $w$ such that every reading of $w$ as $\langle\mathcal V,\ell\rangle$ has $|\operatorname{Spec}_\ell(\mathcal V)|\le1$; strings encoding no input, and malformed inputs, are yes-instances. The **fixed-order language** consists of the encodings of $\langle\mathcal V,\ell,N\rangle$ with $N\in\operatorname{Spec}_\ell(\mathcal V)$.
--   5. **Size parameters.** $\nu=\sum_{r=0}^t|L_r|$; $M$ is the largest of $\ell$, the outdegree labels and the red multiplicities of $\mathcal V$; $K=(1+\nu M)^t$. The dense full-prefix size of a network adds, over the levels $0,\dots,t$ of its full history tree, one unit per node, the bits of its anonymity and outdegree label, and one unit plus the bits of each entry of its row of incoming red multiplicities from the previous full level.
--   6. **Network prefixes.** An explicit prefix gives its order $n$, its last round $t$, one leader bit for every agent, and the positive arc multiplicities $e_r(x,y)$ for $1\le r\le t$ in binary. It is well formed when it has one bit per agent and at least one leader, entries are positive, listed once and refer to listed agents and rounds, and every round graph is strongly connected. **SomeAgentKnows** is the set of encodings of well-formed prefixes in which some agent's round-$t$ vista has a singleton order spectrum for the input's leader count; all other strings are no-instances.
--
--   **Formalization Note** Realizations are networks strongly connected in every round; a finite prefix strongly connected through round $t$ extends to one by repeating any strongly connected round, and later rounds do not affect round-$t$ vistas. Rounds after $t$ of a listed prefix carry no arcs.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 24 (PDF p. 26), Appendix E.1–E.2; printed pp. 12, 28 (PDF pp. 14, 30), Section 4 and Appendix E.5

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree
import Definitions.Def_AnonymousDirectedCounting_Exact_LocalCost

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact.Supplement

open AnonymousDirectedCounting.Exact
open scoped Classical

noncomputable section

/-- An explicit vista, Appendix E.1 (printed p. 24, PDF p. 26). Node ids are natural numbers and
index the input only. `levels` lists `L_0, …, L_t` (`t = depth`); `status` gives each level-0 node
its leader status; `parents` lists `(v, parent of v, outdegree label of v)` for every node of a level
`r ≥ 1`; `reds` lists `(u, v, μ_r(u, v))` for every positive red multiplicity, unlisted
multiplicities being zero. The root (level `-1`) is implicit. -/
structure VistaTable where
  depth : ℕ
  levels : List (List ℕ)
  status : List (ℕ × Bool)
  parents : List (ℕ × ℕ × ℕ)
  reds : List (ℕ × ℕ × ℕ)
  bottom : ℕ

namespace VistaTable

/-- The node ids of level `r` (empty beyond the table). -/
def level (T : VistaTable) (r : ℕ) : List ℕ := T.levels.getD r []

/-- The listed leader status of a level-0 node. -/
def statusOf (T : VistaTable) (i : ℕ) : Bool := (T.status.lookup i).getD false

/-- The listed parent of a node of level `r ≥ 1`. -/
def parentOf (T : VistaTable) (i : ℕ) : ℕ := ((T.parents.lookup i).map Prod.fst).getD 0

/-- The listed outdegree label of a node of level `r ≥ 1`. -/
def degreeOf (T : VistaTable) (i : ℕ) : ℕ := ((T.parents.lookup i).map Prod.snd).getD 0

/-- The red multiplicity `μ(u, v)`: the listed value, zero when unlisted. -/
def mult (T : VistaTable) (u v : ℕ) : ℕ :=
  ((T.reds.find? (fun e => decide (e.1 = u ∧ e.2.1 = v))).map (fun e => e.2.2)).getD 0

/-- One backward step from `x`: to its parent, or to a tail of a positive red edge into `x`. -/
def BackStep (T : VistaTable) (x y : ℕ) : Prop :=
  (x ∈ (T.levels.drop 1).flatten ∧ y = T.parentOf x) ∨ 0 < T.mult y x

/-- The syntax of an explicit vista (printed p. 24, PDF p. 26): one list per level `0, …, t`;
distinct ids; exactly one bottom node at level `t`; a status for exactly the level-0 nodes, with at
most one node of each status; a parent and label for exactly the nodes of levels `≥ 1`, the parent
lying one level up; positive red multiplicities, listed once each, between consecutive levels;
distinct signatures `(d_r(v), (μ_r(u, v))_u)` for children of the same parent; and exactly the nodes
reached from the bottom by following parents and positive red edges backward. It does not assert
that a network realizes the vista. -/
def WellFormed (T : VistaTable) : Prop :=
  T.levels.length = T.depth + 1 ∧
  T.levels.flatten.Nodup ∧
  T.level T.depth = [T.bottom] ∧
  (T.status.map Prod.fst).Perm (T.level 0) ∧
  (T.status.filter (fun p => p.2)).length ≤ 1 ∧
  (T.status.filter (fun p => !p.2)).length ≤ 1 ∧
  (T.parents.map Prod.fst).Perm (T.levels.drop 1).flatten ∧
  (∀ r : ℕ, ∀ v ∈ T.level (r + 1), T.parentOf v ∈ T.level r) ∧
  (T.reds.map (fun e => (e.1, e.2.1))).Nodup ∧
  (∀ e ∈ T.reds, 0 < e.2.2 ∧ ∃ r : ℕ, e.1 ∈ T.level r ∧ e.2.1 ∈ T.level (r + 1)) ∧
  (∀ r : ℕ, ∀ v ∈ T.level (r + 1), ∀ w ∈ T.level (r + 1), v ≠ w →
    T.parentOf v = T.parentOf w →
      (T.degreeOf v, fun u => T.mult u v) ≠ (T.degreeOf w, fun u => T.mult u w)) ∧
  (∀ i ∈ T.levels.flatten, Relation.ReflTransGen T.BackStep T.bottom i)

/-- Decoding of node `i` read at level `r` into the published `History r` (an unfolded vista):
status at level 0; parent, outdegree label and the multiset of red tails at later levels. -/
def decodeNode (T : VistaTable) : (r : ℕ) → ℕ → History r
  | 0, i => (T.statusOf i : Bool)
  | r + 1, i =>
    ((decodeNode T r (T.parentOf i), T.degreeOf i,
      ((T.level r).map (fun u => Multiset.replicate (T.mult u i) (decodeNode T r u))).sum) :
        History r × ℕ × Multiset (History r))

/-- The decoded vista: its bottom node at level `t`. -/
def decode (T : VistaTable) : History T.depth := T.decodeNode T.depth T.bottom

end VistaTable

/-- Self-delimiting binary list of naturals: its length, then each entry. -/
def encodeNatList (l : List ℕ) : List Bool :=
  encodeNat l.length ++ l.flatMap encodeNat

/-- The binary encoding of an explicit vista; every number is written in binary. -/
def encodeVistaTable (T : VistaTable) : List Bool :=
  encodeNat T.depth ++
  encodeNat T.levels.length ++ T.levels.flatMap encodeNatList ++
  encodeNat T.status.length ++ T.status.flatMap (fun p => encodeNat p.1 ++ [p.2]) ++
  encodeNat T.parents.length ++
    T.parents.flatMap (fun p => encodeNat p.1 ++ encodeNat p.2.1 ++ encodeNat p.2.2) ++
  encodeNat T.reds.length ++
    T.reds.flatMap (fun e => encodeNat e.1 ++ encodeNat e.2.1 ++ encodeNat e.2.2) ++
  encodeNat T.bottom

/-- The input `⟨𝒱, ℓ⟩`: the vista, then the leader count in binary. Its length is `s`. -/
def encodeVistaInput (T : VistaTable) (ell : ℕ) : List Bool :=
  encodeVistaTable T ++ encodeNat ell

/-- Realizations of the vista value `v : History t` with `ell` leaders (printed p. 24, PDF p. 26):
the orders `N` of networks with `ell` leaders, strongly connected in every round, in which some
agent's round-`t` history is `v`. Equal values of `History t` are exactly isomorphic vistas. -/
def vistaSpec (ell t : ℕ) (v : History t) : Set ℕ :=
  {N | ∃ G : NetworkModel N, Admissible G ∧ G.leaders.card = ell ∧
    ∃ x : Fin N, history G t x = v}

/-- `Spec_ℓ(𝒱)` for an explicit table: empty for a malformed table or a nonpositive leader count,
otherwise the spectrum of the decoded vista. -/
def tableSpec (ell : ℕ) (T : VistaTable) : Set ℕ :=
  {N | T.WellFormed ∧ 0 < ell ∧ N ∈ vistaSpec ell T.depth T.decode}

/-- AtMostOneVista (printed pp. 12, 24): binary strings all of whose readings as `⟨𝒱, ℓ⟩` have
spectrum of cardinality at most one. Strings that encode no input, and malformed inputs, have empty
spectrum and are yes-instances. -/
def AtMostOneVista : Language Bool :=
  {w | ∀ (T : VistaTable) (ell : ℕ), encodeVistaInput T ell = w → (tableSpec ell T).Subsingleton}

/-- The fixed-order language of Lemma 13: `⟨𝒱, ℓ, N⟩` with `N ∈ Spec_ℓ(𝒱)`, `N` in binary. -/
def FixedOrderVista : Language Bool :=
  {w | ∃ (T : VistaTable) (ell N : ℕ), encodeVistaInput T ell ++ encodeNat N = w ∧
    N ∈ tableSpec ell T}

/-- `ν = ∑_{r=0}^t |L_r|`, the number of nonroot nodes of the vista. -/
def vistaNodeCount (t : ℕ) (v : History t) : ℕ :=
  ∑ r ∈ Finset.range (t + 1), (vistaLevel t v r).card

/-- The largest numerical label carried by a node of level `r + 1`: its outdegree label and the
multiplicities of its red edges. -/
def nodeMaxLabel {r : ℕ} (w : History (r + 1)) : ℕ :=
  max (outLabel w) ((redTails w).toFinset.sup (fun u => redMult u w))

/-- `M`: the largest of `ℓ`, the outdegree labels and the red multiplicities of the vista. -/
def vistaMaxLabel (ell t : ℕ) (v : History t) : ℕ :=
  max ell ((Finset.range t).sup (fun r => (vistaLevel t v (r + 1)).sup nodeMaxLabel))

/-- `K = (1 + νM)^t` (printed p. 24, PDF p. 26). -/
def influenceBound (ell t : ℕ) (v : History t) : ℕ :=
  (1 + vistaNodeCount t v * vistaMaxLabel ell t v) ^ t

/-- The size bound `K + ℓ + 2` of Lemma 9, for the decoded table. -/
def smallOrderBound (ell : ℕ) (T : VistaTable) : ℕ :=
  influenceBound ell T.depth T.decode + ell + 2

/-- The length of a dense description of the full history-tree prefix `T_0, …, T_t` of `G`: for
every node one slot, the bits of its anonymity, of its outdegree label, and a row holding all its
incoming red multiplicities from the previous full level, each with its bits. -/
def fullPrefixSize {N : ℕ} (G : NetworkModel N) (t : ℕ) : ℕ :=
  (∑ v ∈ historyLevel G 0, (1 + Nat.size (anonymity G 0 v))) +
  ∑ r ∈ Finset.range t, ∑ v ∈ historyLevel G (r + 1),
    (1 + Nat.size (anonymity G (r + 1) v) + Nat.size (outLabel v) +
      ∑ u ∈ historyLevel G r, (1 + Nat.size (redMult u v)))

/-- An explicitly listed network prefix (printed p. 28, PDF p. 30): its order, its last round `t`,
one leader bit per agent, and the list of positive arc multiplicities `(r, x, y, e_r(x, y))`. -/
structure PrefixInput where
  order : ℕ
  rounds : ℕ
  leaderBits : List Bool
  arcs : List (ℕ × ℕ × ℕ × ℕ)

namespace PrefixInput

/-- The listed multiplicity, zero when unlisted. -/
def mult (P : PrefixInput) (r x y : ℕ) : ℕ :=
  ((P.arcs.find? (fun e => decide (e.1 = r ∧ e.2.1 = x ∧ e.2.2.1 = y))).map
    (fun e => e.2.2.2)).getD 0

/-- The listed prefix as a network (no arcs after round `t`; they do not affect round-`t` histories). -/
def toNetwork (P : PrefixInput) : NetworkModel P.order where
  arcs r x y := if r ≤ P.rounds then P.mult r x.val y.val else 0
  leaders := Finset.univ.filter (fun x => P.leaderBits.getD x.val false = true)

/-- Syntax of a network prefix: one leader bit per agent, a nonempty leader set, positive arc
entries listed once each between listed agents in rounds `1, …, t`, and every round graph strongly
connected. -/
def WellFormed (P : PrefixInput) : Prop :=
  P.leaderBits.length = P.order ∧ true ∈ P.leaderBits ∧
  (P.arcs.map (fun e => (e.1, e.2.1, e.2.2.1))).Nodup ∧
  (∀ e ∈ P.arcs, 1 ≤ e.1 ∧ e.1 ≤ P.rounds ∧ e.2.1 < P.order ∧ e.2.2.1 < P.order ∧ 0 < e.2.2.2) ∧
  ∀ r : ℕ, 1 ≤ r → r ≤ P.rounds → StronglyConnected (P.toNetwork.arcs r)

end PrefixInput

/-- The binary encoding of a network prefix: every agent has its own leader bit; multiplicities
are in binary. -/
def encodePrefix (P : PrefixInput) : List Bool :=
  encodeNat P.order ++ encodeNat P.rounds ++ encodeBits P.leaderBits ++
  encodeNat P.arcs.length ++
    P.arcs.flatMap (fun e => encodeNat e.1 ++ encodeNat e.2.1 ++ encodeNat e.2.2.1 ++ encodeNat e.2.2.2)

/-- SomeAgentKnows (printed p. 28, PDF p. 30): well-formed prefixes in which some agent's round-`t`
vista has a singleton order spectrum for the input's leader count. Other strings are no-instances. -/
def SomeAgentKnows : Language Bool :=
  {w | ∃ P : PrefixInput, encodePrefix P = w ∧ P.WellFormed ∧
    ∃ x : Fin P.order, ∃ N : ℕ,
      vistaSpec P.toNetwork.leaders.card P.rounds (history P.toNetwork P.rounds x) = {N}}

end

end AnonymousDirectedCounting.Exact.Supplement


