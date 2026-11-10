-- Prove2me | Definitions.Def_FreeReplExchange_m3Select
-- name    : FreeReplExchange_m3Select
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:17:30.333832+00:00
-- url     : https://prove2.me/theorems/51c977f9-305b-452c-b3c5-95ce92992e38
-- title:
--   Exchange graph (15), gains (17), the objective $\Phi$ (18) and M3's matching selection
-- statement:
--   For an allocation $x\ge x^{(0)}$ and participating set $P$, the **exchange graph** $G(x,P)$ has the empty slots $(i,s)$, $i\in P$, $x_{i,s}=0$, as vertices and the edges
--   $$\{(i,s),(j,r)\}:\ i,j\in P,\ i<j,\ x_{i,s}=x_{j,r}=0,\ x^{(0)}_{i,r}=x^{(0)}_{j,s}=1,\ (U_i)_{i,s}+(U_i)_{j,r}\ge0,\ (U_j)_{j,r}+(U_j)_{i,s}\ge0 ;$$
--   the edge $e=\{(i,s),(j,r)\}$ represents the exchange $p(e)=((i,r),(j,s))$. A **matching** is a set of edges with pairwise disjoint endpoints. The **total immediate gain** of an edge is
--   $$g(e)=(U_i)_{i,s}+(U_i)_{j,r}+(U_j)_{j,r}+(U_j)_{i,s},\qquad g(\mu)=\sum_{e\in\mu}g(e).$$
--   For a total order $e_1\prec\dots\prec e_L$ on all potential exchanges, the **tie score** is $T(\mu)=\sum_{\ell:e_\ell\in\mu}2^{L-\ell}$, and M3 lexicographically maximizes
--   $$\Phi(\mu)=\bigl(|\mu|,\ g(\mu),\ T(\mu)\bigr)$$
--   over the matchings of the current graph. A **two-objective rule** is any selection rule that picks a matching lexicographically optimal for $(|\mu|,g(\mu))$, with any resolution of the remaining ties. The module also defines the degree of a slot and the maximum degree $\Delta$ of a graph.
--
--   These are the objects of M3's round rule and of the IR, NIC and running-time analyses.
--
--   **Formalization Note** Edges are identified with the exchanges they represent; with $i<j$ this is a bijection. The total order is an injective rank $rk$ (smaller rank first) and $\ell-1$ is the number of exchanges of smaller rank. M3's selection is a $\Phi$-maximizing matching, chosen by `Classical.choose`; for an injective rank it is the unique one. `slotGraph` turns a set of exchanges into a simple graph on slots, for the components in Lemma 1.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), §4.1, p.31 (PDF p.33), eq. (15); §4.2, pp.32–33 (PDF pp.34–35), eqs. (16)–(18)

import Mathlib
import Definitions.Def_FreeReplExchange_util
import Definitions.Def_FreeReplExchange_Exchange

namespace FreeReplExchange

open Classical in
/-- The edge set `E(x, P)` of the exchange graph (15), Yang–Kandasamy, *Pairwise Exchanges of
Freely Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256
3ae07967…), p.31 (PDF p.33): the exchanges `p(e) = ((i, r), (j, s))` with `i, j ∈ P`, `i < j`,
`x_{i,s} = x_{j,r} = 0`, `x^(0)_{i,r} = x^(0)_{j,s} = 1`, `(U_i)_{i,s} + (U_i)_{j,r} ≥ 0` and
`(U_j)_{j,r} + (U_j)_{i,s} ≥ 0`.

**Formalization Note.** An edge `e = {(i, s), (j, r)}` of (15) is identified with the exchange
`p(e) = ((i, r), (j, s))` it represents; its endpoints are the receiving slots `recv p`. With
`i < j` this identification is a bijection, and the vertex set `V(x, P)` is the set of empty slots
of participants. -/
noncomputable def edges {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (P : Finset A) (x : A → Fin m → Bool) :
    Finset (Exchange A m) :=
  Finset.univ.filter fun p =>
    p.i ∈ P ∧ p.j ∈ P ∧ p.i < p.j ∧ x p.i p.s = false ∧ x p.j p.r = false ∧
      x0 p.i p.r = true ∧ x0 p.j p.s = true ∧
      0 ≤ U p.i p.i p.s + U p.i p.j p.r ∧ 0 ≤ U p.j p.j p.r + U p.j p.i p.s

/-- The total immediate gain (17), p.32: for `e = {(i, s), (j, r)}`,
`g(e) = (U_i)_{i,s} + (U_i)_{j,r} + (U_j)_{j,r} + (U_j)_{i,s}`. -/
def gain {A : Type*} {m : ℕ} (U : A → A → Fin m → ℝ) (p : Exchange A m) : ℝ :=
  U p.i p.i p.s + U p.i p.j p.r + U p.j p.j p.r + U p.j p.i p.s

/-- `g(μ) = Σ_{e∈μ} g(e)`, p.32. -/
def gSum {A : Type*} {m : ℕ} (U : A → A → Fin m → ℝ) (μ : Finset (Exchange A m)) : ℝ :=
  ∑ e ∈ μ, gain U e

open Classical in
/-- The matchings of a graph with edge set `E`: the subsets of `E` whose edges have pairwise
disjoint endpoints (receiving slots). -/
noncomputable def matchingsOf {A : Type*} [DecidableEq A] {m : ℕ} (E : Finset (Exchange A m)) :
    Finset (Finset (Exchange A m)) :=
  E.powerset.filter RecvDisjoint

open Classical in
/-- The 0-based position of `e` in the global order `e_1 ≺ ⋯ ≺ e_L` given by a rank `rk`
(smaller rank first): `ℓ − 1` when `e = e_ℓ`. -/
noncomputable def pos {A : Type*} [Fintype A] {m : ℕ} (rk : Exchange A m → ℕ)
    (e : Exchange A m) : ℕ :=
  (Finset.univ.filter fun e' => rk e' < rk e).card

/-- The additive tie score of (18), p.33: `T(μ) = Σ_{ℓ : e_ℓ ∈ μ} 2^{L−ℓ}`, `L` the number of
potential exchanges.

**Formalization Note.** The total order `e_1 ≺ ⋯ ≺ e_L` "on all potential exchanges independently
of participation and history" (p.32) is given by an injective rank `rk : Exchange A m → ℕ`, smaller
rank first; every total order on the finite type of exchanges arises this way. With `ℓ = pos + 1`,
`2^{L−ℓ} = 2^{L−1−pos}`. -/
noncomputable def tieScore {A : Type*} [Fintype A] {m : ℕ} (rk : Exchange A m → ℕ)
    (μ : Finset (Exchange A m)) : ℕ :=
  ∑ e ∈ μ, 2 ^ (Fintype.card (Exchange A m) - 1 - pos rk e)

/-- The objective (18), p.33: `Φ(μ) = (|μ|, g(μ), T(μ))`, compared lexicographically. -/
noncomputable def phi {A : Type*} [Fintype A] {m : ℕ} (U : A → A → Fin m → ℝ)
    (rk : Exchange A m → ℕ) (μ : Finset (Exchange A m)) : Lex (ℕ × Lex (ℝ × ℕ)) :=
  toLex (μ.card, toLex (gSum U μ, tieScore rk μ))

/-- `μ` is a matching of the graph with edge set `E` that maximizes `Φ` lexicographically. -/
def IsPhiMax {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (U : A → A → Fin m → ℝ)
    (rk : Exchange A m → ℕ) (E μ : Finset (Exchange A m)) : Prop :=
  μ ∈ matchingsOf E ∧ ∀ ν ∈ matchingsOf E, phi U rk ν ≤ phi U rk μ

open Classical in
/-- Step 2 of M3, §4.3, p.33: "Select the unique matching `μ_t` maximizing (18) in `G_t`".

**Formalization Note.** Defined as a `Φ`-maximizing matching of `E` (one exists: the matchings
form a finite nonempty family, `∅` among them). For an injective rank distinct edge sets have
distinct tie scores, so the maximizer is unique (p.33) and the choice is canonical. -/
noncomputable def m3Select {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (U : A → A → Fin m → ℝ) (rk : Exchange A m → ℕ) (E : Finset (Exchange A m)) :
    Finset (Exchange A m) :=
  if h : ∃ μ, IsPhiMax U rk E μ then Classical.choose h else ∅

/-- A selection rule (possibly depending on the participating set and the history) that picks,
in every graph with edge set `E`, a matching that is lexicographically optimal for the first two
objectives `(|μ|, g(μ))` of (18), with any resolution of the remaining ties (p.33: "any
tie-breaking rule among matchings that optimize the first two objectives"). -/
def IsTwoObjRule {A : Type*} [DecidableEq A] {m : ℕ} (U : A → A → Fin m → ℝ)
    {H : Type*} (sel : Finset A → H → Finset (Exchange A m) → Finset (Exchange A m)) : Prop :=
  ∀ P h E, sel P h E ∈ matchingsOf E ∧
    ∀ ν ∈ matchingsOf E, toLex (ν.card, gSum U ν) ≤ toLex ((sel P h E).card, gSum U (sel P h E))

/-- The edge `{(i, s), (j, r)}` of slots that represents the exchange `p = ((i, r), (j, s))`. -/
def slotEdge {A : Type*} {m : ℕ} (p : Exchange A m) : Sym2 (A × Fin m) :=
  s((p.i, p.s), (p.j, p.r))

/-- The simple graph on slots whose edges are the slot edges of the exchanges in `S`
(used for the components of `μ0 △ μ1` in Lemma 1). -/
def slotGraph {A : Type*} {m : ℕ} (S : Finset (Exchange A m)) : SimpleGraph (A × Fin m) :=
  SimpleGraph.fromEdgeSet {e | ∃ p ∈ S, slotEdge p = e}

open Classical in
/-- The degree of the slot `v` in the graph with edge set `E`: the number of edges having `v` as
an endpoint. -/
noncomputable def slotDeg {A : Type*} [DecidableEq A] {m : ℕ} (E : Finset (Exchange A m))
    (v : A × Fin m) : ℕ :=
  (E.filter fun p => v ∈ recv p).card

/-- The maximum degree `∆` of the graph with edge set `E`. -/
noncomputable def maxDeg {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (E : Finset (Exchange A m)) : ℕ :=
  Finset.univ.sup (slotDeg E)

end FreeReplExchange


