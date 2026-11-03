-- Prove2me | Definitions.Def_RandomOrderCRS_Policy
-- name    : RandomOrderCRS_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:28.407119+00:00
-- url     : https://prove2.me/theorems/f79189f7-7d91-4b70-bc04-2b5901880c85
-- title:
--   Sequential contention resolution schemes, selection probabilities and selectability
-- statement:
--   Let $G=(V,E)$ be a finite graph and $x$ a fractional matching. Each edge $e$ has an **activeness state** $X_e\sim\mathrm{Ber}(x_e)$, independently. A **sequential contention resolution scheme** knows $G$ and $x$, but not the states. The states are presented one at a time along an ordering of $E$. On learning $X_e$, the scheme decides irrevocably whether to select $e$, and the selected set must be a matching of active edges. An edge is **blocked** if one of its endpoints is already covered by a selected edge.
--
--   A scheme is modelled as a **policy**: a finite type of private random seeds with a probability law, and a decision that depends only on the seed, the past arrivals with their states, the current edge and its state. The **run** of a policy processes the edges along the order, and selects the current edge exactly when it is active, the policy says yes, and it is not blocked. Write $\mathbb P_\sigma[e\text{ selected}]$ for the selection probability on the order $\sigma$, over the seed and over the independent states.
--
--   For a constant $c$, the policy is a **$c$-selectable random-order contention resolution scheme (RCRS)** for $(G,x)$ if
--
--   $$\frac1{|E|!}\sum_{\sigma}\mathbb P_\sigma[e\text{ selected}]\ge c\,x_e\qquad\text{for all }e\in E,$$
--
--   and a **$c$-selectable online contention resolution scheme (OCRS)** for $(G,x)$ if $\mathbb P_\sigma[e\text{ selected}]\ge c\,x_e$ for all orders $\sigma$ and all edges $e$. The second form is the oblivious adversary: the order is fixed knowing the scheme, and it does not react to realizations.
--
--   This is the general class over which the mission's main theorem quantifies. Its causal interface is what makes the guarantee an online one.
--
--   **Formalization Note** An order is a bijection `Fin |E| ≃ E`. The seed is drawn once, independently of the order and the states, so selection probabilities are explicit finite sums. Selecting only active, unblocked edges is enforced by the run, which loses no generality. Finite seeds lose no generality either: a scheme with arbitrary private randomness is a mixture of the finitely many deterministic decision rules. The scheme is a parameter given for $G$ and may be built from $x$.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, §1.1, p.3 (sequential CRS, OCRS, RCRS, c-selectable) and footnote 1, p.3 (oblivious adversary); Definition 1, p.10 (matched, blocked)

import Mathlib

open Finset

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An arrival order of the edges of `G`: position `i` holds the `i`-th arriving edge.

**Formalization Note.** Arrival orders are the bijections from `Fin |E|` to the edges, so there are
`|E|!` of them. -/
abbrev ArrivalOrder (G : SimpleGraph V) [DecidableRel G.Adj] : Type :=
  Fin (Fintype.card G.edgeSet) ≃ G.edgeSet

/-- What a sequential scheme has seen so far: the past arrivals in order, each with its revealed
state. -/
abbrev History (G : SimpleGraph V) : Type := List (G.edgeSet × Bool)

/-- A sequential contention resolution scheme for `G`, arXiv:2209.07520v2, §1.1, p.3: "A sequential
CRS is also passed G and x as input, but initially does not know the edge states (X_e)_{e∈E}.
Instead, an ordering on E is chosen, and the edge states are presented one-by-one to the sequential
CRS using this ordering. Upon learning X_e, it makes an irrevocable decision on whether or not to
select e."

**Formalization Note.** A policy has a finite type `Seed` of private randomness, a normalized
nonnegative law on it, and a decision that sees exactly the seed, the history (past arrivals with
their states), the current edge and the current state. It sees no future edge, no future state, and
not the tail of the order. The seed is drawn once, independently of the order and of the states (see
`selProb`). The policy is passed `G` as a type parameter, and may depend on `x` because `x` is a
parameter of whoever constructs it. Finite seeds lose no generality: a scheme with arbitrary private
randomness is a mixture of the finitely many deterministic decision rules on the finitely many
histories, and that mixture is a finite seed with the same selection probabilities. -/
structure Policy (G : SimpleGraph V) where
  /-- The private randomness of the scheme. -/
  Seed : Type
  /-- The private randomness takes finitely many values. -/
  [seedFintype : Fintype Seed]
  /-- The law of the private randomness. -/
  seedWeight : Seed → ℝ
  seedWeight_nonneg : ∀ ω, 0 ≤ seedWeight ω
  seedWeight_sum : ∑ ω, seedWeight ω = 1
  /-- The decision at the current edge: seed, history, current edge, current state. -/
  decide : Seed → History G → G.edgeSet → Bool → Bool

attribute [instance] Policy.seedFintype

/-- `e` is blocked given the selected set `M`: "an edge e = (u, v) is blocked if either u or v has
been matched by the time e arrives", where `v` is matched if "an edge incident to v that has
already arrived has been selected", arXiv:2209.07520v2, Definition 1, p.10. -/
def Blocked (G : SimpleGraph V) (M : Finset G.edgeSet) (e : G.edgeSet) : Prop :=
  ∃ f ∈ M, ∃ v, v ∈ (f : Sym2 V) ∧ v ∈ (e : Sym2 V)

/-- The state of a run: the edges selected so far and the history revealed so far. -/
structure RunState (G : SimpleGraph V) where
  selected : Finset G.edgeSet
  history : History G

open Classical in
/-- One arrival of a run. The current edge `e` is selected iff it is active, the policy says yes,
and it is not blocked. The state `X e` is then appended to the history.

**Formalization Note.** Selecting only active, unblocked edges is enforced here, so the selected set
is always a matching of active edges (arXiv:2209.07520v2, p.3), and selections are irrevocable
because the set only grows. A scheme that would violate these constraints loses no generality. -/
noncomputable def runStep (G : SimpleGraph V) (π : Policy G) (X : G.edgeSet → Bool) (ω : π.Seed)
    (st : RunState G) (e : G.edgeSet) : RunState G :=
  ⟨if X e = true ∧ π.decide ω st.history e (X e) = true ∧ ¬ Blocked G st.selected e then
      insert e st.selected
    else st.selected,
    st.history ++ [(e, X e)]⟩

/-- The state after the first `k` arrivals of the order `σ`. -/
noncomputable def runPrefix (G : SimpleGraph V) [DecidableRel G.Adj] (π : Policy G)
    (σ : ArrivalOrder G) (X : G.edgeSet → Bool) (ω : π.Seed) (k : ℕ) : RunState G :=
  ((List.ofFn σ).take k).foldl (runStep G π X ω) ⟨∅, []⟩

/-- The set of edges selected by `π` on the order `σ`, the states `X` and the seed `ω`. -/
noncomputable def run (G : SimpleGraph V) [DecidableRel G.Adj] (π : Policy G)
    (σ : ArrivalOrder G) (X : G.edgeSet → Bool) (ω : π.Seed) : Finset G.edgeSet :=
  (runPrefix G π σ X ω (Fintype.card G.edgeSet)).selected

/-- The probability of a realization `X` of the edge states: "each edge e has an activeness state
X_e that realizes to 1 with probability (w.p.) x_e and 0 w.p. 1 − x_e, independent of everything
else", arXiv:2209.07520v2, §1.1, p.3. -/
noncomputable def stateWeight (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (X : G.edgeSet → Bool) : ℝ :=
  ∏ e : G.edgeSet, if X e = true then x e else 1 - x e

open Classical in
/-- The probability that `π` selects `e` when the arrival order is `σ` and the states are
independent `Ber(x_e)`.

**Formalization Note.** This is a finite sum over seeds and over states, of the seed weight times
the product of Bernoulli weights times the indicator of `e ∈ run`. So the seed is independent of the
states and of `σ`. -/
noncomputable def selProb (G : SimpleGraph V) [DecidableRel G.Adj] (π : Policy G) (x : Sym2 V → ℝ)
    (σ : ArrivalOrder G) (e : G.edgeSet) : ℝ :=
  ∑ ω, π.seedWeight ω *
    ∑ X : G.edgeSet → Bool, stateWeight G x X * if e ∈ run G π σ X ω then (1 : ℝ) else 0

/-- `π` is a `c`-selectable random-order contention resolution scheme for `(G, x)`: "selects each
edge e with probability at least c x_e", where the order "is chosen uniformly at random",
arXiv:2209.07520v2, §1.1, p.3.

**Formalization Note.** The uniform order is the average over all `|E|!` orders. The bound is on the
unconditional selection probability, as in the paper's definition of selectability; it covers
`x_e = 0` with no conditioning. -/
def IsRCRSelectable (G : SimpleGraph V) [DecidableRel G.Adj] (π : Policy G) (x : Sym2 V → ℝ)
    (c : ℝ) : Prop :=
  ∀ e : G.edgeSet,
    c * x e ≤ ((Fintype.card G.edgeSet).factorial : ℝ)⁻¹ * ∑ σ : ArrivalOrder G, selProb G π x σ e

/-- `π` is a `c`-selectable online contention resolution scheme for `(G, x)`, where the order "is
chosen by an adversary", arXiv:2209.07520v2, §1.1, p.3, and footnote 1, p.3: "this adversary is
oblivious, in that it fixes the arrival order based on the algorithm and cannot change the order
based on realizations".

**Formalization Note.** The oblivious adversary is the quantifier `∀ σ` after `π`. -/
def IsOCRSelectable (G : SimpleGraph V) [DecidableRel G.Adj] (π : Policy G) (x : Sym2 V → ℝ)
    (c : ℝ) : Prop :=
  ∀ (σ : ArrivalOrder G) (e : G.edgeSet), c * x e ≤ selProb G π x σ e

end RandomOrderCRS


