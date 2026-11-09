-- Prove2me | Definitions.Def_AutomaticSelfReduction_Lifting_Local
-- name    : AutomaticSelfReduction_Lifting_Local
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:49.547651+00:00
-- url     : https://prove2.me/theorems/b349f830-72f5-4b54-8170-12ed84b0ca4c
-- title:
--   The randomized LOCAL model on biregular 2-coloured graphs and the expected error of an algorithm
-- statement:
--   An **instance** is a finite simple $(\Delta,\delta)$-biregular 2-coloured graph $G=(W,B,E)$ with $n=|W|+|B|$ vertices: every edge joins a white and a black node, white nodes have degree $\Delta$ and black nodes degree $\delta$. Its girth is at least $g$ if every cycle has length at least $g$ (acyclic graphs qualify for every $g$).
--
--   **Randomized LOCAL model.** Computation proceeds in synchronous rounds; in each round every node sends a possibly different message of unbounded size to each neighbour and computes without restriction. Nodes have no identifiers. They know $n$, $\Delta$, $\delta$ and their colour. Each node has its own infinite string of independent fair random bits and numbers its incident edges (its ports) itself, uniformly at random and independently of everything else. In addition, all nodes see a common sample from an arbitrary shared probability space $(S,\mu)$, independent of the private randomness. After $t$ rounds the most a node can know is its **full-information state**: after $0$ rounds its own random bits, after $t+1$ rounds its state after $t$ rounds together with, for each port $i$, the neighbour's port number of that edge and the neighbour's state after $t$ rounds.
--
--   A **$T$-round algorithm** $A$ is a single measurable (not necessarily computable) map that takes the shared sample and the $T$-round state of a white node and returns a label for each of its $\Delta$ ports; every white node runs it, and the label of an edge is the one its white endpoint assigns to it. White nodes are active, black nodes passive. A problem whose active side is the degree-$\delta$ side is solved on the same graph with the colours exchanged.
--
--   **Error (Definition 2.9).** For a labelling $f:E\to\Sigma$ and a node $v$ let $c(v)$ be the multiset of labels of its edges. The error of $f$ with respect to $\Pi$ is
--   $$
--   \operatorname{err}(f)=\underbrace{\sum_{v\in W}d\bigl(c(v),C_W\bigr)}_{\text{white error}}+\underbrace{\sum_{v\in B}d\bigl(c(v),C_B\bigr)}_{\text{black error}},
--   $$
--   the number of labels that must be changed around each node to correct its configuration, summed over the nodes. The **expected error** of $A$ on $G$ is the expectation of $\operatorname{err}$ over all random bits, port numberings and the shared sample. An algorithm has white error $0$ on every execution if the multiset of its outputs belongs to $C_W$ for every state and every shared sample.
--
--   **Formalization Note** The graph is a bijection `edge : Fin nW × Fin Δ ≃ Fin nB × Fin δ` between white and black half-edges (indices are only names; the nodes' ports are a uniformly random permutation of them) plus a no-multi-edge condition; `swap` exchanges the colours and `graph` is the underlying simple graph on `Fin nW ⊕ Fin nB`. The private bits use `Measure.infinitePi` of fair coins, so randomness is not restricted to finitely many bits. States are a recursive tower of measurable product spaces; since messages are unbounded, every $T$-round protocol's output is a function of the full-information state. Expectations are lower Lebesgue integrals in $[0,\infty]$, so no integrability side condition is needed; the error is bounded and measurable for every algorithm, so this is the ordinary expectation.
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), §4 LOCAL model, white and black algorithms, computable vs non-computable algorithms, printed pp. 11–12 (PDF pp. 12–13); shared randomness, printed p. 4 (PDF p. 5); Definition 2.9, printed p. 8 (PDF p. 9)

import Definitions.Def_AutomaticSelfReduction_Lifting_Problem

/-!
# The randomized LOCAL model on biregular 2-coloured graphs, and the error of an algorithm

Balliu, d'Amore, Olivetti, STOC 2027 submission #338 (October 2026): §4 "LOCAL model" and
"White and black algorithms", "Computable vs non-computable algorithms" (PDF pp. 12–13,
printed pp. 11–12); shared randomness (PDF p. 5); Definition 2.9 (PDF p. 9).

* `Instance n Δ δ`: a finite simple `(Δ, δ)`-biregular 2-coloured graph with `n` vertices in
  total (`nW` white of degree `Δ`, `nB` black of degree `δ`), given as a bijection between white
  half-edges `(w, k)` and black half-edges `(b, j)`. The indices `k`, `j` are only names of the
  half-edges; the ports seen by the nodes are drawn at random (below).
* Randomness: an arbitrary shared probability space `(S, μ)`, and at every node, independently,
  a uniformly random port order (a permutation of its incident edges) and an infinite string of
  fair random bits. No identifiers are given.
* `State a p t`: the full-information state of a node of degree `a` whose neighbours have
  degree `p`, after `t` synchronous rounds of unbounded messages: own state, and for each own
  port the port number on the neighbour's side and the neighbour's previous state.
* `Algorithm S L Δ δ T`: a `T`-round algorithm for the active (white) side: one measurable
  (not necessarily computable) map from the shared randomness and the `T`-round state of a
  white node to a label on each of its ports, used by all white nodes.
* `output`, `whiteError`, `blackError`, `expError`, `expWhiteError`: Definition 2.9.
-/

open MeasureTheory

namespace AutomaticSelfReduction.Lifting

/-! ### Graphs -/

/-- A finite simple `(Δ, δ)`-biregular 2-coloured graph on `n = nW + nB` vertices. White
vertices are `Fin nW` (degree `Δ`), black vertices are `Fin nB` (degree `δ`); the edges are the
white half-edges `Fin nW × Fin Δ`, matched bijectively with the black half-edges
`Fin nB × Fin δ`. `simple`: no two edges join the same white and black vertex. -/
structure Instance (n Δ δ : ℕ) where
  nW : ℕ
  nB : ℕ
  card_eq : nW + nB = n
  edge : Fin nW × Fin Δ ≃ Fin nB × Fin δ
  simple : ∀ (w : Fin nW) (k k' : Fin Δ), (edge (w, k)).1 = (edge (w, k')).1 → k = k'

namespace Instance

variable {n Δ δ : ℕ}

/-- The same graph with the colours exchanged: a `(δ, Δ)`-biregular 2-coloured graph. -/
def swap (G : Instance n Δ δ) : Instance n δ Δ where
  nW := G.nB
  nB := G.nW
  card_eq := by have := G.card_eq; omega
  edge := G.edge.symm
  simple := by
    intro b j j' h
    have h1 : G.edge (G.edge.symm (b, j)) = (b, j) := G.edge.apply_symm_apply _
    have h2 : G.edge (G.edge.symm (b, j')) = (b, j') := G.edge.apply_symm_apply _
    have hk : (G.edge.symm (b, j)).2 = (G.edge.symm (b, j')).2 := by
      apply G.simple (G.edge.symm (b, j)).1
      have e1 : ((G.edge.symm (b, j)).1, (G.edge.symm (b, j)).2) = G.edge.symm (b, j) := rfl
      have e2 : ((G.edge.symm (b, j)).1, (G.edge.symm (b, j')).2) = G.edge.symm (b, j') :=
        Prod.ext h rfl
      rw [e1, e2, h1, h2]
    have hx : G.edge.symm (b, j) = G.edge.symm (b, j') := Prod.ext h hk
    have := congrArg Prod.snd (G.edge.symm.injective hx)
    exact this

/-- The underlying simple graph on the vertex set `Fin nW ⊕ Fin nB`. -/
def graph (G : Instance n Δ δ) : SimpleGraph (Fin G.nW ⊕ Fin G.nB) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl w, Sum.inr b => ∃ k : Fin Δ, (G.edge (w, k)).1 = b
    | _, _ => False

/-- The girth is at least `g`: every cycle has length at least `g`. Acyclic graphs (girth `∞`)
satisfy this for every `g`. -/
def GirthAtLeast (G : Instance n Δ δ) (g : ℝ) : Prop :=
  ∀ (v : Fin G.nW ⊕ Fin G.nB) (c : G.graph.Walk v v), c.IsCycle → g ≤ (c.length : ℝ)

end Instance

/-! ### Randomness -/

/-- An infinite string of private random bits. -/
abbrev Tape : Type := ℕ → Bool

/-- A fair coin. -/
noncomputable def coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := by
  unfold coin; infer_instance

/-- Independent fair bits: the infinite product of fair coins. -/
noncomputable def tapeMeasure : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => coin)

instance : IsProbabilityMeasure tapeMeasure := by
  unfold tapeMeasure; infer_instance

/-- A port order of a node of degree `d`: local port `i` is the incident edge (half-edge name)
`σ i`. -/
def PortOrder (d : ℕ) : Type := Equiv.Perm (Fin d)

/-- The permutation underlying a port order. -/
def PortOrder.perm {d : ℕ} (σ : PortOrder d) : Equiv.Perm (Fin d) := σ

instance (d : ℕ) : MeasurableSpace (PortOrder d) := ⊤
instance (d : ℕ) : Fintype (PortOrder d) := inferInstanceAs (Fintype (Equiv.Perm (Fin d)))
instance (d : ℕ) : Nonempty (PortOrder d) := ⟨Equiv.refl _⟩

/-- Ports are assigned by each node uniformly at random. -/
noncomputable def portMeasure (d : ℕ) : Measure (PortOrder d) :=
  (PMF.uniformOfFintype (PortOrder d)).toMeasure

instance (d : ℕ) : IsProbabilityMeasure (portMeasure d) := by
  unfold portMeasure; infer_instance

/-- The private randomness of one node of degree `d`: its port order and its random bits. -/
abbrev Private (d : ℕ) : Type := PortOrder d × Tape

/-- Port order and random bits are independent. -/
noncomputable def privateMeasure (d : ℕ) : Measure (Private d) :=
  (portMeasure d).prod tapeMeasure

instance (d : ℕ) : IsProbabilityMeasure (privateMeasure d) := by
  unfold privateMeasure; infer_instance

/-- All randomness of an execution on `G`: the shared randomness and the private randomness of
every white and every black node. -/
abbrev Rand (S : Type) {n Δ δ : ℕ} (G : Instance n Δ δ) : Type :=
  S × ((Fin G.nW → Private Δ) × (Fin G.nB → Private δ))

/-- Shared randomness `μ`, independent of the private randomness, which is independent across
nodes. -/
noncomputable def randMeasure {S : Type} [MeasurableSpace S] (μ : Measure S) {n Δ δ : ℕ}
    (G : Instance n Δ δ) : Measure (Rand S G) :=
  μ.prod ((Measure.pi fun _ : Fin G.nW => privateMeasure Δ).prod
    (Measure.pi fun _ : Fin G.nB => privateMeasure δ))

/-! ### Full-information states -/

/-- A type with a measurable structure. -/
structure MType where
  carrier : Type
  inst : MeasurableSpace carrier

/-- `stateSpace a p t`: states after `t` rounds of a node of degree `a` whose neighbours have
degree `p`. Round `0`: own random bits. Round `t+1`: own state after `t` rounds and, for each own
port `i`, the neighbour's port number of the edge and the neighbour's state after `t` rounds. -/
def stateSpace : ℕ → ℕ → ℕ → MType
  | _, _, 0 => ⟨Tape, inferInstance⟩
  | a, p, t + 1 =>
    letI := (stateSpace a p t).inst
    letI := (stateSpace p a t).inst
    ⟨(stateSpace a p t).carrier × (Fin a → Fin p × (stateSpace p a t).carrier), inferInstance⟩

/-- Full-information state (the radius-`t` view) of a node of degree `a`, neighbours of degree
`p`. -/
def State (a p t : ℕ) : Type := (stateSpace a p t).carrier

instance (a p t : ℕ) : MeasurableSpace (State a p t) := (stateSpace a p t).inst

section Execution

variable {S : Type} {n Δ δ : ℕ}

/-- Under the randomness `ω`, the black half-edge `(b, k)` at the other end of the local port `i`
of the white node `w`: the edge `(w, σ_w i)`. -/
def whitePortEnd (G : Instance n Δ δ) (ω : Rand S G) (w : Fin G.nW) (i : Fin Δ) :
    Fin G.nB × Fin δ :=
  G.edge (w, (ω.2.1 w).1.perm i)

/-- Under the randomness `ω`, the white half-edge `(w, k)` at the other end of the local port `j`
of the black node `b`. -/
def blackPortEnd (G : Instance n Δ δ) (ω : Rand S G) (b : Fin G.nB) (j : Fin δ) :
    Fin G.nW × Fin Δ :=
  G.edge.symm (b, (ω.2.2 b).1.perm j)

/-- The states of all white and all black nodes after `t` rounds, under the randomness `ω`. In
round `t + 1` a node receives on each local port the neighbour's state after `t` rounds and the
neighbour's local port number of that edge (`σ_b⁻¹ k` for the half-edge `(b, k)`). -/
def states (G : Instance n Δ δ) (ω : Rand S G) :
    (t : ℕ) → (Fin G.nW → State Δ δ t) × (Fin G.nB → State δ Δ t)
  | 0 => (fun w => (ω.2.1 w).2, fun b => (ω.2.2 b).2)
  | t + 1 =>
    ((fun w =>
        (((states G ω t).1 w : State Δ δ t),
          fun i : Fin Δ =>
            (((ω.2.2 (whitePortEnd G ω w i).1).1.perm.symm (whitePortEnd G ω w i).2 : Fin δ),
              ((states G ω t).2 (whitePortEnd G ω w i).1 : State δ Δ t))) :
          Fin G.nW → State Δ δ (t + 1)),
      (fun b =>
        (((states G ω t).2 b : State δ Δ t),
          fun j : Fin δ =>
            (((ω.2.1 (blackPortEnd G ω b j).1).1.perm.symm (blackPortEnd G ω b j).2 : Fin Δ),
              ((states G ω t).1 (blackPortEnd G ω b j).1 : State Δ δ t))) :
          Fin G.nB → State δ Δ (t + 1)))

end Execution

/-! ### Algorithms -/

/-- A `T`-round algorithm (§4): a measurable, not necessarily computable, rule mapping the
shared randomness and the `T`-round full-information state of an active (white) node of degree
`Δ` to a label on each of its `Δ` ports. All white nodes run the same rule. -/
structure Algorithm (S : Type) [MeasurableSpace S] (L : Type) (Δ δ T : ℕ) where
  rule : S → State Δ δ T → Fin Δ → L
  measurable_rule : ∀ (i : Fin Δ) (ℓ : L),
    MeasurableSet {x : S × State Δ δ T | rule x.1 x.2 i = ℓ}

section Errors

variable {S : Type} [MeasurableSpace S] {L : Type} {n Δ δ T : ℕ}

/-- The edge labelling produced by `A` on `G` under the randomness `ω`: the edge `(w, k)` gets the
label that `w` outputs on its local port `σ_w⁻¹ k`. -/
def output (A : Algorithm S L Δ δ T) (G : Instance n Δ δ) (ω : Rand S G) :
    Fin G.nW × Fin Δ → L :=
  fun e => A.rule ω.1 ((states G ω T).1 e.1) ((ω.2.1 e.1).1.perm.symm e.2)

/-- `c_f(w)`: the multiset of labels on the edges at the white node `w`. -/
def whiteConf (G : Instance n Δ δ) (f : Fin G.nW × Fin Δ → L) (w : Fin G.nW) : Multiset L :=
  Finset.univ.val.map fun k => f (w, k)

/-- `c_f(b)`: the multiset of labels on the edges at the black node `b`. -/
def blackConf (G : Instance n Δ δ) (f : Fin G.nW × Fin Δ → L) (b : Fin G.nB) : Multiset L :=
  Finset.univ.val.map fun j => f (G.edge.symm (b, j))

variable [DecidableEq L]

/-- Definition 2.9, white error: `∑_{v ∈ W} d(c(v), C_W)`. -/
noncomputable def whiteError (P : Problem L Δ δ) (G : Instance n Δ δ)
    (f : Fin G.nW × Fin Δ → L) : ℕ :=
  ∑ w, distToSet (whiteConf G f w) P.CW

/-- Definition 2.9, black error: `∑_{v ∈ B} d(c(v), C_B)`. -/
noncomputable def blackError (P : Problem L Δ δ) (G : Instance n Δ δ)
    (f : Fin G.nW × Fin Δ → L) : ℕ :=
  ∑ b, distToSet (blackConf G f b) P.CB

/-- Expected white error of `A` on `G`, over all randomness. -/
noncomputable def expWhiteError (P : Problem L Δ δ) (μ : Measure S) (A : Algorithm S L Δ δ T)
    (G : Instance n Δ δ) : ENNReal :=
  ∫⁻ ω, (whiteError P G (output A G ω) : ENNReal) ∂(randMeasure μ G)

/-- Expected error (Definition 2.9) of `A` on `G`: the expectation over all random bits of the
white error plus the black error. -/
noncomputable def expError (P : Problem L Δ δ) (μ : Measure S) (A : Algorithm S L Δ δ T)
    (G : Instance n Δ δ) : ENNReal :=
  ∫⁻ ω, ((whiteError P G (output A G ω) + blackError P G (output A G ω) : ℕ) : ENNReal)
    ∂(randMeasure μ G)

end Errors

/-- The algorithm outputs a configuration of `C_W` at every white node on every execution:
for every shared randomness and every state, the multiset of its port outputs lies in `C_W`. -/
def Algorithm.WhiteValid {S : Type} [MeasurableSpace S] {L : Type} {Δ δ T : ℕ}
    (P : Problem L Δ δ) (A : Algorithm S L Δ δ T) : Prop :=
  ∀ (s : S) (x : State Δ δ T), Finset.univ.val.map (A.rule s x) ∈ P.CW

end AutomaticSelfReduction.Lifting


