-- Prove2me | Definitions.Def_OSPMech_SqrtLB_Model
-- name    : OSPMech_SqrtLB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:02.774577+00:00
-- url     : https://prove2.me/theorems/0916c083-60cc-48a9-b958-4f2a6b6b2d1b
-- title:
--   §2, §3, §4.2, pp. 6–8, 12 — extensive-form mechanisms: implementation trees, compatibility, divergence, OSP, the OSP-graph; machine scheduling, makespan, k-approximation; divergence rank
-- statement:
--   This file sets up extensive-form mechanisms, obvious strategyproofness and machine scheduling on related machines, following §2 and §3 of Ferraioli, Meier, Penna and Ventre.
--
--   **Implementation trees.** There are $n$ agents, indexed by $i \in [n]$; agent $i$ has a real type $t_i$ in a finite domain $D_i$, and $D = \times_i D_i$ is the set of type profiles. An *implementation tree* $\mathcal T$ is a rooted tree in which every leaf $\ell$ carries an outcome $X(\ell)$ and every internal vertex $u$ is labelled by an agent $S(u)$. At $u$ the agent $S(u)$ takes an action that depends only on her own presumed type, and the action selects the child through which the execution continues. A profile $\mathbf b$ is *compatible* with $u$ if its execution passes through $u$; two profiles *diverge* at $u$ if both are compatible with $u$ and they leave $u$ through different children. Every profile reaches exactly one leaf, and $\mathcal M(\mathbf b)$ is the outcome there. A vertex at which two profiles of $D$ diverge is a *divergent node*.
--
--   **Obvious strategyproofness.** Payments are a function $\mathbf p(\mathbf b) = (p_1(\mathbf b), \dots, p_n(\mathbf b))$ of the declared profile, and the utility of agent $i$ of true type $t_i$ is quasi-linear, $u_i(t_i, \mathcal M(\mathbf b)) = p_i(\mathbf b) - t_i(f(\mathbf b))$, where $t_i(X)$ is the cost of outcome $X$ for type $t_i$. The mechanism is *obviously strategyproof* (OSP) if for every agent $i$, every vertex $u$ with $S(u) = i$, and all profiles $(t_i, \mathbf b_{-i})$ and $(b_i, \mathbf b'_{-i})$ in $D$ that are compatible with $u$ and diverge at $u$,
--   $$u_i(t_i, \mathcal M(t_i, \mathbf b_{-i})) \ge u_i(t_i, \mathcal M(b_i, \mathbf b'_{-i})).$$
--
--   **The OSP-graph.** For agent $i$, the OSP-graph $\mathcal O_i^{\mathcal T}$ has the profiles of $D$ as nodes and an edge from $\mathbf a = (a, \mathbf a_{-i})$ to $\mathbf b = (b, \mathbf b_{-i})$ whenever both are compatible with some vertex labelled $i$ at which they diverge. The edge has weight $a(f(\mathbf b)) - a(f(\mathbf a))$. The graph has *no negative-weight cycle* if every closed walk along its edges has non-negative total weight.
--
--   **Machine scheduling.** There are $m$ identical jobs and agent $i$ controls a related machine with processing time $t_i$ per job. An outcome is a load vector $\mathbf x = (x_1, \dots, x_n)$ of natural numbers, and the cost of agent $i$ is $t_i \cdot x_i$. The *makespan* of $\mathbf x$ under $\mathbf b$ is $\max_i b_i x_i$, and $\mathrm{OPT}(\mathbf b)$ is the least makespan over all load vectors with $\sum_i x_i = m$. A mechanism is a *schedule* on $D$ if every outcome on $D$ assigns exactly $m$ jobs, and it is *$k$-approximate* on $D$ if
--   $$\max_i b_i f_i(\mathbf b) \le k \cdot \mathrm{OPT}(\mathbf b) \quad \text{for every } \mathbf b \in D.$$
--
--   **Divergence rank.** Following the renaming in the proof of Theorem 12 (p. 12), agent $i$ is the $(r+1)$-th diverging agent at vertex $u_i$ if $u_i$ lies on the execution path of the all-$H$ profile, $i$ diverges at $u_i$ and at no earlier vertex of that path, and exactly $r$ distinct agents diverge at earlier vertices of that path.
--
--   These objects carry the paper's characterization of OSP by cycle monotonicity and its lower bound for scheduling with three-value domains.
--
--   **Formalization Note.** A vertex is encoded by its agent and an action map from types to child indices, so the paper's four conditions on edge labels hold by construction; positions are lists of child indices. Payments are a function of the declared profile (p. 6, and the payments built in the proof of Theorem 3, p. 24), not a leaf label; for impossibility results this is the stronger reading. The edge weight is the one of Observation 1 and of the proof of Theorem 3 (p. 24); Definition 2 prints the opponents' profiles $\mathbf b_{-i}$ and $\mathbf b'_{-i}$ swapped. The paper's subtree "in which agents that previously diverged took actions compatible with $H$" is the path of the all-$H$ profile, because on that path a vertex labelled by an agent who has not yet diverged is either not divergent or is that agent's divergence. The divergence rank $r$ is 0-based: the paper's agent $i$ has $r = i - 1$. The makespan is a supremum over the finite set of machines and OPT an infimum over the (nonempty, bounded below) set of feasible schedules.
-- source:
--   Ferraioli, Meier, Penna, Ventre, On the approximation guarantee of obviously strategyproof mechanisms, arXiv:1805.04190v2, pp. 6–8, 12, §2, §3 (Definition 2), §4.2

import Mathlib

namespace OSPMech.SqrtLB

/-- §2, pp. 6–7: an implementation tree 𝒯 for `n` agents with outcomes in `X`.
An internal vertex `u` is labelled by an agent `i = S(u)` and an action map `act : ℝ → ℕ`: a profile `b`
leaves `u` towards the child `act (b i)`. The edge label T(u, v) is the set of profiles compatible with
`u` whose action selects `v`. Because `act` is a function of the agent's own type, the four conditions
on edge labels of p. 7 hold automatically (outgoing labels are disjoint, they cover the incoming label,
the root's cover every profile, and the child chosen depends on `bᵢ` only). Every leaf `ℓ` carries an
outcome `X(ℓ)`. Root-to-leaf paths are finite. -/
inductive ImplTree (n : ℕ) (X : Type) where
  | leaf : X → ImplTree n X
  | node : Fin n → (ℝ → ℕ) → (ℕ → ImplTree n X) → ImplTree n X

variable {n : ℕ} {X : Type}

/-- p. 7: ℳ(b) = X(ℓ(b)), the outcome at the unique leaf reached by the profile `b`. -/
def outcome : ImplTree n X → (Fin n → ℝ) → X
  | .leaf x, _ => x
  | .node i act ch, b => outcome (ch (act (b i))) b

/-- The list of child indices that the profile `b` follows from the root to its leaf. -/
def path : ImplTree n X → (Fin n → ℝ) → List ℕ
  | .leaf _, _ => []
  | .node i act ch, b => act (b i) :: path (ch (act (b i))) b

/-- The vertex at position `pos` (a list of child indices read from the root), if it exists. -/
def subtreeAt : ImplTree n X → List ℕ → Option (ImplTree n X)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node _ _ ch, k :: pos => subtreeAt (ch k) pos

/-- p. 7: the profile `b` is compatible with the vertex at position `pos`, i.e. `b ∈ T(φ(u), u)`:
the path of `b` passes through that vertex. -/
def Compatible (t : ImplTree n X) (pos : List ℕ) (b : Fin n → ℝ) : Prop := pos <+: path t b

/-- `b ∈ D = ×ᵢ Dᵢ`. -/
def InDomain (D : Fin n → Finset ℝ) (b : Fin n → ℝ) : Prop := ∀ i, b i ∈ D i

/-- p. 7: the vertex at position `pos` is labelled by agent `i`, the profiles `b` and `b'` are both
compatible with it, and they diverge there (they leave it through different children). -/
def DivergeAt (t : ImplTree n X) (pos : List ℕ) (i : Fin n) (b b' : Fin n → ℝ) : Prop :=
  Compatible t pos b ∧ Compatible t pos b' ∧
    ∃ act ch, subtreeAt t pos = some (.node i act ch) ∧ act (b i) ≠ act (b' i)

/-- p. 7: obvious strategyproofness of the extensive-form mechanism with tree `t` and payments `p`,
where `cost i a x` is the cost a(x) of agent `i` of type `a` for the outcome `x`. For every vertex
labelled `i`, every true profile `b = (tᵢ, b₋ᵢ)` and every deviation `bDev = (bᵢ, b′₋ᵢ)` in `D` that are
compatible with the vertex and diverge there (so `bᵢ ≠ tᵢ`), the utility of truth-telling is at least
that of deviating: uᵢ(tᵢ, ℳ(tᵢ, b₋ᵢ)) ≥ uᵢ(tᵢ, ℳ(bᵢ, b′₋ᵢ)), with uᵢ(tᵢ, ℳ(b)) = pᵢ(b) − tᵢ(f(b)).
Payments are a function of the declared profile, p = p(b) (p. 6). -/
def IsOSP (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X)
    (p : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (pos : List ℕ) (i : Fin n) (b bDev : Fin n → ℝ), InDomain D b → InDomain D bDev →
    DivergeAt t pos i b bDev →
    p bDev i - cost i (b i) (outcome t bDev) ≤ p b i - cost i (b i) (outcome t b)

/-- Definition 2, p. 8: an edge of the OSP-graph 𝒪ᵢ^𝒯 from the profile `a = (a, a₋ᵢ)` to the profile
`b = (b, b₋ᵢ)`: both in `D`, and both compatible with some `ab`-separating vertex `u` for `i` (a vertex
labelled `i` where they diverge). -/
def OSPEdge (D : Fin n → Finset ℝ) (t : ImplTree n X) (i : Fin n) (a b : Fin n → ℝ) : Prop :=
  InDomain D a ∧ InDomain D b ∧ ∃ pos, DivergeAt t pos i a b

/-- The weight of the OSP-graph edge from `a` to `b`: aᵢ(f(b)) − aᵢ(f(a)), the cost for type `aᵢ` of the
outcome at the head minus its cost of the outcome at the tail (the weight of Observation 1, (1), and of
the proof of Theorem 3, p. 24; Definition 2 prints the opponents' profiles swapped). -/
def edgeWeight (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X) (i : Fin n) (a b : Fin n → ℝ) : ℝ :=
  cost i (a i) (outcome t b) - cost i (a i) (outcome t a)

/-- 𝒪ᵢ^𝒯 has no negative-weight cycle: every closed walk `w 0 → w 1 → ⋯ → w k → w 0` along its edges
has non-negative total weight. -/
def NoNegCycle (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X) (i : Fin n) :
    Prop :=
  ∀ (k : ℕ) (w : Fin (k + 1) → (Fin n → ℝ)),
    (∀ j, OSPEdge D t i (w j) (w (finRotate (k + 1) j))) →
    0 ≤ ∑ j, edgeWeight cost t i (w j) (w (finRotate (k + 1) j))

/-! Machine scheduling, p. 8: `m` identical jobs on related machines; an outcome is the vector of job
loads `x : Fin n → ℕ`. -/

/-- The cost tᵢ · fᵢ of agent `i` of type `a` for the load vector `x`. -/
def schedCost : Fin n → ℝ → (Fin n → ℕ) → ℝ := fun i a x => a * x i

/-- The makespan maxᵢ bᵢ xᵢ of the load vector `x` under the processing times `b`. -/
noncomputable def makespan (b : Fin n → ℝ) (x : Fin n → ℕ) : ℝ := ⨆ i, b i * (x i : ℝ)

/-- OPT(b): the least makespan over all schedules of the `m` identical jobs. -/
noncomputable def optMakespan (m : ℕ) (b : Fin n → ℝ) : ℝ :=
  sInf ((fun x => makespan b x) '' {x : Fin n → ℕ | ∑ i, x i = m})

/-- Every outcome of the tree on a profile of `D` schedules exactly the `m` jobs. -/
def IsSchedule (m : ℕ) (D : Fin n → Finset ℝ) (t : ImplTree n (Fin n → ℕ)) : Prop :=
  ∀ b, InDomain D b → ∑ i, outcome t b i = m

/-- p. 8: the mechanism is `k`-approximate on `D`: its makespan is at most `k` times the optimum on
every profile of `D`. -/
def IsKApprox (m : ℕ) (k : ℝ) (D : Fin n → Finset ℝ) (t : ImplTree n (Fin n → ℕ)) : Prop :=
  ∀ b, InDomain D b → makespan b (outcome t b) ≤ k * optMakespan m b

/-! The renaming of the agents in the proof of Theorem 12, p. 12. -/

/-- The vertex at position `pos` is a divergent node with divergent agent `i` (p. 7): it is labelled
by `i` and two profiles of `D` diverge there. -/
def IsDivergentNode (D : Fin n → Finset ℝ) (t : ImplTree n X) (pos : List ℕ) (i : Fin n) : Prop :=
  ∃ b b', InDomain D b ∧ InDomain D b' ∧ DivergeAt t pos i b b'

/-- p. 12: agent `i` is the (r + 1)-th agent to diverge in the subtree in which every agent that
previously diverged took the action compatible with type `H`, and `pos` is the node uᵢ at which `i`
diverges there. That subtree is followed exactly by the all-`H` profile: on its path, a vertex labelled
by an agent that has not diverged before either is not divergent (all compatible profiles take the same
child) or is that agent's divergence. So: `pos` lies on the path of the all-`H` profile, `i` diverges at
`pos` and at no earlier vertex of that path, and exactly `r` distinct agents diverge at earlier vertices
of that path. The rank `r` is 0-based: the paper's agent `i` has `r = i − 1`. -/
def IsKthDiverger (D : Fin n → Finset ℝ) (t : ImplTree n X) (H : ℝ) (r : ℕ) (i : Fin n)
    (pos : List ℕ) : Prop :=
  pos <+: path t (fun _ => H) ∧ IsDivergentNode D t pos i ∧
    (∀ pos', pos' <+: pos → pos' ≠ pos → ¬ IsDivergentNode D t pos' i) ∧
    {j : Fin n | ∃ pos', pos' <+: pos ∧ pos' ≠ pos ∧ IsDivergentNode D t pos' j}.ncard = r

end OSPMech.SqrtLB


