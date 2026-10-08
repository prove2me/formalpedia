-- Prove2me | Definitions.Def_KellyReversibility_MarkovFields_RandomField
-- name    : KellyReversibility_MarkovFields_RandomField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:41.887036+00:00
-- url     : https://prove2.me/theorems/ad0ffa5a-e701-4049-942f-e02d6357c8c4
-- title:
--   Random fields, the conditional probabilities (9.1), Markov fields (9.2) and the simplex product form (9.5)
-- statement:
--   Consider a system of $J$ **sites**, the vertices of a finite graph $G$. Site $j$ carries an **attribute** $n_j$ from a finite set $\mathcal N_j$, so the state of the system is $\mathbf n = (n_1,\dots,n_J)$ in the state space $\mathcal S = \mathcal N_1\times\cdots\times\mathcal N_J$. For a set of sites $H$, $\mathbf n_H$ is the vector of attributes of the sites in $H$; $G-j$ denotes the sites other than $j$ and $\partial j$ the set of neighbours of $j$ in $G$. The operator $T_j^m$ changes the attribute of site $j$ to $m$:
--   $$T_j^m\mathbf n = (n_1,\dots,n_{j-1},m,n_{j+1},\dots,n_J).$$
--
--   1. A **random field** is a function $\pi:\mathcal S\to\mathbb R$ with $\pi(\mathbf n)>0$ for every state and $\sum_{\mathbf n\in\mathcal S}\pi(\mathbf n)=1$: a probability distribution on $\mathcal S$ that gives positive probability to every state.
--   2. The **conditional probability** that site $j$ has attribute $n_j$ given the attributes of all other sites is
--   $$P(n_j\mid \mathbf n_{G-j}) = \frac{\pi(\mathbf n)}{\sum_{m\in\mathcal N_j}\pi(T_j^m\mathbf n)}. \qquad (9.1)$$
--   3. For a set of sites $H$, $P(n_j\mid\mathbf n_H)$ is the conditional probability, under $\pi$, that site $j$ has attribute $n_j$ given that the sites of $H$ have attributes $\mathbf n_H$: the $\pi$-probability of the states agreeing with $\mathbf n$ at $j$ and on $H$, divided by the $\pi$-probability of the states agreeing with $\mathbf n$ on $H$.
--   4. $\pi$ is a **Markov field** with respect to $G$ if for every site $j$ and state $\mathbf n$
--   $$P(n_j\mid\mathbf n_{G-j}) = P(n_j\mid\mathbf n_{\partial j}). \qquad (9.2)$$
--   5. A **simplex** of $G$ is a nonempty set of sites $C$ any two distinct members of which are joined by an edge (a single site, or a clique). $\mathcal C$ is the set of simplices.
--   6. $\pi$ has the **simplex product form (9.5)** if there are a constant $B$ and real functions $\phi_C$ of $\mathbf n_C$, $C\in\mathcal C$, such that
--   $$\pi(\mathbf n) = B\prod_{C\in\mathcal C}\phi_C(\mathbf n_C), \qquad \mathbf n\in\mathcal S.$$
--
--   These are the objects of Kelly's §9.1. A Markov field is a random field with limited dependence: the attribute of a site depends on the rest of the system only through its neighbours.
--
--   **Formalization Note** Sites form an arbitrary finite type `V` with decidable equality (Kelly's $\{1,\dots,J\}$); the attribute sets `N j` are finite types that may differ from site to site; $T_j^m\mathbf n$ is `Function.update n j m`. The book writes $\pi:\mathcal S\to(0,1)$; positivity and summing to one give values in $(0,1]$, with the value $1$ only when $\mathcal S$ is a single state. The empty set is not a simplex; a factor for it would be a constant and is absorbed in $B$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 184–186 (PDF 187–189), §9.1: definition of random field (p. 184), Eq. (9.1) and (9.2) (p. 185), definition of simplex and Eq. (9.5) (p. 186)

import Mathlib

namespace KellyReversibility.MarkovFields

open Finset

/-! Kelly, *Reversibility and Stochastic Networks* (1979), §9.1, pp. 184–186.

There are finitely many sites `V` (the vertices of a graph `G`), site `j` carries an attribute
from the finite set `N j`, and a state is `n : (j : V) → N j`. The operator `T_j^m` of p. 185,
which changes the attribute of site `j` to `m`, is `Function.update n j m`. -/

/-- **Random field** (p. 184): a function on the state space `𝒮 = ∏ⱼ 𝒩ⱼ` that is strictly
positive at every state and sums to one over `𝒮`. -/
def IsRandomField {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π : ((j : V) → N j) → ℝ) : Prop :=
  (∀ n, 0 < π n) ∧ ∑ n, π n = 1

/-- **The conditional probability (9.1)** that site `j` has attribute `n j` given the attributes
`n_{G-j}` of all other sites:
`P(n_j | n_{G-j}) = π(n) / ∑_{m ∈ 𝒩_j} π(T_j^m n)`. -/
noncomputable def condProb {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π : ((j : V) → N j) → ℝ) (j : V) (n : (k : V) → N k) : ℝ :=
  π n / ∑ m : N j, π (Function.update n j m)

open Classical in
/-- **The conditional probability `P(n_j | n_H)`** that site `j` has attribute `n j` given only
the attributes `n_H` of the sites in `H`, computed from the joint law `π`:
the `π`-mass of the states agreeing with `n` at `j` and on `H`, divided by the `π`-mass of the
states agreeing with `n` on `H`. -/
noncomputable def condProbGiven {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π : ((j : V) → N j) → ℝ) (j : V) (H : Set V)
    (n : (k : V) → N k) : ℝ :=
  (∑ n' ∈ univ.filter (fun n' : (k : V) → N k => n' j = n j ∧ ∀ k ∈ H, n' k = n k), π n') /
    (∑ n' ∈ univ.filter (fun n' : (k : V) → N k => ∀ k ∈ H, n' k = n k), π n')

/-- **Markov field (9.2)** (p. 185): for every site `j` and state `n`,
`P(n_j | n_{G-j}) = P(n_j | n_{∂j})`, where `∂j = G.neighborSet j` is the set of neighbours
of `j` in `G`, the left side is (9.1) and the right side is the conditional probability of
`n_j` given the neighbours' attributes only. -/
def IsMarkovField {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (G : SimpleGraph V) (π : ((j : V) → N j) → ℝ) : Prop :=
  ∀ (j : V) (n : (k : V) → N k), condProb π j n = condProbGiven π j (G.neighborSet j) n

open Classical in
/-- **The simplices `𝒞` of `G`** (p. 186): the nonempty sets of sites `C` such that any two
distinct sites of `C` are joined by an edge of `G` (the single sites and the cliques of `G`). -/
noncomputable def simplices {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) :=
  univ.filter (fun C : Finset V => C.Nonempty ∧ G.IsClique (C : Set V))

/-- **The product form (9.5)**: `π(n) = B ∏_{C ∈ 𝒞} φ_C(n_C)` for all states `n`, for some
constant `B` and some real functions `φ_C` of the attributes `n_C` of the sites in `C`. -/
def HasSimplexProductForm {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (G : SimpleGraph V) (π : ((j : V) → N j) → ℝ) : Prop :=
  ∃ (B : ℝ) (φ : (C : Finset V) → ((k : C) → N k) → ℝ),
    ∀ n : (k : V) → N k, π n = B * ∏ C ∈ simplices G, φ C (fun k => n k)

end KellyReversibility.MarkovFields


