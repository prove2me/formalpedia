-- Prove2me | Definitions.Def_ConsiderChoose_StateSpace_Model
-- name    : ConsiderChoose_StateSpace_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:19.064976+00:00
-- url     : https://prove2.me/theorems/f7b0b681-3ac4-498f-835c-1d760a8be41e
-- title:
--   §2.1, §3, pp. 8–14 — unique-ranking consider-then-choose instance, Rev(j,A), J(S,T), graph G[S,T], components, the DP state space 𝒮 and Φ
-- statement:
--   This file sets up the consider-then-choose assortment problem of Aouad, Farias and Levi under a **unique ranking**, and the state space of its dynamic program.
--
--   **Instance.** There are $N$ products $[N]=\{1,\dots,N\}$ with prices $P_i\in\mathbb R$, and $K$ customer types $[K]$. Type $j$ has a **consideration set** $C_j\subseteq[N]$ and occurs with probability $\lambda_j$; the *standing assumption* is that $(\lambda_1,\dots,\lambda_K)$ is a probability vector. All types rank products by one common permutation $\sigma$, and products are numbered in that order: product $1$ is the most preferred and product $N$ the least.
--
--   **Revenue.** Given an assortment $A\subseteq[N]$, a type-$j$ customer buys the most preferred product of $A\cap C_j$, i.e. the one with the smallest index, and buys nothing if $A\cap C_j=\emptyset$:
--   $$\mathrm{Rev}(j,A)=\begin{cases}P_{\min(A\cap C_j)} & A\cap C_j\neq\emptyset,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   **Subproblems.** For $S\subseteq[N]$ and $T\subseteq[K]$,
--   $$J(S,T)=\max_{A\subseteq S}\ \sum_{j\in T}\lambda_j\,\mathrm{Rev}(j,A),$$
--   the best expected revenue from products in $S$ when only the types in $T$ arrive (probabilities not renormalised).
--
--   **Graph.** $G$ is the bipartite graph with the products and the types as vertices and an edge $\{i,j\}$ exactly when $i\in C_j$. $G[S,T]$ is the subgraph induced on $S\cup T$. A pair $(S',T')$ is a **connected component** of $G[S,T]$ when $S'\subseteq S$, $T'\subseteq T$, $G[S',T']$ is connected (in particular nonempty), and no edge of $G[S,T]$ joins $S'\cup T'$ to the rest of $S\cup T$. For a product $i$, $T(i)=\{j\in T: i\in C_j\}$.
--
--   **State space.** The dynamic program processes products in the order $\sigma$. The set $\mathcal S$ of subproblems it generates is the smallest set such that
--   1. every connected component $(S,T)$ of $G[[N],[K]]$ with $S\neq\emptyset$ and $T\neq\emptyset$ is in $\mathcal S$;
--   2. if $(S,T)\in\mathcal S$ and $i=\min(S)$, every component $(S',T')$ with $S',T'\neq\emptyset$ of $G[S\setminus\{i\},\,T\setminus T(i)]$ (product $i$ stocked) is in $\mathcal S$;
--   3. if $(S,T)\in\mathcal S$ and $i=\min(S)$, every component $(S',T')$ with $S',T'\neq\emptyset$ of $G[S\setminus\{i\},\,T]$ (product $i$ not stocked) is in $\mathcal S$.
--
--   $\mathcal S$ is a set of distinct pairs: a pair reached along several paths counts once. It depends on the consideration sets only.
--
--   **Projection.** For a state $(S,T)$,
--   $$\Phi(S,T)=[\min(S)]\ \cap\ \bigcup_{u\in T}C_u,\qquad [\min(S)]=\{1,\dots,\min(S)\}.$$
--
--   These objects are the vocabulary of §3 of the paper: Lemma 1 and recursion (1) describe the dynamic program over them, and Lemma 2 and Theorem 1 count $\mathcal S$.
--
--   **Formalization Note.** Products are `Fin N` and types `Fin K`; the paper's product $1$ is `0 : Fin N`, and $[\min(S)]$ is the set of indices `≤ S.min' h`, which includes $\min(S)$. $J$ is a finite maximum (`Finset.sup'` over the powerset of $S$, which contains $\emptyset$). Connectivity is Mathlib's `SimpleGraph.Connected` of the induced graph, which requires a nonempty vertex set. `comps C S T` is the finite set of **all** components of $G[S,T]$, including isolated products $(\{k\},\emptyset)$ and isolated types $(\emptyset,\{j\})$; the state space excludes these trivial components (their value $J$ is $0$, and the paper's proof of Lemma 2 assumes every state has an edge). `Phi` returns $\emptyset$ when $S=\emptyset$, which never happens for a state. `stateSpace C` is a subset of a finite type, so `Set.ncard` counts it exactly.
-- source:
--   Aouad, Farias & Levi (2021), Management Science 67(6), accepted manuscript (LBS eprint 1426), pp. 8, 11–14, §2.1, §3 (footnote 1, Cases 1–2, Φ)

import Mathlib

namespace ConsiderChoose.StateSpace

/-- An instance of the assortment problem under a consider-then-choose model with a unique ranking
(Aouad, Farias & Levi 2021, §2.1, p. 8, and §3 *Preliminaries*, p. 11). Products are `Fin N`,
customer types are `Fin K`. The products are numbered by the common ranking `σ`: the order on
`Fin N` *is* the preference order, so `0 : Fin N` (the paper's product 1) is the most preferred
product. `C j` is the consideration set of type `j`, `P i` the price of product `i`, and `lam j`
the fraction of type `j` in the population. -/
structure Instance (N K : ℕ) where
  /-- Consideration sets `C_j ⊆ [N]`. -/
  C : Fin K → Finset (Fin N)
  /-- Prices `P_i`. -/
  P : Fin N → ℝ
  /-- Type probabilities `λ_j`. -/
  lam : Fin K → ℝ

/-- The standing assumption on `λ` (p. 8): `(λ_1, …, λ_K)` is a probability vector. -/
def Instance.Standing {N K : ℕ} (I : Instance N K) : Prop :=
  (∀ j, 0 ≤ I.lam j) ∧ ∑ j, I.lam j = 1

/-- `Rev(j, A)` (p. 8): the price of the most preferred product of `A ∩ C_j` (the smallest index,
since products are numbered by `σ`), and `0` if `A ∩ C_j = ∅` (no purchase). -/
noncomputable def Rev {N K : ℕ} (I : Instance N K) (j : Fin K) (A : Finset (Fin N)) : ℝ :=
  if h : (A ∩ I.C j).Nonempty then I.P ((A ∩ I.C j).min' h) else 0

/-- The subproblem value `J(S, T) = max_{A ⊆ S} Σ_{j ∈ T} λ_j · Rev(j, A)` (p. 11). The maximum is
over the finite, nonempty family of subsets of `S` (it contains `∅`). -/
noncomputable def J {N K : ℕ} (I : Instance N K) (S : Finset (Fin N)) (T : Finset (Fin K)) : ℝ :=
  S.powerset.sup' ⟨∅, Finset.empty_mem_powerset S⟩ (fun A => ∑ j ∈ T, I.lam j * Rev I j A)

/-- The bipartite graph `G = ([N], [K], E)` with `E = {(i, j) : i ∈ C_j}` (p. 11), on the vertex
type `Fin N ⊕ Fin K` (products on the left, types on the right). Its only edges join a product `i`
and a type `j` with `i ∈ C_j`. -/
def bip {N K : ℕ} (C : Fin K → Finset (Fin N)) : SimpleGraph (Fin N ⊕ Fin K) :=
  SimpleGraph.fromRel (fun x y => ∃ i j, x = Sum.inl i ∧ y = Sum.inr j ∧ i ∈ C j)

/-- The vertex set `S ∪ T` of the subgraph `G[S, T]`. -/
def verts {N K : ℕ} (S : Finset (Fin N)) (T : Finset (Fin K)) : Set (Fin N ⊕ Fin K) :=
  {v | Sum.elim (fun i => i ∈ S) (fun j => j ∈ T) v}

/-- `G[S, T]` is connected (p. 11): the subgraph of `G` induced on `S ∪ T` is connected. Mathlib's
`Connected` includes nonemptiness, so `GConnected C ∅ ∅` is false, while a single vertex
(`({k}, ∅)` or `(∅, {j})`) is connected. -/
def GConnected {N K : ℕ} (C : Fin K → Finset (Fin N)) (S : Finset (Fin N)) (T : Finset (Fin K)) :
    Prop :=
  ((bip C).induce (verts S T)).Connected

/-- `(S', T')` is a connected component of `G[S, T]` (footnote 1, p. 12): `S' ∪ T'` lies in `S ∪ T`,
induces a connected subgraph, and no edge of `G[S, T]` leaves it. -/
def IsComponent {N K : ℕ} (C : Fin K → Finset (Fin N)) (S : Finset (Fin N)) (T : Finset (Fin K))
    (S' : Finset (Fin N)) (T' : Finset (Fin K)) : Prop :=
  S' ⊆ S ∧ T' ⊆ T ∧ GConnected C S' T' ∧
    (∀ i ∈ S', ∀ j ∈ T \ T', i ∉ C j) ∧ (∀ j ∈ T', ∀ i ∈ S \ S', i ∉ C j)

open Classical in
/-- The finite set of **all** connected components `(S_u, T_u)` of `G[S, T]`, including the trivial
ones (an isolated product `({k}, ∅)` or an isolated type `(∅, {j})`). -/
noncomputable def comps {N K : ℕ} (C : Fin K → Finset (Fin N)) (S : Finset (Fin N))
    (T : Finset (Fin K)) : Finset (Finset (Fin N) × Finset (Fin K)) :=
  Finset.univ.filter (fun p => IsComponent C S T p.1 p.2)

/-- `T(i) = {j ∈ T : i ∈ C_j}` (p. 13): the types in `T` whose consideration set contains `i`. -/
def typesOf {N K : ℕ} (C : Fin K → Finset (Fin N)) (T : Finset (Fin K)) (i : Fin N) :
    Finset (Fin K) :=
  T.filter (fun j => i ∈ C j)

/-- The subproblems generated by the recursion of §3 (pp. 12–14), with products processed in the
order `σ` (smallest index first):
* `root`: the nontrivial connected components of `G[[N], [K]]` (base case, p. 12);
* `stock`: from a generated `(S, T)` with `i = min(S)`, the nontrivial components of the residual
  graph `G[S \ {i}, T \ T(i)]` (Case 1, p. 13);
* `skip`: the nontrivial components of `G[S \ {i}, T]` (Case 2, p. 13).

"Nontrivial" means `S' ≠ ∅` and `T' ≠ ∅`: isolated products and isolated types are not states
(their value `J` is `0`). -/
inductive Reachable {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    Finset (Fin N) → Finset (Fin K) → Prop
  | root {S : Finset (Fin N)} {T : Finset (Fin K)} :
      IsComponent C Finset.univ Finset.univ S T → S.Nonempty → T.Nonempty → Reachable C S T
  | stock {S : Finset (Fin N)} {T : Finset (Fin K)} {S' : Finset (Fin N)} {T' : Finset (Fin K)} :
      Reachable C S T → (h : S.Nonempty) →
      IsComponent C (S.erase (S.min' h)) (T \ typesOf C T (S.min' h)) S' T' →
      S'.Nonempty → T'.Nonempty → Reachable C S' T'
  | skip {S : Finset (Fin N)} {T : Finset (Fin K)} {S' : Finset (Fin N)} {T' : Finset (Fin K)} :
      Reachable C S T → (h : S.Nonempty) →
      IsComponent C (S.erase (S.min' h)) T S' T' →
      S'.Nonempty → T'.Nonempty → Reachable C S' T'

/-- The state space `𝒮` (p. 14): the set of distinct subproblems `(S, T)` generated by the
recursion. It depends on the consideration sets only, not on prices or type probabilities. It is a
subset of the finite type `Finset (Fin N) × Finset (Fin K)`, so it is finite and `Set.ncard` counts
it exactly. -/
def stateSpace {N K : ℕ} (C : Fin K → Finset (Fin N)) : Set (Finset (Fin N) × Finset (Fin K)) :=
  {p | Reachable C p.1 p.2}

/-- The projection `Φ(S, T) = [min(S)] ∩ ⋃_{u ∈ T} C_u` (p. 14), where
`[min(S)] = {1, …, min(S)}` is the set of products at least as preferred as `min(S)` (indices
`≤ min(S)`, including `min(S)`). On `S = ∅`, which is never a state, it is `∅`. -/
def Phi {N K : ℕ} (C : Fin K → Finset (Fin N)) (S : Finset (Fin N)) (T : Finset (Fin K)) :
    Finset (Fin N) :=
  if h : S.Nonempty then (Finset.univ.filter (· ≤ S.min' h)) ∩ T.biUnion C else ∅

end ConsiderChoose.StateSpace


