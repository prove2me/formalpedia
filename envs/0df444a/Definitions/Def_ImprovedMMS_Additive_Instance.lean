-- Prove2me | Definitions.Def_ImprovedMMS_Additive_Instance
-- name    : ImprovedMMS_Additive_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:40.430349+00:00
-- url     : https://prove2.me/theorems/6ca16cfd-d182-42f3-b70a-6ee207ba5875
-- title:
--   §2, p. 13 — α-MMS allocations of an instance, α-reducibility and α-irreducibility (Definition 2.1)
-- statement:
--   Let $n$ agents $a_1,\dots,a_n$ have valuations $V_i$ on the subsets of a finite set of $m$ goods. An **instance** is a pair $(\mathcal N, \mathcal M)$ of a set $\mathcal N$ of agents and a set $\mathcal M$ of goods; each agent $a_i\in\mathcal N$ values a set $S\subseteq\mathcal M$ at $V_i(S)$. Write $n=|\mathcal N|$ and
--   $$\mathsf{MMS}_i=\mathsf{MMS}^{n}_{V_i}(\mathcal M)=\max_{(P_1,\dots,P_n)}\ \min_{1\le j\le n} V_i(P_j)$$
--   for the maxmin share of $a_i$, the maximum over all partitions of $\mathcal M$ into $n$ disjoint (possibly empty) parts.
--
--   1. An **allocation** of $\mathcal M$ to $\mathcal N$ gives every good of $\mathcal M$ to exactly one agent of $\mathcal N$; $A_i$ is the set of goods agent $a_i$ receives. It is **$\alpha$-MMS** if $V_i(A_i)\ge\alpha\,\mathsf{MMS}_i$ for every $a_i\in\mathcal N$. The instance *admits an $\alpha$-MMS allocation* if such an allocation exists.
--   2. (Definition 2.1) The instance is **$\alpha$-reducible** if there are a non-empty set $T\subseteq\mathcal N$ of agents, a set $S\subseteq\mathcal M$ of goods and an allocation $\langle A_i\rangle_{a_i\in T}$ of $S$ to the agents of $T$ such that
--   $$V_i(A_i)\ge\alpha\,\mathsf{MMS}_i\quad(a_i\in T),\qquad \mathsf{MMS}^{\,n-|T|}_{V_i}(\mathcal M\setminus S)\ge\mathsf{MMS}_i\quad(a_i\in\mathcal N\setminus T).$$
--   3. The instance is **$\alpha$-irreducible** if it is not $\alpha$-reducible.
--
--   Reducibility is the device behind the paper's existence proof: an $\alpha$-reducible instance can be shrunk to a smaller one without lowering anyone's share, so it suffices to treat $\alpha$-irreducible instances (Observation 2.1).
--
--   **Formalization Note** Agents are `Fin n` and goods `Fin m`; an instance is a pair of finite sets `N`, `M` with the valuations `v` of all ambient agents, so the sub-instance $(\mathcal N\setminus T,\mathcal M\setminus S)$ needs no re-indexing. An allocation is a map `A : Fin m → Fin n` sending every good of `M` (resp. `S`) into `N` (resp. `T`); agent `i`'s bundle is `M.filter (A · = i)`. The maxmin share is the published `LittleCharity.MMS.mms (v i) k M` over labelled, possibly empty `k`-partitions. The paper's "$T\subset\mathcal N$" is read as a **non-empty** $T\subseteq\mathcal N$: with $T=\emptyset$ (and $S=\emptyset$) every instance would be reducible and every irreducibility hypothesis would be unsatisfiable, while $T=\mathcal N$ is needed (Lemma 3.1 with one agent, Lemma 3.3 with $T=\mathcal N$). Since $T\subseteq\mathcal N$, the natural-number subtraction $|\mathcal N|-|T|$ is exact.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, pp. 11–13, §2 (agents, items, MMS^r_f, allocations, α-MMS) and Definition 2.1

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace ImprovedMMS.Additive

open LittleCharity.MMS

/-- §2, p. 13: the instance with agents `N` and goods `M` admits an `α`-MMS allocation. An
allocation sends every good `b ∈ M` to exactly one agent `A b ∈ N` (so `⋃ A_i = M` and the bundles
are disjoint); agent `i` receives `A_i = M.filter (A · = i)`. It is `α`-MMS when
`V_i(A_i) ≥ α · MMS_i` for every `i ∈ N`, where `MMS_i = MMS^{|N|}_{V_i}(M)`. -/
def AdmitsMMSAlloc {n m : ℕ} (α : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (N : Finset (Fin n)) (M : Finset (Fin m)) : Prop :=
  ∃ A : Fin m → Fin n, (∀ b ∈ M, A b ∈ N) ∧
    ∀ i ∈ N, α * mms (v i) N.card M ≤ v i (M.filter (fun b => A b = i))

/-- Definition 2.1, p. 13: the instance `(N, M)` is `α`-reducible if there are a non-empty set
`T ⊆ N` of agents, a set `S ⊆ M` of goods and an allocation `A` of `S` to the agents of `T` with
`V_i(A_i) ≥ α · MMS_i` for every `i ∈ T` and `MMS^{n-|T|}_{V_i}(M \ S) ≥ MMS_i` for every
`i ∈ N \ T` (here `n = |N|`, `MMS_i = MMS^{n}_{V_i}(M)`). -/
def IsReducible {n m : ℕ} (α : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (N : Finset (Fin n)) (M : Finset (Fin m)) : Prop :=
  ∃ T ⊆ N, T.Nonempty ∧ ∃ S ⊆ M, ∃ A : Fin m → Fin n, (∀ b ∈ S, A b ∈ T) ∧
    (∀ i ∈ T, α * mms (v i) N.card M ≤ v i (S.filter (fun b => A b = i))) ∧
    ∀ i ∈ N \ T, mms (v i) N.card M ≤ mms (v i) (N.card - T.card) (M \ S)

/-- Definition 2.1, p. 13: an instance is `α`-irreducible if it is not `α`-reducible. -/
def IsIrreducible {n m : ℕ} (α : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (N : Finset (Fin n)) (M : Finset (Fin m)) : Prop :=
  ¬ IsReducible α v N M

end ImprovedMMS.Additive


