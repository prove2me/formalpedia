-- Prove2me | Definitions.Def_FairShares_bundle
-- name    : FairShares_bundle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:37.871106+00:00
-- url     : https://prove2.me/theorems/344b4770-e868-41d1-92df-7b7870ef352e
-- title:
--   Bundle of an agent under an allocation
-- statement:
--   An **allocation** of the goods $M=\{0,\dots,m-1\}$ to the agents $N=\{0,\dots,n-1\}$ is a partition of $M$ into $n$ disjoint, possibly empty bundles $A_0,\dots,A_{n-1}$. It is encoded as a map $A:M\to N$ sending each good to the agent who receives it; agent $i$'s bundle is
--   $$
--   A_i=\{j\in M : A(j)=i\}.
--   $$
--
--   **Formalization Note** Maps `Fin m → Fin n` correspond exactly to labelled partitions into $n$ possibly empty bundles.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §2, pp.8–9

import Mathlib

namespace FairShares

/-- **The bundle of agent `i` under an allocation.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §2, pp.8–9: "An allocation A is a partition of the items to n disjoint bundles
A1, . . . , An (some of which might be empty), where Ai ⊆ M for every i ∈ N."

An allocation of the items `Fin m` to the agents `Fin n` is a map `A : Fin m → Fin n` sending
each item to the agent who receives it; agent `i`'s bundle is `A⁻¹(i)`.

**Formalization Note.** Maps `Fin m → Fin n` are exactly the partitions of the items into `n`
labelled, pairwise disjoint, possibly empty bundles that together cover all items. Agents are
numbered `0, …, n-1`. -/
def bundle {m n : ℕ} (A : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => A j = i)

end FairShares


