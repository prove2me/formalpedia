-- Prove2me | Definitions.Def_BalancedKneser_KG
-- name    : BalancedKneser_KG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:01.404763+00:00
-- url     : https://prove2.me/theorems/1e9401e1-5cc1-40e5-bf01-f519345aa4f9
-- title:
--   Generalized Kneser graph $KG(N,k,r)$ and the balanced graph $G_{n,r}=KG(2n,n,r)$
-- statement:
--   For integers $N,k,r$, the **generalized Kneser graph** $KG(N,k,r)$ has as vertices the $k$-subsets of $[N]=\{1,\dots,N\}$; two distinct $k$-sets $A,B$ are adjacent when
--   $$
--   |A\cap B|<r .
--   $$
--   A proper coloring therefore partitions the $k$-sets into families in which every two members share at least $r$ elements. The **balanced graph** is
--   $$
--   G_{n,r}=KG(2n,n,r),
--   $$
--   whose vertices are the $n$-subsets of $[2n]$, i.e. the balanced allocations of $2n$ goods. Its chromatic number $\chi(G_{n,c+1})$ is the exact threshold for balanced EF$c$ (Theorem 2.1).
--
--   **Formalization Note** $[N]$ is $\mathrm{Fin}\,N$ (0-based), and a $k$-set is an element of the subtype $\{A:\mathrm{Finset}(\mathrm{Fin}\,N)\mid |A|=k\}$ (`KSet N k`). A decidability instance for adjacency is included.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §1, p.1 (PDF p.3): KG(N, k, r) and G_{n,r}

import Mathlib

namespace BalancedKneser

/-- The `k`-subsets of `[N]`, encoded as `{A : Finset (Fin N) // A.card = k}` (the ground set
`[N] = {1, …, N}` is `Fin N`, 0-based). -/
abbrev KSet (N k : ℕ) : Type := {A : Finset (Fin N) // A.card = k}

/-- **Generalized Kneser graph** `KG(N, k, r)` (Alipour–Jafari, *Balanced Fair Division and
Generalized Kneser Graphs*, arXiv:2611.04486v1, §1, p.1 (PDF p.3)): its vertices are the
`k`-subsets of `[N]`, and two distinct sets are adjacent when their intersection has size less
than `r`.

Formalization Note: `[N]` is `Fin N` (0-based). -/
def KG (N k r : ℕ) : SimpleGraph (KSet N k) where
  Adj A B := A ≠ B ∧ (A.1 ∩ B.1).card < r
  symm := ⟨fun A B h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun A h => h.1 rfl⟩

instance (N k r : ℕ) : DecidableRel (KG N k r).Adj := fun A B =>
  inferInstanceAs (Decidable (A ≠ B ∧ (A.1 ∩ B.1).card < r))

/-- The balanced graph `G_{n,r} = KG(2n, n, r)` (arXiv:2611.04486v1, §1, p.1 (PDF p.3)): the
`n`-subsets of `[2n]`, two distinct ones adjacent when they share fewer than `r` elements. -/
abbrev Gnr (n r : ℕ) : SimpleGraph (KSet (2 * n) n) := KG (2 * n) n r

end BalancedKneser


