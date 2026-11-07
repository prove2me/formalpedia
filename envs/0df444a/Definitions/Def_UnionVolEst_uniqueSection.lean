-- Prove2me | Definitions.Def_UnionVolEst_uniqueSection
-- name    : UnionVolEst_uniqueSection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:50.591665+00:00
-- url     : https://prove2.me/theorems/dbefc73f-962a-4865-b358-abf892050bfa
-- title:
--   Unique sections $\hat K_j = K_j \setminus \bigcup_{i>j} K_i$
-- statement:
--   Given bodies $K_1,\dots,K_M$ processed in this order, each point of the union is assigned to the last body that contains it:
--   $$
--   \hat K_j := K_j \setminus \bigcup_{i>j} K_i .
--   $$
--   The unique sections are pairwise disjoint and their union is $K_1\cup\dots\cup K_M$. They describe which points survive the removal steps (lines 6–7) of Alpona.
--
--   **Formalization Note** Bodies are indexed by `Fin M`, i.e. $0,\dots,M-1$, in the same order.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, p.17 (PDF p.19)

import Mathlib

namespace UnionVolEst

/-- The unique sections of §5.1 (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), printed p.17, PDF p.19): each point of the union is
assigned to the last body (in the processing order) that contains it,
`K̂_j := K_j \ ⋃_{i > j} K_i`.

**Formalization Note** Bodies are indexed by `Fin M`, i.e. `0, …, M − 1` instead of the page's
`1, …, M`, with the same order. -/
def uniqueSection {α : Type*} {M : ℕ} (K : Fin M → Set α) (j : Fin M) : Set α :=
  K j \ ⋃ (i : Fin M) (_ : j < i), K i

end UnionVolEst


