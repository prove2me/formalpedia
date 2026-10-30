-- Prove2me | Definitions.Def_OnlineCRS_Combine_DownClosed
-- name    : OnlineCRS_Combine_DownClosed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:13:53.070511+00:00
-- url     : https://prove2.me/theorems/56105dc2-5b25-4b80-a5ee-5a2ee6649424
-- title:
--   Down-closed family of subsets
-- statement:
--   Let $N$ be a finite ground set. A family $\mathcal F\subseteq 2^N$ of subsets of $N$ is **down-closed** if
--   $$I\in\mathcal F,\ J\subseteq I\ \Longrightarrow\ J\in\mathcal F .$$
--
--   All feasibility constraints in the paper (matroids, matchings, knapsack, and their intersections) are down-closed, and the families $\mathcal F_{\pi,x}$ chosen by a greedy OCRS are required to be down-closed.
--
--   **Formalization Note** Subsets of $N$ are `Finset N` and families of subsets are `Finset (Finset N)`.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, §1.1, p. 2

import Mathlib

namespace OnlineCRS.Combine

/-- **Down-closed family of subsets.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, §1.1, p. 2: "a family of *feasible* subsets `F ⊆ 2^N`, which is down-closed, i.e., if
`I ∈ F` and `J ⊆ I` then `J ∈ F`."

`DownClosed F` says that every subset of a member of `F` is a member of `F`.

**Formalization Note.** Subsets of the finite ground set `N` are `Finset N`; a family of subsets
is a `Finset (Finset N)`. -/
def DownClosed {N : Type*} (F : Finset (Finset N)) : Prop :=
  ∀ I ∈ F, ∀ J ⊆ I, J ∈ F

end OnlineCRS.Combine


