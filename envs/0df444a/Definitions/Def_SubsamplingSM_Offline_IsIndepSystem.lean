-- Prove2me | Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
-- name    : SubsamplingSM_Offline_IsIndepSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:20.498665+00:00
-- url     : https://prove2.me/theorems/1f1c80da-b676-4985-a4e5-ba02301d96cc
-- title:
--   Independence system
-- statement:
--   Let $N$ be a finite ground set and $\mathcal I\subseteq 2^N$ a collection of subsets. The pair $(N,\mathcal I)$ is an **independence system** if
--   1. $\emptyset\in\mathcal I$, and
--   2. $A\subseteq B$ and $B\in\mathcal I$ imply $A\in\mathcal I$.
--
--   Members of $\mathcal I$ are called independent. Every constraint family of the paper (matroids, matchings, knapsack constraints, $p$-extendible systems) is an independence system.
--
--   **Formalization Note** $\mathcal I$ is a predicate `I : Finset α → Prop` on subsets of the ground set `α`.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §3, p. 5

import Mathlib

namespace SubsamplingSM.Offline

/-- **Independence system.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §3, p. 5 (unnumbered): "Given a ground set N and a collection of sets `I ⊆ 2^N`, we
say that the pair `(N, I)` is an independence system if `∅ ∈ I` and `A ⊆ B`, `B ∈ I`
implies that `A ∈ I`."

The collection `I` is a predicate `I : Finset α → Prop` on subsets of the ground set `α`. -/
def IsIndepSystem {α : Type*} (I : Finset α → Prop) : Prop :=
  I ∅ ∧ ∀ A B : Finset α, A ⊆ B → I B → I A

end SubsamplingSM.Offline


