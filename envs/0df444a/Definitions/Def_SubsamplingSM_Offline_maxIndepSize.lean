-- Prove2me | Definitions.Def_SubsamplingSM_Offline_maxIndepSize
-- name    : SubsamplingSM_Offline_maxIndepSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:07.681538+00:00
-- url     : https://prove2.me/theorems/04c44469-532f-4e98-8c39-44fe7f8bfa1b
-- title:
--   $k$, the size of the largest independent set
-- statement:
--   For an independence system $(N,\mathcal I)$ on a finite ground set, $k$ is the size of the largest independent set:
--   $$k=\max\{|S| : S\in\mathcal I\}.$$
--
--   It enters the oracle-call bound of Theorem 1.
--
--   **Formalization Note** The maximum is a supremum over the finite collection of independent sets; it equals $0$ when $\mathcal I=\{\emptyset\}$. Decidability of $\mathcal I$ is classical.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §2, p. 3

import Mathlib

namespace SubsamplingSM.Offline

open Classical in
/-- **`k`, the size of the largest independent set.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §2, p. 3 (unnumbered): "k is the size of the largest independent set"; it
enters the query bound "`O(nk/p)`" of Theorem 1, p. 7.

`maxIndepSize I = max {|S| : S ∈ I}` over the finite ground set `α` (it is `0` when the only
independent set is `∅`, and when no set is independent).

**Formalization Note.** Decidability of `I` is classical, so no statement carries a
`Decidable` binder. -/
noncomputable def maxIndepSize {α : Type*} [Fintype α] (I : Finset α → Prop) : ℕ :=
  (Finset.univ.filter I).sup Finset.card

end SubsamplingSM.Offline


