-- Prove2me | Definitions.Def_SponsoredAssort_IsBestSelector
-- name    : SponsoredAssort_IsBestSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:39.556774+00:00
-- url     : https://prove2.me/theorems/95016929-1f69-4264-aafa-429695f09f7a
-- title:
--   Pointwise welfare-maximizing part $S^P(v)\in\arg\max_\ell R(S_\ell,v)$
-- statement:
--   Let $P=(S_\ell)_{\ell\in L}$ be a partition of $[n]$: the parts are pairwise disjoint and cover $[n]$. A selector $S^P$ chooses at every profile $v$ a part of highest welfare,
--
--   $$
--   S^P(v)\in\arg\max_{\ell\in L} R(S_\ell,v).
--   $$
--
--   **Formalization Note** Partitions are `Finpartition`s of the set of all sellers (nonempty parts). The paper does not specify how ties are broken, so every theorem using $S^P$ is stated for every such selector.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 5.2, pp.26–27

import Mathlib
import Definitions.Def_SponsoredAssort_welfare

open scoped NNReal

namespace SponsoredAssort

/-- `S` is a **pointwise welfare-maximizing selector among the parts of the partition `P`**
(Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Definition 5.2, pp.26–27):
`S^P(v) ∈ argmax_{ℓ ∈ L} R(S_ℓ, v)` for every profile `v`, where `P = (S_ℓ)_{ℓ ∈ L}`.

**Formalization Note.** A partition of `[n]` is a `Finpartition` of `Finset.univ`, whose parts are
nonempty and pairwise disjoint and cover `[n]` (p.26). The paper does not say how ties in the
`argmax` are broken, so the selector is a parameter: any function choosing, at every `v`, a part of
maximal welfare. -/
def IsBestSelector {n : ℕ} (r : Fin n → ℝ) (P : Finpartition (Finset.univ : Finset (Fin n)))
    (S : Attr n → Finset (Fin n)) : Prop :=
  ∀ v, S v ∈ P.parts ∧ ∀ T ∈ P.parts, welfare r T v ≤ welfare r (S v) v

end SponsoredAssort


