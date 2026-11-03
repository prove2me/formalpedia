-- Prove2me | Definitions.Def_RankRobustAssort_IsTop
-- name    : RankRobustAssort_IsTop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:09.029889+00:00
-- url     : https://prove2.me/theorems/61fb885d-f9dd-46de-8366-d75f8cf6de02
-- title:
--   Most preferred product $i=\arg\min_{j\in S}\sigma(j)$
-- statement:
--   A **ranking** is a one-to-one map $\sigma:\{0,\dots,n\}\to\{0,\dots,n\}$; it prefers product $i$ to product $j$ if and only if $\sigma(i)<\sigma(j)$. Product $i$ is the **most preferred product of the assortment $S$** under $\sigma$ when
--
--   $$
--   i\in S\quad\text{and}\quad \sigma(i)\le\sigma(j)\ \text{ for all } j\in S,
--   $$
--
--   that is, $i=\arg\min_{j\in S}\sigma(j)$; equivalently $\sigma\in\mathcal D_i(S)=\{\sigma\in\Sigma: i=\arg\min_{j\in S}\sigma(j)\}$ (Definition 2).
--
--   A customer with ranking $\sigma$ offered $S$ buys this product; it is the building block of the choice probabilities and of the tuple set $\mathcal L$.
--
--   **Formalization Note.** Products are $\mathrm{Fin}(n+1)$ with $0$ the no-purchase option, and rankings are permutations of $\mathrm{Fin}(n+1)$. Since $\sigma$ is injective the minimizer over a nonempty $S$ is unique; for $S=\emptyset$ no product is most preferred.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §2, p.7 and Definition 2, p.15

import Mathlib

namespace RankRobustAssort

/-- `IsTop σ S i` says that `i` is the most preferred product of the assortment `S` under the
ranking `σ`, i.e. `i = arg min_{j ∈ S} σ(j)`; equivalently `σ ∈ 𝒟_i(S)`.

Sturt, arXiv:2112.05010v4, §2, p.7 (rankings `σ : {0,…,n} → {0,…,n}` one-to-one, "σ encodes a
preference for product i over product j if and only if σ(i) < σ(j)", and the indicator
`𝕀{i = arg min_{j∈S} σ(j)}`) and Definition 2, p.15 (`𝒟_i(S) ≜ {σ ∈ Σ : i = arg min_{j∈S} σ(j)}`).

Formalization Note: products are `Fin (n+1)` with `0` the no-purchase option; a ranking is a
permutation `σ : Equiv.Perm (Fin (n+1))`, and a smaller value `σ i` means more preferred. Since
`σ` is injective, the arg min over a nonempty `S` is unique, so "`i` attains the minimum of `σ` on
`S`" is the paper's `i = arg min_{j∈S} σ(j)`. For `S = ∅` no `i` is top. -/
def IsTop {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    Prop :=
  i ∈ S ∧ ∀ j ∈ S, σ i ≤ σ j

end RankRobustAssort


