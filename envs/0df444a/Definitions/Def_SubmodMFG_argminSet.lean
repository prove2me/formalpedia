-- Prove2me | Definitions.Def_SubmodMFG_argminSet
-- name    : SubmodMFG_argminSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:26.250065+00:00
-- url     : https://prove2.me/theorems/6dbdae23-e8e0-4214-b4c8-20eb3bef4cd6
-- title:
--   The set of minimizers $\arg\min_E J(\cdot,\mu)$
-- statement:
--   Let $E$ be the set of strategies of the representative player and $J:E\times L\to\mathbb R$ her cost functional. For a distribution $\mu\in L$, the **set of minimizers** is
--   $$
--   \arg\min_E J(\cdot,\mu)=\{\nu\in E:\ J(\nu,\mu)\le J(\nu',\mu)\ \text{for all }\nu'\in E\}.
--   $$
--
--   It is the set of optimal strategies of the representative player when the population is distributed according to $\mu$.
--
--   **Formalization Note** $J$ is curried, $J:E\to L\to\mathbb R$. The minimum is global over $E$; the set may be empty (Assumption 2.1 (1) excludes that).
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.1, p.5 (Assumption 2.1) and p.6

import Mathlib

namespace SubmodMFG

/-- **The set of minimizers `arg min_E J(·, µ)`.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.1, p.5 (Assumption 2.1) and p.6 (definition of `R(µ)`).

For a cost functional `J : E × L → ℝ` and a distribution `µ ∈ L`, the set of strategies
`ν ∈ E` that minimize `J(·, µ)` over the whole strategy set `E`.

**Formalization Note.** `J` is curried, `J : E → L → ℝ`, with `J ν µ = J(ν, µ)`. The minimum is
global over `E` (not local, not on a subset). The set may be empty; Assumption 2.1 (1) is what
makes it nonempty. -/
def argminSet {E L : Type*} (J : E → L → ℝ) (μ : L) : Set E :=
  {ν | ∀ ν' : E, J ν μ ≤ J ν' μ}

end SubmodMFG


