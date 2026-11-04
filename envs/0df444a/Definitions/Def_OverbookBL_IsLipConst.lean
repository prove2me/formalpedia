-- Prove2me | Definitions.Def_OverbookBL_IsLipConst
-- name    : OverbookBL_IsLipConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:56.374222+00:00
-- url     : https://prove2.me/theorems/efccfc84-bfe3-46cc-a370-8ba6223987e2
-- title:
--   The local Lipschitz property of Lemma 2 for a constant $\delta$
-- statement:
--   Fix an instance. A natural number $\delta$ has the **local Lipschitz property** if for every capacity $B$, past accepted arrivals $\vec x[t-1]$, (estimated) future arrivals $\widetilde N^f[t]$, every solution $\vec x^\star$ of problem (1) that is locally optimal at $j$, and every type $i$ such that a type-$i$ customer can still be added ($x^\star_i<\widetilde N^f_i[t]$ when $i\ne j$), there is $l\in\{0,1,\dots,\delta\}$ with
--
--   $$
--   \vec x'=\vec x^\star+e_i-l\,e_j\ \text{ a feasible solution of (1), locally optimal at } j .
--   $$
--
--   Lemma 2 asserts that some $\delta\ge1$ has this property; Lemma 6 and Claim 3 are stated for "$\delta$ as constructed in Lemma 2".
--
--   **Formalization Note** Feasibility of $\vec x'$ (implicit in "locally optimal") forces $x^\star_i<\widetilde N^f_i[t]$ when $i\ne j$, assumed, and $l\le x^\star_j+\mathbb 1\{i=j\}$, part of the conclusion.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 2, p.13

import Definitions.Def_OverbookBL_IsLocOpt

namespace OverbookBL

/-- The local Lipschitz property of Lemma 2 (Freund & Zhao, *Overbooking with bounded loss*,
arXiv:2204.11148v2, Lemma 2, p.13) for a given constant `δ`: for every capacity `B`, past
accepted arrivals `past`, estimated future arrivals `Nf` and solution `x` of problem (1) that is
locally optimal at `j`, and every type `i`, there is `l ∈ {0, 1, …, δ}` such that
`x + eᵢ − l eⱼ` is (a solution of (1)) locally optimal at `j`.

Lemma 2 states that some `δ ≥ 1` has this property; Lemma 6 and Claim 3 use "`δ` as constructed in
Lemma 2", which this predicate names.

**Formalization Note** "`x⃗′ = x⃗⋆ + eᵢ − l eⱼ` is locally optimal at `j`" presupposes that `x⃗′` is
a feasible solution of (1) (Definition 2 is stated for feasible solutions). This needs
`x⋆ᵢ < Ñᶠᵢ[t]` when `i ≠ j` (taken as a hypothesis) and `l ≤ x⋆ⱼ + 𝟙{i=j}` (part of the
conclusion, so that the `ℕ` subtraction in `x + eᵢ − l eⱼ` never truncates). For `i = j` the
property holds trivially with `l = 1`. -/
def IsLipConst {k : ℕ} (I : Instance k) (δ : ℕ) : Prop :=
  ∀ (B : ℕ) (past Nf x : Fin k → ℕ) (i j : Fin k),
    IsLocOpt I B past Nf x j → (i ≠ j → x i < Nf i) →
      ∃ l : ℕ, l ≤ δ ∧ l ≤ x j + (if i = j then 1 else 0) ∧
        IsLocOpt I B past Nf (x + Pi.single i 1 - l • Pi.single j 1) j

end OverbookBL


