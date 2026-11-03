-- Prove2me | Definitions.Def_RankRobustAssort_rho
-- name    : RankRobustAssort_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:19.98423+00:00
-- url     : https://prove2.me/theorems/ae6d738c-45d8-47fb-937a-6cbe4c0afd19
-- title:
--   Least revenue $\rho_{i_1\cdots i_M}(S)$ of a top product of $S$ compatible with a tuple
-- statement:
--   For an assortment $S$ and a tuple $(i_1,\dots,i_M)$,
--
--   $$
--   \rho_{i_1\cdots i_M}(S)=\min_{i\in S:\ \bigcap_{m\in\mathcal M}\mathcal D_{i_m}(S_m)\cap\mathcal D_i(S)\ne\emptyset} r_i,
--   $$
--
--   the minimum revenue among the products of $S$ that can be the most preferred product of $S$ under a ranking corresponding to the tuple. These are the objective coefficients of the linear program (2).
--
--   **Formalization Note.** The minimum is taken in $\mathbb R\cup\{+\infty\}$, so it equals $+\infty$ when the index set is empty instead of a default real value. For tuples in $\mathcal L$ and nonempty $S$ (in particular every $S\in\mathcal S$) the index set is nonempty and the value is the paper's real minimum.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Definition 4, p.15

import Mathlib
import Definitions.Def_RankRobustAssort_Problem
import Definitions.Def_RankRobustAssort_IsTop

open Classical

namespace RankRobustAssort

/-- For an assortment `S` and a tuple `(i₁,…,i_M)`, the least revenue among the products of `S`
that can be most preferred in `S` under a ranking corresponding to the tuple:
`ρ_{i₁⋯i_M}(S) ≜ min_{i∈S : ⋂_{m∈ℳ} 𝒟_{i_m}(S_m) ∩ 𝒟_i(S) ≠ ∅} r_i`.

Sturt, arXiv:2112.05010v4, Definition 4, p.15.

Formalization Note: the minimum is `Finset.inf` in `WithTop ℝ`, so an empty index set gives `⊤`
rather than a junk real. For a tuple in `ℒ` and a nonempty `S` (in particular every `S ∈ 𝒮`) the
index set is nonempty and the value is the real minimum `r_i` of the paper; the paper defines
`ρ` only for `S ∈ 𝒮` and tuples in `ℒ`. -/
noncomputable def rho {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1))
    (S : Finset (Fin (n + 1))) : WithTop ℝ :=
  (S.filter (fun i => ∃ σ : Equiv.Perm (Fin (n + 1)),
      (∀ m, IsTop σ (P.S m) (t m)) ∧ IsTop σ S i)).inf (fun i => ((P.r i : ℝ) : WithTop ℝ))

end RankRobustAssort


