-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_xi
-- name    : RankRobustAssort_Supplement_xi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:34:18.658826+00:00
-- url     : https://prove2.me/theorems/8a337207-a5d6-43bb-aaf6-a504e0a52b59
-- title:
--   $\xi_{i_1\cdots i_M}(S)$: largest revenue reachable as top choice (Definition EC.3)
-- statement:
--   For an assortment $S$ and a tuple $(i_1,\dots,i_M)$, let
--
--   $$
--   \xi_{i_1\cdots i_M}(S)=\max_{i\in S:\ \bigcap_{m\in\mathcal M}\mathcal D_{i_m}(S_m)\cap\mathcal D_i(S)\neq\emptyset} r_i ,
--   $$
--
--   where $\mathcal D_i(S)$ is the set of rankings under which $i$ is the most preferred product of $S$. It is the largest revenue among the products of $S$ that can be most preferred in $S$ under a ranking that, in each past assortment $S_m$, most prefers $i_m$. It is the optimistic counterpart of $\rho_{i_1\cdots i_M}(S)$ (Definition 4).
--
--   **Formalization Note.** The maximum is taken in $\mathbb R\cup\{-\infty\}$, so an empty index set gives $-\infty$; for $S\in\mathcal S$ and tuples in $\mathcal L$ the index set is nonempty and the value is the paper's real maximum.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Definition EC.3, p.ec54

import Mathlib
import Definitions.Def_RankRobustAssort_Problem
import Definitions.Def_RankRobustAssort_IsTop

open Classical

namespace RankRobustAssort.Supplement

/-- For an assortment `S` and a tuple `(i₁,…,i_M)`, the largest revenue among the products of `S`
that can be most preferred in `S` under a ranking corresponding to the tuple:
`ξ_{i₁⋯i_M}(S) ≜ max_{i∈S : ⋂_{m∈ℳ} 𝒟_{i_m}(S_m) ∩ 𝒟_i(S) ≠ ∅} r_i`.

Sturt, arXiv:2112.05010v4, Definition EC.3, p.ec54.

Formalization Note: the optimistic mirror of the published `rho` (same index set, `max` instead
of `min`). The maximum is `Finset.sup` in `WithBot ℝ`, so an empty index set gives `⊥` rather
than a junk real. For a tuple in `ℒ` and a nonempty `S` (in particular every `S ∈ 𝒮`) the index
set is nonempty and the value is the real maximum `r_i` of the paper; the paper uses `ξ` only for
`S ∈ 𝒮` and tuples in `ℒ`. -/
noncomputable def xi {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1))
    (S : Finset (Fin (n + 1))) : WithBot ℝ :=
  (S.filter (fun i => ∃ σ : Equiv.Perm (Fin (n + 1)),
      (∀ m, IsTop σ (P.S m) (t m)) ∧ IsTop σ S i)).sup (fun i => ((P.r i : ℝ) : WithBot ℝ))

end RankRobustAssort.Supplement


