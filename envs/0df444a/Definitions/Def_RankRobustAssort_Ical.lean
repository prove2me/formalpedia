-- Prove2me | Definitions.Def_RankRobustAssort_Ical
-- name    : RankRobustAssort_Ical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:58.939528+00:00
-- url     : https://prove2.me/theorems/6ee7c624-d30b-41eb-9dbd-d8a48f62e928
-- title:
--   The set $\mathcal I_{i_1\cdots i_M}(S)$
-- statement:
--   For an assortment $S$ and a tuple $(i_1,\dots,i_M)$,
--
--   $$
--   \mathcal I_{i_1\cdots i_M}(S)=\{i\in\mathcal N_0:\ \text{for all } m\in\mathcal M,\ \text{if } i_m\in S, \text{ then } i_m\not\prec_{i_1\cdots i_M} i\},
--   $$
--
--   the vertices of $\mathcal G_{i_1\cdots i_M}$ with no directed path to any vertex $i_m$ that lies in $S$. It gives the graphical description of $\rho_{i_1\cdots i_M}(S)$ (Proposition EC.1).
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Definition EC.2, p.ec16

import Mathlib
import Definitions.Def_RankRobustAssort_Reach

namespace RankRobustAssort

/-- Membership in `ℐ_{i₁⋯i_M}(S) ≜ {i ∈ 𝒩₀ : for all m ∈ ℳ, if i_m ∈ S, then i_m ⊀_{i₁⋯i_M} i}`:
the vertices of `𝒢_{i₁⋯i_M}` with no directed path to a vertex `i_m` that lies in `S`.

Sturt, arXiv:2112.05010v4, Definition EC.2, p.ec16.

Formalization Note: `Ical P t S` is the set as a predicate on `Fin (n+1)`; `i_m ⊀ i` is
`¬ Reach P t (t m) i` (no path of ≥ 1 edge from `i` to `t m`). -/
def Ical {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Prop :=
  ∀ m, t m ∈ S → ¬ Reach P t (t m) i

end RankRobustAssort


