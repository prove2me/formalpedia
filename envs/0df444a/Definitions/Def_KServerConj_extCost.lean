-- Prove2me | Definitions.Def_KServerConj_extCost
-- name    : KServerConj_extCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:07.422226+00:00
-- url     : https://prove2.me/theorems/6776489e-46d3-474c-a8eb-6618ce05edb0
-- title:
--   Extended cost $\mathrm{ExtCost}_t=\max_X(w_t(X)-w_{t-1}(X))$
-- statement:
--   For a finite point set $M$, the **extended cost** of the request at time $t\ge1$ is the largest increase of the work function at that request,
--
--   $$\mathrm{ExtCost}_t=\max_X\big(w_t(X)-w_{t-1}(X)\big),$$
--
--   the maximum over all configurations $X$ of $k$ points. Bounding the total extended cost instead of the algorithm's cost is the extended-cost method of Chrobak and Larmore (Lemma 1.1).
--
--   **Formalization Note** $M$ is finite (the paper's standing assumption in the analysis). The maximum is a supremum over the finite type of $k$-point subsets; it is attained whenever that type is nonempty, which every statement guarantees through the initial configuration.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Lemma 1.1, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_workFn

namespace KServerConj

/-- **The extended cost of the request at time `t`**, Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Lemma 1.1, printed
p.2 (PDF p.3): `ExtCost_t = max_X (w_t(X) − w_{t−1}(X))`, the maximum over configurations `X`.

**Formalization Note.** Stated for a finite point set `M` (the paper's standing assumption, printed
p.1: "We assume in the analysis that M is finite"). The maximum runs over configurations, i.e.
`X : Finset M` with `X.card = k`; it is a supremum over a finite type, which is attained when that
type is nonempty (`k ≤ |M|`, guaranteed in every statement by the initial configuration). -/
noncomputable def extCost {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (C₀ : Finset M)
    (r : ℕ → M) (t : ℕ) : ℝ :=
  ⨆ X : {X : Finset M // X.card = k},
    (workFn k C₀ r t (X : Finset M) - workFn k C₀ r (t - 1) (X : Finset M))

end KServerConj


