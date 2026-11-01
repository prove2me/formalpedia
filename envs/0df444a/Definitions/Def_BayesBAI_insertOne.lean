-- Prove2me | Definitions.Def_BayesBAI_insertOne
-- name    : BayesBAI_insertOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:54.451993+00:00
-- url     : https://prove2.me/theorems/15304df9-98e6-4e42-93a1-4f178230400d
-- title:
--   Inserting a coordinate $x$ at arm $i$
-- statement:
--   The vector of $\mathbb R^K$ with coordinate $i$ equal to $x$ and the remaining coordinates given by $\nu$. It inverts $\mu\mapsto(\mu_i,\mu_{\setminus i})$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1.1, p.2

import Mathlib

namespace BayesBAI

/-- The vector whose coordinate `i` is `x` and whose other coordinates are `ν`, for the conditional
density `h_i(x | ν)` of Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, §1.1, p.2. -/
def insertOne {K : ℕ} (i : Fin K) (x : ℝ) (ν : {j : Fin K // j ≠ i} → ℝ) : Fin K → ℝ :=
  fun k => if h : k = i then x else ν ⟨k, h⟩

end BayesBAI


