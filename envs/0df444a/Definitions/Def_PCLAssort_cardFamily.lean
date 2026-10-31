-- Prove2me | Definitions.Def_PCLAssort_cardFamily
-- name    : PCLAssort_cardFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:39.672989+00:00
-- url     : https://prove2.me/theorems/d8af1b4e-8c5d-4b14-ba26-cbd3844e777a
-- title:
--   Cardinality-constrained assortments
-- statement:
--   For a limit $c\in\mathbb N$ on the number of products, the cardinality-constrained family is
--
--   $$
--   \mathcal F=\Big\{x\in\{0,1\}^n\ \Big|\ \sum_i x_i\le c\Big\},
--   $$
--
--   that is, all assortments with at most $c$ products.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §2, p.790 (PDF p.6)

import Mathlib

namespace PCLAssort

/-- The cardinality-constrained family `𝓕 = {x ∈ {0,1}^n | ∑_i x_i ≤ c}` (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §2, p.790), as a
family of assortments. -/
def cardFamily (n c : ℕ) : Set (Finset (Fin n)) :=
  {S | S.card ≤ c}

end PCLAssort


