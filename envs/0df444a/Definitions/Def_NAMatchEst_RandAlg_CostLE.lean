-- Prove2me | Definitions.Def_NAMatchEst_RandAlg_CostLE
-- name    : NAMatchEst_RandAlg_CostLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:12.906334+00:00
-- url     : https://prove2.me/theorems/255654f6-5584-4456-8640-8b7361c65c72
-- title:
--   Worst-case query bound
-- statement:
--   An algorithm $A$ makes **at most $q$ queries in the worst case** if, for every seed $\omega$ (including seeds of weight zero), the list $\mathrm{queries}(\omega)$ has at most $q$ entries.
--
--   This is the cost measure of Theorem 3 and Lemma 3.1 ("in the worst case").
--
--   **Formalization Note** Repeated queries are charged each time they occur; the paper allows identical queries to be answered once, so this measure is at least the paper's.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 3, p.17 (PDF 21) and Lemma 3.1, p.19 (PDF 23)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg

namespace NAMatchEst

/-- The algorithm `A` makes **at most `q` queries in the worst case**: under every seed (including
seeds of weight zero) its query list has length at most `q`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 3, p.17 (PDF 21) ("The algorithm makes at most … degree and indexed-neighbor
queries in the worst case") and Lemma 3.1, p.19 (PDF 23) ("Its worst-case number of queries").

**Formalization Note** Repeated queries are charged each time they occur in the list. -/
def RandAlg.CostLE {n : ℕ} {β : Type} (A : RandAlg n β) (q : ℝ) : Prop :=
  ∀ ω, ((A.queries ω).length : ℝ) ≤ q

end NAMatchEst


