-- Prove2me | Definitions.Def_SparseDisc_Supplement_K
-- name    : SparseDisc_Supplement_K
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:03:31.736378+00:00
-- url     : https://prove2.me/theorems/c854c3e2-053d-4671-9983-8ee56d1e39fb
-- title:
--   Worst discrepancy $K_n$ of $n$ functions
-- statement:
--   For $n\ge1$, $K_n$ is the supremum of the discrepancies of all finite instances with exactly $n$ odd $2$-Lipschitz functions and any positive number of items:
--   $$
--   K_n=\sup_G\operatorname{disc}(G).
--   $$
--   The supremum is retained; no attainment is assumed.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_Supplement_instanceDiscrepancy

namespace SparseDisc.Supplement

/-- `K n`, the supremum of the discrepancies of all finite instances with exactly `n` functions
and at least one item (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), Definition 2.4, p.12).

**Formalization Note** The source defines this only for `n ≥ 1`; every theorem using `K n` states
that condition. Both extrema are genuine finite-instance extrema: each inner attainable-threshold
set is nonempty and bounded below, and the source's Lemma 2.5 bounds the outer set. -/
noncomputable def K (n : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ (m : ℕ) (g : Fin n → SparseDisc.Cube (Fin m) → ℝ)
      (U : Fin n → Finset (Fin m)), 1 ≤ m ∧ SparseDisc.IsInstance g U ∧
        c = instanceDiscrepancy g}

end SparseDisc.Supplement


