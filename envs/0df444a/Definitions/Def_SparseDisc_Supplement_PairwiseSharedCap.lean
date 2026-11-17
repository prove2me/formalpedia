-- Prove2me | Definitions.Def_SparseDisc_Supplement_PairwiseSharedCap
-- name    : SparseDisc_Supplement_PairwiseSharedCap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:04:38.584499+00:00
-- url     : https://prove2.me/theorems/169c1b5d-5b0e-45e0-a3eb-26dd2d82657d
-- title:
--   Pairwise shared-item cap
-- statement:
--   Declared supports satisfy the **pairwise shared-item cap** $s$ when $|U_u\cap U_v|\le s$ for every two distinct functions $u,v$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorems 1.10 and 8.37, pp.5,46

import Mathlib

namespace SparseDisc.Supplement

/-- Any two distinct functions share at most `s` declared support items, the hypothesis of
Theorems 1.10 and 8.37 (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), pp.5,46). -/
def PairwiseSharedCap {V ι : Type} [DecidableEq ι]
    (U : V → Finset ι) (s : ℕ) : Prop :=
  ∀ u v, u ≠ v → ((U u) ∩ (U v)).card ≤ s

end SparseDisc.Supplement


