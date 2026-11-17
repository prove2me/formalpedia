-- Prove2me | Definitions.Def_SparseDisc_Supplement_IsBundleStructure
-- name    : SparseDisc_Supplement_IsBundleStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:03:46.817214+00:00
-- url     : https://prove2.me/theorems/85106b3f-78a6-4356-bc39-0a5533d2b14d
-- title:
--   Bundle structure $(B_e,S_e)$
-- statement:
--   A **bundle structure** consists of nonempty pairwise disjoint item sets $B_e$ and nonempty reader sets $S_e$, such that every declared support item of $v$ lies in some $B_e$ with $v\in S_e$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 5.1, p.21

import Mathlib

namespace SparseDisc.Supplement

/-- A bundle structure `(B_e,S_e)` for declared supports `U_v`: the item bundles are nonempty,
pairwise disjoint, the reader sets are nonempty, and every declared support item is covered by a
bundle whose reader set contains that function (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Definition 5.1,
p.21). -/
def IsBundleStructure {V ι E : Type} (U : V → Finset ι)
    (B : E → Finset ι) (S : E → Finset V) : Prop :=
  (∀ e, (B e).Nonempty) ∧ (∀ e, (S e).Nonempty) ∧
    (∀ e e', e ≠ e' → Disjoint (B e) (B e')) ∧
    ∀ v j, j ∈ U v → ∃ e, v ∈ S e ∧ j ∈ B e

end SparseDisc.Supplement


