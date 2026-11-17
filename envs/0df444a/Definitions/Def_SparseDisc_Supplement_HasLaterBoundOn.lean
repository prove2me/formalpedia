-- Prove2me | Definitions.Def_SparseDisc_Supplement_HasLaterBoundOn
-- name    : SparseDisc_Supplement_HasLaterBoundOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:05:28.363655+00:00
-- url     : https://prove2.me/theorems/bce266a0-0223-49a3-bb55-5ab48e3538b1
-- title:
--   Ordering with bounded later neighbours inside a vertex set
-- statement:
--   The vertices of $W$ have a **later-neighbour bound** $d$ if they admit an ordering in which every vertex has at most $d$ later neighbours that also belong to $W$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.22(d), p.38

import Mathlib

namespace SparseDisc.Supplement

open Classical in
/-- The vertices in `W` admit an ordering in which every vertex has at most `d` later neighbours
also in `W`, as used for `V₁` in Theorem 8.22(d) (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy
Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.38). -/
noncomputable def HasLaterBoundOn {V : Type} [Fintype V]
    (G : SimpleGraph V) (W : Finset V) (d : ℕ) : Prop :=
  ∃ r : V → ℕ, Function.Injective r ∧ ∀ v ∈ W,
    (W.filter (fun w => G.Adj v w ∧ r v < r w)).card ≤ d

end SparseDisc.Supplement


