-- Prove2me | Definitions.Def_SparseHistComm_worstCost
-- name    : SparseHistComm_worstCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:10.575564+00:00
-- url     : https://prove2.me/theorems/33af9f01-13f5-4f64-9275-171366f51d24
-- title:
--   Worst-case cost of a protocol
-- statement:
--   The **cost** of a protocol is its worst-case expected total message length over admissible inputs:
--   $$
--   \sup_{\substack{x_1,\dots,x_n \in \{0,1\}^d \\ \|x_i\|_0 \le k\ \forall i}} E\Big[\sum_{i=1}^n |M_i|\Big].
--   $$
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (3), p.2

import Mathlib
import Definitions.Def_SparseHistComm_expCost
import Definitions.Def_SparseHistComm_Admissible
open scoped ENNReal

namespace SparseHistComm

/-- The **cost** of a protocol (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (3), p.2):
`sup_{x₁,…,xₙ ∈ {0,1}^d, ‖xᵢ‖₀ ≤ k ∀i} E[∑ᵢ |Mᵢ|]`. -/
noncomputable def worstCost {n d : ℕ} (P : Protocol n d) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (x : Fin n → Finset (Fin d)) (_ : Admissible k x), expCost P x

end SparseHistComm


