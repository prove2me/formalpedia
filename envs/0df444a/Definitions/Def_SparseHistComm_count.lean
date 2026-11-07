-- Prove2me | Definitions.Def_SparseHistComm_count
-- name    : SparseHistComm_count
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:40:46.347202+00:00
-- url     : https://prove2.me/theorems/bbcba3a9-c73d-4e42-88fd-09ce17e9d26a
-- title:
--   True-support count $J_i = |\mathrm{supp}(X_i) \cap I_i|$
-- statement:
--   The **true-support count** of user $i$ is
--   $$
--   J_i = |\mathrm{supp}(X_i) \cap I_i(M_i, R)| ,
--   $$
--   the number of truly active coordinates of $X_i$ that its posterior list contains. It depends on the inputs, on user $i$'s message and on the public randomness.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (16), p.8

import Mathlib
import Definitions.Def_SparseHistComm_postList

namespace SparseHistComm

/-- The **true-support count** `Jᵢ = |supp(Xᵢ) ∩ Iᵢ|` of user `i` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (16), p.8), as a
function of the public randomness `r`, the inputs `X = (X₁, …, Xₙ)` and the messages
`m = (m₁, …, mₙ)`; the list `Iᵢ` depends on user `i`'s message only. -/
noncomputable def count {n d : ℕ} (P : Protocol n d) (k : ℕ) (τ : ℝ) (i : Fin n) (r : P.Ω)
    (X : Fin n → Finset (Fin d)) (m : Fin n → List Bool) : ℕ :=
  (X i ∩ postList P k τ i r (m i)).card

end SparseHistComm


