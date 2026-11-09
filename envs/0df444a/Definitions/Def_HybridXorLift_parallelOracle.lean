-- Prove2me | Definitions.Def_HybridXorLift_parallelOracle
-- name    : HybridXorLift_parallelOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:45.193692+00:00
-- url     : https://prove2.me/theorems/c8cf2c18-b65a-4aa1-a67d-aa373165c3b7
-- title:
--   $k$ parallel controlled phase queries
-- statement:
--   For an input $x \in \{0,1\}^\iota$, the **$k$ parallel controlled phase queries** act on $k$ query registers and a workspace as the diagonal operator
--   $$
--   O^{(k)}_x\, |(k_1,b_1),\dots,(k_k,b_k), w\rangle = \prod_{\ell=1}^k (-1)^{b_\ell x_{k_\ell}}\, |(k_1,b_1),\dots,(k_k,b_k), w\rangle .
--   $$
--   Each factor is the controlled phase oracle (2.1) on one register; a slot with $b_\ell = 0$ is inactive.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.2, p.9 (PDF p.11); Eq. (2.1)

import Mathlib

namespace HybridXorLift

/-- The `k` controlled phase queries made at the same time on `k` separate query registers
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.2, p.9 (PDF p.11), and Eq. (2.1)): the diagonal matrix with entry
`∏_ℓ (−1)^{b_ℓ x_{k_ℓ}}` on the basis vector `|(k_1, b_1), …, (k_k, b_k), w⟩`; it acts as the
identity on the workspace. A slot with control bit `b_ℓ = 0` is inactive but still counts. -/
def parallelOracle {ι : Type} [DecidableEq ι] (k w : ℕ) (x : ι → Bool) :
    Matrix ((Fin k → ι × Bool) × Fin w) ((Fin k → ι × Bool) × Fin w) ℂ :=
  Matrix.diagonal fun p => ∏ l, if (p.1 l).2 && x (p.1 l).1 then -1 else 1

end HybridXorLift


