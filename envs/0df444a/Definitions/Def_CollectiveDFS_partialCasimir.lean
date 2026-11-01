-- Prove2me | Definitions.Def_CollectiveDFS_partialCasimir
-- name    : CollectiveDFS_partialCasimir
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:05.942115+00:00
-- url     : https://prove2.me/theorems/dae6a466-d2d7-49e5-b4fe-32ea7bf6825d
-- title:
--   Partial Casimir $(s^k)^2$
-- statement:
--   For $0\le k\le n$, the **partial Casimir** is
--   $$(s^k)^2=\sum_{\alpha=x,y,z}\big(s^k_\alpha\big)^2,\qquad s^k_\alpha=\tfrac12 S^k_\alpha=\sum_{i=1}^k\tfrac12\sigma^i_\alpha,$$
--   the squared total spin of the first $k$ qubits. On a spin-$J_k$ irreducible representation of the first $k$ qubits it acts as $J_k(J_k+1)$. At $k=n$ it is the total Casimir $(s^n)^2$.
--
--   **Formalization Note** This is the operator in $s=S/2$ used in (7.12) and (7.23); the operator $(S^k)^2$ of (7.8) equals $4(s^k)^2$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.10) and the line after it, p.23

import Mathlib
import Definitions.Def_CollectiveDFS_partialS

open QAlgorithms

namespace CollectiveDFS

/-- The partial Casimir `(s^k)² = Σ_{α=x,y,z} (s^k_α)²`, where `s^k_α = ½ S^k_α = Σ_{i≤k} ½ σ_α^i`
(7.10) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eq. (7.10) and the line after it, p.23, PDF p.23). Its eigenvalue on a spin-`J_k`
irrep of the first `k` qubits is `J_k(J_k+1)`. At `k = n` it is the total Casimir `(s^n)²`.

**Formalization Note** This is the operator in `s = S/2`, as in (7.12) and (7.23); the operator
`(S^k)²` of (7.8) is `4 (s^k)²`. -/
noncomputable def partialCasimir (n k : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ α : Fin 3, ((1 / 2 : ℂ) • partialS n k α) ^ 2

end CollectiveDFS


