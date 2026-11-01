-- Prove2me | Definitions.Def_CollectiveDFS_IsPath
-- name    : CollectiveDFS_IsPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:10.696997+00:00
-- url     : https://prove2.me/theorems/1e2e2ad8-9ffb-4df1-8cd6-b0883c76a9f7
-- title:
--   Paths of partial spins $(J_1,\dots,J_n)$
-- statement:
--   A **path** for $n$ qubits is a sequence of partial spins $(J_1,\dots,J_n)$ with $J_1=\tfrac12$, every $J_k\ge 0$, and $|J_{k+1}-J_k|=\tfrac12$: each step combines the spin $J_k$ of the first $k$ qubits with one more spin-$\tfrac12$ particle to give $J_k+\tfrac12$ or $|J_k-\tfrac12|$ (p.23, Fig. 4).
--
--   **Formalization Note** Labels are doubled and positions 0-based: a path is $p:\mathrm{Fin}\,n\to\mathbb N$ with $p(k)=2J_{k+1}$. A step down from $J_k=0$ is impossible because labels are natural numbers, matching the absolute value in the paper.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §VII, p.23

import Mathlib

namespace CollectiveDFS

/-- A path of partial spins `(J_1, …, J_n)` for `n` qubits: `J_1 = 1/2`, every `J_k ≥ 0`, and
`|J_{k+1} − J_k| = 1/2` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII, p.23, PDF p.23: "each step … corresponds to combining the
previous spin J particle with a spin 1/2 particle to create a J + 1/2 or |J − 1/2| particle …
starting from a single qubit with J_1 = 1/2"; Fig. 4).

**Formalization Note** Doubled labels and 0-based positions: `p k = 2 J_{k+1}` for `k : Fin n`.
`J_k ≥ 0` holds by typing, so a step down from `J_k = 0` is impossible, matching the absolute
value in the paper. -/
def IsPath {n : ℕ} (p : Fin n → ℕ) : Prop :=
  (∀ h : 0 < n, p ⟨0, h⟩ = 1) ∧
    ∀ (k : Fin n) (h : (k : ℕ) + 1 < n), p ⟨k + 1, h⟩ = p k + 1 ∨ p ⟨k + 1, h⟩ + 1 = p k

end CollectiveDFS


