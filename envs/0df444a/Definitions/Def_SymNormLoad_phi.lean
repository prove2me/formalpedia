-- Prove2me | Definitions.Def_SymNormLoad_phi
-- name    : SymNormLoad_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:26.81995+00:00
-- url     : https://prove2.me/theorems/495f4cbb-bad8-47d6-af92-1f2535326e83
-- title:
--   $\varphi(k)=\Psi(\mathbf 1_k)$
-- statement:
--   For $k\in\{0,\dots,M\}$,
--   $$
--   \varphi(k)=\Psi(\mathbf 1_k),
--   $$
--   the norm of the flat vector with $k$ ones.
--
--   **Formalization Note** Defined for every natural $k$; only $k\le M$ is used.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.1, p.9

import Mathlib
import Definitions.Def_SymNormLoad_flatVec

namespace SymNormLoad

/-- **`φ(k) = Ψ(1_k)`.** Chen–Im–Sirri, *Online Load Balancing under Symmetric Norms*,
manuscript (STOC 2027 submission), §2.1.1, p.9: `φ(k) = Ψ(1_k)` for `k ∈ {0, …, M}`.

**Formalization Note** Defined for every natural `k`; only `k ≤ M` is used. -/
def phi {M : ℕ} (Ψ : (Fin M → ℝ) → ℝ) (k : ℕ) : ℝ :=
  Ψ (flatVec M k)

end SymNormLoad


