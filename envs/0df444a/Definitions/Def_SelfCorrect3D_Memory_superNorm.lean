-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_superNorm
-- name    : SelfCorrect3D_Memory_superNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:33.302988+00:00
-- url     : https://prove2.me/theorems/0ea7fbfc-7409-4e4a-8f3a-4b179b49bf55
-- title:
--   Induced trace norm $\|\mathcal L\|_1$ of a superoperator
-- statement:
--   For a map $\mathcal T$ on $n$-qubit operators, the **trace-norm-induced norm** is
--
--   $$\|\mathcal T\|_1=\sup_{X\neq 0}\frac{\|\mathcal T(X)\|_1}{\|X\|_1}=\min\{c\ge 0:\ \|\mathcal T(X)\|_1\le c\|X\|_1\ \text{for all }X\},$$
--
--   where $\|X\|_1=\mathrm{Tr}\sqrt{X^\dagger X}$ is the trace norm. This is the norm $\|\mathcal L\|_1$ appearing in eq. (48).
--
--   **Formalization Note** Written as an infimum over admissible constants $c\ge0$, with the platform's trace norm `WildeQIT.traceNorm`. For a linear map in finite dimension the set is nonempty and closed, so the infimum is attained.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Theorem 2.6, eq. (48), p. 21

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_Op
import Definitions.Def_WildeQIT_traceNorm

namespace SelfCorrect3D.Memory

/-- **Trace-norm-induced norm of a superoperator** `‖𝓛‖₁ = sup_{X ≠ 0} ‖𝓛 X‖₁ / ‖X‖₁`, the norm
`‖𝓛‖₁` of Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, Theorem 2.6, eq. (48), p. 21.

**Formalization Note.** Written as the least `c ≥ 0` with `‖𝓛 X‖₁ ≤ c ‖X‖₁` for all `X`, with
`‖·‖₁ = WildeQIT.traceNorm` (Schatten 1-norm). For a linear map on a finite-dimensional space the
set is nonempty and closed, so the infimum is attained and equals the operator norm; it is never
the junk value of an empty set. -/
noncomputable def superNorm {n : ℕ} (L : Op n → Op n) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ X : Op n, WildeQIT.traceNorm (L X) ≤ c * WildeQIT.traceNorm X}

end SelfCorrect3D.Memory


