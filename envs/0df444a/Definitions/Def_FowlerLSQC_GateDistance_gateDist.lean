-- Prove2me | Definitions.Def_FowlerLSQC_GateDistance_gateDist
-- name    : FowlerLSQC_GateDistance_gateDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:26.62097+00:00
-- url     : https://prove2.me/theorems/1b3b2bb0-f8f8-43b7-9b29-cb4827ada775
-- title:
--   Gate distance (10.1): $\mathrm{dist}(U,V)=\sqrt{(m-|\mathrm{tr}(U^\dagger V)|)/m}$
-- statement:
--   Let $U(m)$ denote the group of $m\times m$ complex unitary matrices. For $U,V\in U(m)$, the **gate distance** is
--
--   $$
--   \mathrm{dist}(U,V)=\sqrt{\frac{m-\left|\mathrm{tr}(U^\dagger V)\right|}{m}},
--   $$
--
--   where $U^\dagger$ is the conjugate transpose of $U$ and $|\cdot|$ is the modulus of a complex number.
--
--   The distance measures how far $U^\dagger V$ is from a scalar multiple of the identity. Fowler uses it as the objective when searching for the sequence of fault-tolerant gates that best approximates a given gate.
--
--   **Formalization Note** $U(m)$ is `Matrix.unitaryGroup (Fin m) ℂ`. The definition does not build in nonnegativity of the radicand: that is the separate theorem `radicand_bounds`. At $m=0$, where the formula reads $0/0$, the Lean value is $0$; every theorem of the mission assumes $m\ge 1$.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.1, (10.1), p.110 (PDF 128)

import Mathlib

open scoped Matrix

namespace FowlerLSQC.GateDistance

/-- The phase-insensitive gate distance of Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, §10.1, (10.1), p.110 (PDF 128): for `U, V ∈ U(m)`,
`dist(U, V) = sqrt((m − |tr(U†V)|) / m)`. The book writes the second argument as `U_l`, a gate
sequence in `U(m)`, and uses `dist(U, V)` for any two elements in (10.2).

**Formalization Note** `U(m)` is `Matrix.unitaryGroup (Fin m) ℂ`, `U†` is the conjugate transpose
`Uᴴ`, and `|·|` is the norm of `ℂ`. No nonnegativity is built in: that the radicand lies in
`[0, 1]` is the separate theorem `radicand_bounds`, so `Real.sqrt` never truncates when `m ≥ 1`.
At `m = 0`, where (10.1) reads 0/0, the Lean value is the junk value `0`; every theorem of this
mission assumes `0 < m`. -/
noncomputable def gateDist {m : ℕ} (U V : Matrix.unitaryGroup (Fin m) ℂ) : ℝ :=
  Real.sqrt
    (((m : ℝ) - ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖) /
      (m : ℝ))

end FowlerLSQC.GateDistance


