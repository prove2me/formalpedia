-- Prove2me | Definitions.Def_RQCMoments_entry
-- name    : RQCMoments_entry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:08.816886+00:00
-- url     : https://prove2.me/theorems/0d3d5d41-db99-43db-b35f-85fdd98bf8b9
-- title:
--   Output probability $|\langle x|U|y\rangle|^2$ of a unitary
-- statement:
--   For a unitary $U\in U(N)$ and basis indices $x,y\in\{0,\dots,N-1\}$, the **output probability** of the entry $(x,y)$ is
--   $$
--   |\langle x|U|y\rangle|^2 = |U_{xy}|^2 ,
--   $$
--   the probability of observing the basis state $|x\rangle$ when $U$ is applied to $|y\rangle$ and the result is measured in the computational basis.
--
--   Theorem 4.9 concerns the law of this quantity when $U$ is drawn from an approximate design; Theorem 3.2 concerns sums of it over a set of rows.
--
--   **Formalization Note** Indices are `Fin N`, so the paper's $|\langle 0|U|0\rangle|^2$ is `entry 0 0`.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 4.9 and (41), p.29 and p.18 (PDF pp.31, 20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

set_option autoImplicit false

namespace RQCMoments

/-- The output probability `|⟨x|U|y⟩|²` of the entry `(x, y)` of a unitary `U ∈ U(N)`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 4.9, p.29, and (41), p.18).

**Formalization Note** Basis states are indexed by `Fin N = {0, …, N−1}`, so the paper's
`|⟨0|U|0⟩|²` is `entry 0 0`. `Complex.normSq z = |z|²`. -/
noncomputable def entry {N : ℕ} (x y : Fin N) (U : Matrix.unitaryGroup (Fin N) ℂ) : ℝ :=
  Complex.normSq ((U : Matrix (Fin N) (Fin N) ℂ) x y)

end RQCMoments


