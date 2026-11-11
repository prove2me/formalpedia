-- Prove2me | Definitions.Def_QDSGibbs_traceNorm
-- name    : QDSGibbs_traceNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:17.292381+00:00
-- url     : https://prove2.me/theorems/4e9dc903-719a-49fd-8425-a95c2c876e17
-- title:
--   Operator norm, trace norm, states, and the trace norm of a partial trace
-- statement:
--   For a square complex matrix $A$, the **operator norm** $\|A\|$ is its norm as a linear map on the Euclidean space, and the **trace norm** is
--
--   $$
--   \|X\|_1=\mathrm{Tr}\sqrt{X^*X}.
--   $$
--
--   A **state** is a positive semidefinite operator of trace one. For a region $S$, $\|\mathrm{Tr}_S Y\|_1=\|\mathrm{ptr}_S Y\|_1/\dim\mathcal H_S$, since tensoring with $\mathbb 1_S$ multiplies the trace norm by $\dim\mathcal H_S$.
--
--   These are the norms in which every estimate of the paper is stated.
--
--   **Formalization Note** The operator norm is the spectral norm (`Matrix.toEuclideanCLM`), not Mathlib's default entrywise matrix norm. The square root is the continuous functional calculus, the same formula as the platform's `QAlgorithms.traceNorm`.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §2.1, p.10; §2.2, p.12; (2.13)–(2.14), pp.13–14

import Mathlib
import Definitions.Def_QDSGibbs_Op

open scoped Matrix ComplexOrder

namespace QDSGibbs

/-- The **operator norm** `‖A‖` (arXiv:2610.03578, held file sha256 ede55815…, §2.2, p.12): the norm
of `A` as a continuous linear map on the Euclidean space `ℂ^n`.

**Formalization Note** This is the spectral norm, not Mathlib's default (entrywise) matrix norm. -/
noncomputable def opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A‖

/-- The **trace norm** `‖X‖₁ = Tr √(X*X)` (arXiv:2610.03578, §2.2, p.12).

**Formalization Note** The square root is the continuous functional calculus of the positive
semidefinite matrix `Xᴴ X`; this is the same formula as the platform's `QAlgorithms.traceNorm`. -/
noncomputable def traceNorm {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) : ℝ :=
  (cfc Real.sqrt (Xᴴ * X)).trace.re

/-- A **state** (density matrix): a positive semidefinite operator of trace one (arXiv:2610.03578,
§2.1, p.10). -/
def IsState {n : Type} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The trace norm of the partial trace, `‖Tr_S Y‖₁` (arXiv:2610.03578, (2.13)–(2.14), pp.13–14).

**Formalization Note** `Tr_S Y` lives on `H_{S^c}`; since `ptr S Y = 1_S ⊗ Tr_S Y` and
`‖1_S ⊗ Z‖₁ = dim H_S · ‖Z‖₁`, the value is `traceNorm (ptr S Y) / dim H_S`. -/
noncomputable def ptrNorm {N : ℕ} {d : Fin N → ℕ} (S : Finset (Fin N)) (Y : Op d) : ℝ :=
  traceNorm (ptr S Y) / (dimOf d S : ℝ)

end QDSGibbs


