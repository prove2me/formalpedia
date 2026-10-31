-- Prove2me | Definitions.Def_FuchsThesis_Broadcast_operatorM
-- name    : FuchsThesis_Broadcast_operatorM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:19.754285+00:00
-- url     : https://prove2.me/theorems/863e5011-dbf8-4a4e-97f8-7de68ad99058
-- title:
--   The operator $M = \rho_1^{-1/2}\sqrt{\rho_1^{1/2}\rho_0\rho_1^{1/2}}\,\rho_1^{-1/2}$ (eq. 4.72)
-- statement:
--   For density operators $\rho_0, \rho_1$ with $\rho_1$ invertible, define
--
--   $$
--   M = \rho_1^{-1/2} \sqrt{\rho_1^{1/2}\rho_0\,\rho_1^{1/2}}\; \rho_1^{-1/2},
--   $$
--
--   where $O^{1/2} = \sqrt{O}$ denotes the unique positive square root of a positive operator $O$ and $\rho_1^{-1/2}$ is the inverse of $\rho_1^{1/2}$.
--
--   $M$ is a positive operator. Its eigenbasis gives an optimal measurement for distinguishing $\rho_0$ from $\rho_1$, and in the no-broadcasting proof it is the unique positive solution $G$ of $\rho_0 = G\rho_1 G$.
--
--   **Formalization Note** Square roots are Mathlib's positive square root and $\rho_1^{-1/2}$ is the matrix inverse of $\rho_1^{1/2}$. The source uses $M$ only for invertible $\rho_1$; for singular $\rho_1$ Lean's matrix inverse is $0$, so the expression is $0$ there and every statement about $M$ assumes $\rho_1$ positive definite.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eq. (4.72), p.116 (PDF p.125)

import Mathlib

open scoped MatrixOrder

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.72), p.116 (PDF p.125): for invertible `ρ₁` the positive
operator
`M = ρ₁^{−1/2} √(ρ₁^{1/2} ρ₀ ρ₁^{1/2}) ρ₁^{−1/2}`.

**Formalization Note.** `√·` and `ρ₁^{1/2}` are Mathlib's positive square root `CFC.sqrt`;
`ρ₁^{−1/2}` is the matrix inverse `(CFC.sqrt ρ₁)⁻¹`. The source uses `M` only for invertible
`ρ₁`; on a singular `ρ₁` Lean's matrix inverse is `0` and the expression is `0`, so every statement
about `M` assumes `ρ₁` positive definite. -/
noncomputable def operatorM {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (CFC.sqrt ρ1)⁻¹ * CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) * (CFC.sqrt ρ1)⁻¹

end FuchsThesis.Broadcast


