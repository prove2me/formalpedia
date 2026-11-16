-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_opSqrt
-- name    : OptGaussTomo_Supplement_opSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:43:02.262984+00:00
-- url     : https://prove2.me/theorems/6585ec01-c0b5-4724-b41b-5359d8dd256e
-- title:
--   Positive square root $\sqrt M$ of a positive operator
-- statement:
--   For a positive operator $M$ on $\ell^2(X)$, its **positive square root** $\sqrt M$ is the unique positive bounded operator $S$ with $S^2=M$, i.e.
--
--   $$
--   \sum_k S_{ik}S_{kj}=M_{ij}\qquad\text{for all } i,j .
--   $$
--
--   It enters the standard purification $|\psi^{\mathrm{std}}_\rho\rangle=\sum_x\sqrt\rho|x\rangle\otimes|\tilde x\rangle$ and the operators $\sqrt{\mathcal P_{\mathcal A}[Q_k]}$ of (E.7).
--
--   **Formalization Note** $\sqrt M$ is chosen among all $S$ with this property (there is exactly one when $M$ is positive); on a non-positive $M$, which no statement evaluates, the value is $0$.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), App. E.1, p.62 (standard purification) and Theorem E.1, eq. (E.7), p.64

import Mathlib
import Definitions.Def_OptGaussTomo_Supplement_mulOp

namespace OptGaussTomo.Supplement

/-- `S` is a **positive square root** of `M` (Chen, Fanizza, Girardi, Lami, Mele, Walter,
Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held
version, sha256 0f7548a2…, App. E.1, pp.62–64): `S` is a positive bounded operator and
`∑ₖ S i k S k j = M i j` for all `i, j` (the series converging). -/
def IsPosSqrt {X : Type} (S M : Matrix X X ℂ) : Prop :=
  IsPosCoeff S ∧ IsBoundedCoeff S ∧ ∀ i j, HasSum (fun k => S i k * S k j) (M i j)

/-- The **positive square root** `√M` of a positive operator `M` (used for `√ρ` in the standard
purification, p.62, and for `√(P_A[Q_k])` in (E.7), p.64).

**Formalization Note.** A positive bounded operator has exactly one positive bounded square root,
so `√M` is chosen as any `S` with `IsPosSqrt S M`; when `M` has none (it is not positive) the value
`0` is a placeholder that no statement of this mission evaluates. -/
noncomputable def opSqrt {X : Type} (M : Matrix X X ℂ) : Matrix X X ℂ :=
  by classical exact if h : ∃ S, IsPosSqrt S M then Classical.choose h else 0

end OptGaussTomo.Supplement


