-- Prove2me | Definitions.Def_KnownFidelity_Rank_fid
-- name    : KnownFidelity_Rank_fid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:42.557341+00:00
-- url     : https://prove2.me/theorems/71951286-d4be-4ff2-864d-7975d4125310
-- title:
--   Root fidelity $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1=\mathrm{tr}\sqrt{\sqrt\sigma\rho\sqrt\sigma}$
-- statement:
--   The **root fidelity** between a state $\rho$ and a reference $\sigma$ is
--
--   $$F(\rho,\sigma)=\big\|\sqrt\rho\sqrt\sigma\big\|_1=\mathrm{tr}\sqrt{\sqrt\sigma\,\rho\,\sqrt\sigma}.$$
--
--   The same formula is used for positive semidefinite operators of arbitrary trace. It is the quantity the estimators of the paper estimate to additive error $\varepsilon$.
--
--   **Formalization Note** The value is the platform's `QAlgorithms.rootFidelity σ ρ` (reference in the first slot, i.e. the second formula above), the real part of the trace, with square roots `cfc Real.sqrt`.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1 (unnumbered), p. 1 (PDF p. 3), and §2.1, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

namespace KnownFidelity.Rank

/-- **Root fidelity** `F(ρ, σ) = ‖√ρ √σ‖₁ = tr √(√σ ρ √σ)`.
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1 (unnumbered), printed p. 1 (PDF p. 3): "We use the root-fidelity convention
F(ρ, σ) = ∥√ρ√σ∥1 = tr √(√σρ√σ)", and §2.1, printed p. 4 (PDF p. 6): "We use the same
root-fidelity formula F(R, S) = tr √(√S R √S) for positive semidefinite operators of arbitrary
trace".

**Formalization Note.** The value is the platform's `QAlgorithms.rootFidelity σ ρ`
`= Re tr √(√σ ρ √σ)` with the reference `σ` in the first slot, i.e. the second formula of the
page; square roots are `cfc Real.sqrt`. It is defined for every pair of square matrices, as §2.1
uses it for positive semidefinite operators of arbitrary trace. -/
noncomputable def fid {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  QAlgorithms.rootFidelity σ ρ

end KnownFidelity.Rank


