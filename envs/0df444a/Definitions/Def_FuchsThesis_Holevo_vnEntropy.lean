-- Prove2me | Definitions.Def_FuchsThesis_Holevo_vnEntropy
-- name    : FuchsThesis_Holevo_vnEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:56.811626+00:00
-- url     : https://prove2.me/theorems/3d7adbe5-91ea-4594-b776-04eb6791ff49
-- title:
--   Von Neumann entropy $S(\hat\rho)$ in nats
-- statement:
--   The von Neumann entropy of a density operator $\hat\rho$ with eigenvalues $\lambda_1,\dots,\lambda_D$ is
--
--   $$
--   S(\hat\rho) = -\mathrm{tr}(\hat\rho\ln\hat\rho) = -\sum_{j=1}^D \lambda_j\ln\lambda_j ,
--   $$
--
--   in nats, with $0\ln0=0$.
--
--   **Formalization Note** Computed from the eigenvalues with multiplicity (`eigval`) with `Real.negMulLog`. For a non-Hermitian matrix the value is a junk $0$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.150), p.66 (PDF p.75)

import Mathlib
import Definitions.Def_FuchsThesis_Holevo_eigval

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.150), p.66 (PDF p.75): the von Neumann entropy of a
density operator with eigenvalues `λ_j`,
`S(ρ̂) = −tr(ρ̂ ln ρ̂) = −∑_{j=1}^D λ_j ln λ_j`, in nats.

**Formalization Note.** `Real.negMulLog x = −x ln x` with `0 ln 0 = 0`; eigenvalues with
multiplicity (`FuchsThesis.Holevo.eigval`). For a non-Hermitian matrix the value is the junk `0`. -/
noncomputable def vnEntropy {d : Type} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : ℝ :=
  ∑ j, Real.negMulLog (eigval ρ j)

end FuchsThesis.Holevo


