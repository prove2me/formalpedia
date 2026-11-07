-- Prove2me | Definitions.Def_FreeSpencer_IsDensity
-- name    : FreeSpencer_IsDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:14.453534+00:00
-- url     : https://prove2.me/theorems/f2d8f917-bf00-4508-a4f4-454ca9167051
-- title:
--   Densities, covariances, contraction families
-- statement:
--   A density is a positive semidefinite matrix of trace one. A covariance on $\ell$ coordinates is a matrix with $0\preceq C\preceq I_\ell$. A contraction family is a family of real symmetric matrices of operator norm at most one.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, pp.18–19

import Mathlib
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- A density: a positive semidefinite matrix of trace one. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.19. -/
def IsDensity {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) : Prop :=
  S.PosSemidef ∧ Matrix.trace S = 1

/-- A covariance: `0 ⪯ C ⪯ I_ℓ`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18. -/
def IsCov {ℓ : ℕ} (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : Prop :=
  C.PosSemidef ∧ (1 - C).PosSemidef

/-- Real symmetric contractions in the operator norm. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18
(`‖Âᵢ‖ ≤ 1`), Theorem 1.1, p.2. -/
def IsContrFam {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) : Prop :=
  ∀ i, (Ah i).IsSymm ∧ ‖Ah i‖ ≤ 1

end FreeSpencer


