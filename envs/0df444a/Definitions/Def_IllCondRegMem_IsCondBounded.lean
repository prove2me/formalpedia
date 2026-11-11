-- Prove2me | Definitions.Def_IllCondRegMem_IsCondBounded
-- name    : IllCondRegMem_IsCondBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:47.344047+00:00
-- url     : https://prove2.me/theorems/e1cfd6ec-13b2-4490-8ea7-3cfcfce23351
-- title:
--   $\kappa$-conditioned covariance matrices
-- statement:
--   A real symmetric $d\times d$ matrix $\Sigma$ is **$\kappa$-conditioned** when it is positive definite and its condition number is at most $\kappa$:
--   $$
--   \lambda_{\max}(\Sigma)\le\kappa\,\lambda_{\min}(\Sigma),
--   $$
--   equivalently, there is a scale $s>0$ with $s I\preceq\Sigma\preceq\kappa s I$ in the Loewner order.
--
--   Theorem 1 constrains the adversary only through this condition, with $\kappa=d^{12}\log d$.
--
--   **Formalization Note** The two Loewner inequalities are written as positive semidefiniteness of $\Sigma-sI$ and $\kappa sI-\Sigma$ (`Matrix.PosSemidef`, which includes symmetry).
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Theorem 1, p.3 (PDF p.4); §6.3, p.36 (PDF p.37)

import Mathlib

namespace IllCondRegMem

/-- **κ-conditioned covariance matrix.**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Theorem 1,
p.3 ("κ = d¹² log d-conditioned covariance matrices Σ_t") and §6.3, p.36 ("its condition
number is bounded by κ = 1/(ρλ²)").

`IsCondBounded κ S` says that `S` is positive definite with condition number at most `κ`:
there is a scale `s > 0` with `s·I ⪯ S ⪯ κ·s·I` in the Loewner order, i.e.
`λ_max(S) ≤ κ · λ_min(S)`.

**Formalization Note.** The Loewner inequalities are written with `Matrix.PosSemidef`, which
includes symmetry, so `S` is symmetric. -/
def IsCondBounded {d : ℕ} (κ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ (S - s • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    ((κ * s) • (1 : Matrix (Fin d) (Fin d) ℝ) - S).PosSemidef

end IllCondRegMem


