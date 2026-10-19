-- Prove2me | Definitions.Def_QAlgorithms_Defs_LinearSystemTargets
-- name    : QAlgorithms_Defs_LinearSystemTargets
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:16.735471+00:00
-- url     : https://prove2.me/theorems/7a86abb1-2c1b-4b76-975d-a3cd492f1bbe
-- title:
--   LinearSystemTargets
-- statement:
--   LinearSystemTargets
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LinearSystemTargets.lean

import Definitions.Def_QAlgorithms_Defs_LinearSystems
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms

/-- QAlgorithms.linearSystemSolution: arxiv-1511.02306v2 PDF p.3, arxiv-1909.05500v3 PDF p.3, arxiv-2609.35660v1 PDF p.1. Source domains are explicit below. -/
def linearSystemSolution {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (invertible : IsUnit A) (b : EuclideanSpace ℂ (Fin N)) (nonzero : b ≠ 0) :
    EuclideanSpace ℂ (Fin N) := normalizedVec (act A⁻¹ b)

example {N : ℕ} (hN : 0 < N) (b : EuclideanSpace ℂ (Fin N)) (hb : b ≠ 0) :
    linearSystemSolution hN 1 isUnit_one b hb = normalizedVec b := by
  simp [linearSystemSolution, act]

end QAlgorithms


