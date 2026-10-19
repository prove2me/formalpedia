-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapA12_Model
-- name    : QAlgorithms_Papers_RoadmapA12_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:48:00.251551+00:00
-- url     : https://prove2.me/theorems/603e8184-7f38-4c66-bfbc-ee3f6a7eeaea
-- title:
--   Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm, arXiv:1909.05500v3, https://arxiv.org/abs/1909.05500v3. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_AQCSchedules
noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.RoadmapA12

/-- The full-register final error in An--Lin, arXiv:1909.05500v3, PDF pp.3--5,
Theorem 1, Eq.(7). The norm is the operator 2-norm, and the target is
`|0> tensor (A^{-1}b / norm(A^{-1}b))`; its density matrix removes global phase. -/
noncomputable def finalError {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ)
    (b : EuclideanSpace ℂ (Qubits n))
    (psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n)) : ℝ :=
  specNorm (pureDensity (psi 1) -
    pureDensity (tensorVec (ket false) (normalizedVec (act A⁻¹ b))))


end QAlgorithms.Papers.RoadmapA12


