-- Prove2me | Definitions.Def_QAlgorithms_Defs_QuantumEsscherData
-- name    : QAlgorithms_Defs_QuantumEsscherData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:15.785055+00:00
-- url     : https://prove2.me/theorems/f94208be-347a-48fe-bdea-2da25e5d6894
-- title:
--   QuantumEsscherData
-- statement:
--   QuantumEsscherData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QuantumEsscherData.lean

import Definitions.Def_QAlgorithms_Defs_SDP
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.QuantumEsscher

/-- QAlgorithms.QuantumEsscher.matrixLog2: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.4, arxiv-2401.07561v2 PDF p.5. Source domains are explicit below. -/
def matrixLog2 {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (positive : rho.PosDef) : Matrix I I ℂ := cfc (Real.logb 2) rho

/-- QAlgorithms.QuantumEsscher.PublicParameters: arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
structure PublicParameters where
  d : ℕ
  d_pos : 0 < d
  theta : Fin d → ℝ
  kappa : ℝ
  kappa_gt : 1 < kappa
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < (2 : ℝ)^(-((∑ j, |theta j|)+2*(1+Real.logb 2 (2*kappa))))
  n : ℕ
  purificationAncillas : ℕ
  observableAncillas : ℕ

/-- QAlgorithms.QuantumEsscher.PublicParameters.beta: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.4, arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
def PublicParameters.beta (P : PublicParameters) : ℝ := (∑ j, |P.theta j|)+2*(1+Real.logb 2 (2*P.kappa))

/-- QAlgorithms.QuantumEsscher.PublicParameters.selectorBits: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.4, arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
def PublicParameters.selectorBits (P : PublicParameters) : ℕ := Nat.clog 2 (P.d+1)

/-- QAlgorithms.QuantumEsscher.PublicParameters.encodingError: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.4, arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
def PublicParameters.encodingError (P : PublicParameters) : ℝ := (P.eps/(8*Real.logb 2 P.eps⁻¹))^2

/-- QAlgorithms.QuantumEsscher.PublicParameters.preparationError: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.4, arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
def PublicParameters.preparationError (P : PublicParameters) : ℝ := P.beta*P.encodingError

/-- QAlgorithms.QuantumEsscher.PublicParameters.outputAncillas: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.4, arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
def PublicParameters.outputAncillas (P : PublicParameters) : ℕ :=
  max P.observableAncillas (P.n+P.purificationAncillas)+P.selectorBits+4


/-- Hidden input domain of Algorithm 1: a full-rank density with spectrum in [1/kappa,1] and
norm-bounded Hermitian observables. Source: arxiv-2401.07561v2 PDF pp.4-7. -/
structure InputData (P : PublicParameters) where
  rho : Matrix (Qubits P.n) (Qubits P.n) ℂ
  density : IsDensityMatrix rho
  positive : rho.PosDef
  spectralBounds : ∀ k, P.kappa⁻¹ ≤ ascEigenvalues rho k ∧ ascEigenvalues rho k ≤ 1
  H : Fin P.d → Matrix (Qubits P.n) (Qubits P.n) ℂ
  hermitian : ∀ j, (H j).IsHermitian
  normBound : ∀ j, specNorm (H j) ≤ 1

/-- K=sum theta_j H_j+log_2 rho, arxiv-2401.07561v2 PDF pp.4-7. -/
def generator (P : PublicParameters) (input : InputData P) : Matrix (Qubits P.n) (Qubits P.n) ℂ :=
  (∑ j, (P.theta j : ℂ) • input.H j) + matrixLog2 input.rho input.positive

/-- The proof's selected subnormalized output, exp(K)/(4 exp(beta)), arxiv-2401.07561v2 PDF pp.6-7.
Trace normalization would be the separate frozen Gibbs state and is not used here. -/
def subnormalizedTransform (P : PublicParameters) (input : InputData P) :
    Matrix (Qubits P.n) (Qubits P.n) ℂ :=
  ((4*Real.exp P.beta : ℝ) : ℂ)⁻¹ • NormedSpace.exp (generator P input)

example (P : PublicParameters) (hd : P.d = 1) : P.selectorBits = 1 := by
  simp [PublicParameters.selectorBits,hd]; decide

example (P : PublicParameters) (hd : P.d = 2) (htheta : ∀ j, P.theta j = 0) :
    P.beta = 2*(1+Real.logb 2 (2*P.kappa)) := by
  simp [PublicParameters.beta,htheta]

example (P : PublicParameters) (input : InputData P) (hd : P.d = 2)
    (htheta : ∀ j, P.theta j = 0) :
    generator P input = matrixLog2 input.rho input.positive := by
  simp [generator,htheta]
end QAlgorithms.QuantumEsscher


