-- Prove2me | Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
-- name    : QAlgorithms_Defs_QuantumOutputMetrics
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:18.712214+00:00
-- url     : https://prove2.me/theorems/af4e0fab-d740-4b9e-b753-8240a8c7997c
-- title:
--   QuantumOutputMetrics
-- statement:
--   QuantumOutputMetrics
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QuantumOutputMetrics.lean

import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms

/-- QAlgorithms.traceDistance: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
def traceDistance {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ := 2⁻¹ * traceNorm (rho-sigma)

/-- QAlgorithms.buresWassersteinDistance: arxiv-2212.03544v2 PDF p.16, arxiv-2212.03544v2 PDF p.17, arxiv-2212.03544v2 PDF p.18, arxiv-2212.03544v2 PDF p.20. Source domains are explicit below. -/
def buresWassersteinDistance {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) : ℝ :=
  Real.sqrt (rho.trace.re+sigma.trace.re-2*rootFidelity rho sigma)

/-- Positivity of an unnormalized pure density; arxiv-2212.03544v2 PDF p.16, equation (78). -/
theorem pureDensity_posSemidef {I : Type*} [Fintype I] (psi : EuclideanSpace ℂ I) :
    (pureDensity psi).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp psi)

example {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    traceDistance rho rho = 0 := by simp [traceDistance, traceNorm, cfc_zero]

example {I : Type*} [Fintype I] [DecidableEq I] :
    buresWassersteinDistance (0 : Matrix I I ℂ) 0 Matrix.PosSemidef.zero
      Matrix.PosSemidef.zero = 0 := by
  simp [buresWassersteinDistance, rootFidelity, cfc_zero]



end QAlgorithms


