-- Prove2me | Definitions.Def_QAlgorithms_Defs_JointLowRankGibbsContracts
-- name    : QAlgorithms_Defs_JointLowRankGibbsContracts
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:55.12074+00:00
-- url     : https://prove2.me/theorems/16c2618c-7746-4858-9811-e166100dceaa
-- title:
--   JointLowRankGibbsContracts
-- statement:
--   JointLowRankGibbsContracts
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\JointLowRankGibbsContracts.lean

import Definitions.Def_QAlgorithms_Defs_ElementaryRestartSampling
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open scoped ENNReal
namespace QAlgorithms.LowRankGibbs

/-- Every compatible hidden instance yields terminal mass one and a normalized averaged returned density σ with traceNorm(σ−gibbsState(−K))≤ϵ, according to the source's unhalved trace-norm calculation. Low-rank/trace hypotheses live in WeightedHamiltonianAccess. No assumed target output, perfect phase estimation, good shift, or partition estimate; no added 2/3 success condition. Source: arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.34; arxiv-1710.02581v3 PDF p.38; arxiv-1710.02581v3 PDF p.40. -/
def GibbsSamplingContract {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (eps : ℝ) : Prop :=
  0 < n ∧ K.IsHermitian ∧ 0 < eps ∧ terminationMass P O = 1 ∧
    ∃ summable : Summable (outputTerm P O), IsDensityMatrix (outputDensity P O summable) ∧
      traceNorm (outputDensity P O summable-gibbsState (-K)) ≤ eps

/-- Uniform unspecified polynomial: ∃C>0,∃q before all parameters, expected total quantum gates and D.1/D.2 calls≤C|S|(1+log n+r_K+B_K+ϵ⁻¹)^q. Preserve linear |S| and deduce Φ only using |S|≤Φ. This supplies operational T_Gibbs rather than an unconstrained numeric variable. No explicit exponents, worst-case runtime, additional log m or classical bit-time assertion. Source: arxiv-1710.02581v3 PDF p.22; arxiv-1710.02581v3 PDF p.26; arxiv-1710.02581v3 PDF p.38. -/
def PolynomialResourceContract {Input : Type*} (cost : Input → Fin 3 → ℝ≥0∞)
    (n support rank : Input → ℕ) (trace eps : Input → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ, ∀ input, 0 < n input → 0 < support input →
    0 ≤ trace input → 0 < eps input →
      (∑ j, cost input j) ≤ ENNReal.ofReal (C*support input*
        (1+Real.log (n input)+rank input+trace input+(eps input)⁻¹)^q)

example {a : Fin 2 → ℕ} {N n w : ℕ} (P : SamplingProgram a N n w)
    (O : (k : Fin 2) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (eps : ℝ) (h : GibbsSamplingContract P O K eps) :
    terminationMass P O = 1 := h.2.2.2.1

end QAlgorithms.LowRankGibbs


