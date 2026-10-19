-- Prove2me | Definitions.Def_QAlgorithms_Defs_ZYLocalCertificates
-- name    : QAlgorithms_Defs_ZYLocalCertificates
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:45:51.03268+00:00
-- url     : https://prove2.me/theorems/3964917a-6dd2-4756-afb5-c05a4ab4d537
-- title:
--   ZYLocalCertificates
-- statement:
--   ZYLocalCertificates
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ZYLocalCertificates.lean

import Definitions.Def_QAlgorithms_Defs_ZYCircuits
import Definitions.Def_QAlgorithms_Defs_ZYLightconeConstruction
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ZY

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {O : Orientation G}

/-- For an ansatz on G define α₀(G)=max_θ L₀(θ)/C_max(G), with attained continuous periodic optimization. Define the source's worst-case α₀ as infimum over the explicitly specified nonempty class of graphs with that ansatz policy/source-count regime. This is an approximate analysis quantity, not the actual Born expectation of the whole circuit. Source: arxiv-2504.12896v4 PDF p.4. -/
def localApproximationRatio (seq : GateSequence O) (_nonzero : 0 < maximumCut G) : ℝ :=
  sSup ((fun theta => localCut seq theta/(maximumCut G : ℝ)) '' Set.Icc (0 : ℝ) (2*Real.pi))

/-- Implementation helper; source: arxiv-2504.12896v4 PDF p.4. -/
structure CubicAnsatz where
  N : ℕ
  nonempty : 0 < N
  G : SimpleGraph (Fin N)
  connected : G.Connected
  cubic : ∀ v, (Finset.univ.filter fun u => G.Adj v u).card = 3
  orientation : Orientation G
  sequence : GateSequence orientation
  positiveCut : 0 < @maximumCut N G (Classical.decRel _)

/-- For an ansatz on G define α₀(G)=max_θ L₀(θ)/C_max(G), with attained continuous periodic optimization. Define the source's worst-case α₀ as infimum over the explicitly specified nonempty class of graphs with that ansatz policy/source-count regime. This is an approximate analysis quantity, not the actual Born expectation of the whole circuit. Source: arxiv-2504.12896v4 PDF p.4. -/
def worstCaseLocalRatio (ansatzClass : CubicAnsatz → Prop)
    (_nonempty : ∃ A : CubicAnsatz, ansatzClass A) : ℝ :=
  sInf {v | ∃ A : CubicAnsatz, ansatzClass A ∧
    v = @localApproximationRatio A.N A.G (Classical.decRel _) A.orientation A.sequence A.positiveCut}

/-- b₀(G,A)=max_θ L₀(G,A;θ)/M, M>0, which becomes (D3) after stating the edge calculation. This is the lower bound being optimized over orientations/orders. State b₀≤α₀ using C_max≤M, not α₀=b₀. Source: arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.22. -/
def edgeCountCertificate (seq : GateSequence O) (_positive : 0 < seq.edges.length) : ℝ :=
  sSup ((fun theta => localCut seq theta/(seq.edges.length : ℝ)) '' Set.Icc (0 : ℝ) (2*Real.pi))

/-- k(N,NPlus)=2/3+4 NPlus/(3N), real casts with N>0. Source: arxiv-2504.12896v4 PDF p.5; arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.22. -/
def sourceDensityCoefficient (N sources : ℕ) (_hN : 0 < N) : ℝ :=
  2/3+4*(sources : ℝ)/(3*N)

/-- Attained max over theta in [0,pi/2] of (1+(1-k)sin(theta)+k cos(theta)sin(theta))/2. No rounded decimal; compact continuity supplies attainment. Source: arxiv-2504.12896v4 PDF p.5; arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.22. -/
def scalarEnvelope (k : ℝ) : ℝ :=
  sSup ((fun theta => (1+(1-k)*Real.sin theta+k*Real.cos theta*Real.sin theta)/2) ''
    Set.Icc (0 : ℝ) (Real.pi/2))

example (N : ℕ) (hN : 0 < N) : sourceDensityCoefficient N 0 hN = 2/3 := by
  simp [sourceDensityCoefficient]

end QAlgorithms.ZY


