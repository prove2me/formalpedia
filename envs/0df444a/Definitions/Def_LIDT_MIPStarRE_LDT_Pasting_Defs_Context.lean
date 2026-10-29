-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Context
-- name    : LIDT_MIPStarRE_LDT_Pasting_Defs_Context
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:42:32.20855+00:00
-- url     : https://prove2.me/theorems/7233e84f-5b02-4a5d-8732-94b9951ad428
-- title:
--   LIDT definitions: LDT / Pasting / Defs / Context
-- statement:
--   This bundle records the standing nontrivial-regime data for the LdPasting argument. It packages the parameter and strategy context that the pasting theorem assumes before its analytic reductions begin.
--
--   Principal definitions:
--   - `LdPastingNontrivialContext`: the nontrivial-regime context for the LdPasting construction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Defs/Context.lean#L37-L99

-- Generated from MIPStarRE/LDT/Pasting/Defs/Context.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 12 — Nontrivial pasting context

First-class Lean bundle for the nontrivial-regime standing context used in
the proof of `thm:ld-pasting` (`def:ld-pasting-context` in the blueprint).

The paper theorem is unrestricted.  Immediately after the statement, the
paper observes that the proof may restrict to the nontrivial regime in which
the small parameters and `d/q` are at most `1`; the complementary cases are
now fully discharged in `Pasting/Bernoulli/Final.lean` (the unrestricted
`ldPasting`).  This context records the data and additional nontrivial-regime
hypotheses used by the restricted Lean theorem
`ldPastingNontrivial` and the downstream Section 12 lemmas.

This file only introduces the carrier and re-exposes the paper's standing
`ν` / `σ` abbreviations on top of it. It performs no proof work: all
downstream theorems are re-stated in later modules.

## References

- `references/ldt-paper/ld-pasting.tex` (Section 12, `thm:ld-pasting`)
- `blueprint/src/chapter/ch09_pasting.tex` (`def:ld-pasting-context`)
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT

/-- The nontrivial-regime standing context used in the proof of `thm:ld-pasting`.

This bundle records, for a fixed outcome type `ι` and fixed ambient parameters
`params` (interpreted as the slice dimension `m`), all of the data and
hypotheses threaded through the restricted theorem `ldPastingNontrivial`, its
sub-measurement variant, and the Section 12 pasting lemmas:

* an `(ε,δ,γ)`-good symmetric strategy at dimension `m+1`;
* a slice-indexed projective submeasurement family `{G^x}_{x ∈ 𝔽_q}`
  in `polysub{m}{q}{d}` together with completeness `κ`, point-consistency
  `ζ`, strong self-consistency, and the averaged boundedness input;
* the nontrivial-regime low-degree inequality `d ≤ q` and strict positivity
  `0 < d` used in the downstream sandwich and H-consistency calculations;
* the pasting iteration count `k ≥ 400md`, including the `1 ≤ k`
  positivity needed by the Bernoulli tail recurrence.

The derived error abbreviations `ν` and `σ` from the paper are provided via
`LdPastingNontrivialContext.nu` / `LdPastingNontrivialContext.sigma`.

This structure is not the unrestricted public theorem context for
`thm:ld-pasting`.  The source-facing theorem remains `ldPasting`; the
restriction to the nontrivial regime is a proof-stage reduction.
-/
structure LdPastingNontrivialContext (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The `(ε,δ,γ)`-good symmetric strategy at dimension `m+1`. -/
  strategy : SymStrat params.next ι
  /-- Axis-parallel-line error parameter `ε`. -/
  eps : Error
  /-- Point self-consistency error parameter `δ`. -/
  delta : Error
  /-- Diagonal-line error parameter `γ`. -/
  gamma : Error
  /-- Averaged completeness parameter `κ`. -/
  kappa : Error
  /-- Averaged self-improvement / pasting interface parameter `ζ`. -/
  zeta : Error
  /-- `(ε,δ,γ)`-goodness of the symmetric strategy. -/
  good : strategy.IsGood eps delta gamma
  /-- Small-parameter hypothesis `γ ≤ 1` used throughout Section 12. -/
  gamma_le_one : gamma ≤ 1
  /-- Small-parameter hypothesis `ζ ≤ 1` used throughout Section 12. -/
  zeta_le_one : zeta ≤ 1
  /-- Source-style low-degree inequality `d ≤ q`. -/
  dq_le_q : params.d ≤ params.q
  /-- Strict positivity `0 < d` required by the sandwich lemmas. -/
  d_pos : 0 < params.d
  /-- The slice-indexed polynomial family `{G^x}_{x ∈ 𝔽_q}`. -/
  family : IdxPolyFamily params ι
  /-- Averaged completeness of the slice family (`item:ld-pasting-completeness`). -/
  complete : family.Complete strategy.state kappa
  /-- Averaged point-consistency (`item:ld-pasting-consistency`). -/
  consistent : family.ConsistentWithPoints strategy zeta
  /-- Averaged strong self-consistency (`item:ld-pasting-self-consistency`). -/
  selfConsistent : family.StronglySelfConsistent strategy.state zeta
  /-- Averaged boundedness input (`item:ld-pasting-boundedness`). -/
  bounded : IdxPolyFamily.SliceBoundednessInput strategy family zeta
  /-- Pasting iteration count `k`. -/
  k : ℕ
  /-- Positivity of the iteration count. -/
  hk_pos : 1 ≤ k
  /-- Lower bound `k ≥ 400md` from the theorem statement. -/
  hk : 400 * params.m * params.d ≤ k

namespace LdPastingNontrivialContext

variable {params : Parameters} [FieldModel params.q]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





end LdPastingNontrivialContext

end MIPStarRE.LDT.Pasting

end

end LIDT


