-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
-- name    : LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:34:45.701954+00:00
-- url     : https://prove2.me/theorems/5981d7b9-22d8-4173-9d44-a36df264d10d
-- title:
--   LIDT definitions: LDT / Test / SchwartzZippelStep
-- statement:
--   This bundle isolates the algebraic expansion used in the fifth step of the formal main theorem. It separates evaluated answer collisions from distinct polynomial outcomes and records the resulting consistency comparison with its collision correction.
--
--   Principal definitions:
--   - `localCollisionMass`: the mass of unequal polynomial outcomes that agree after evaluation at the sampled point.
--   - `MainFormalStep5ExpansionBound`: the inequality comparing constant-polynomial consistency with point-evaluation consistency plus the polynomial collision mass.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/SchwartzZippelStep.lean#L91-L237

-- Generated from MIPStarRE/LDT/Test/SchwartzZippelStep.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test



open Classical in
 noncomputable def localCollisionMass
    {α β ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) : Error :=
  ∑ aa : α × α,
    (if aa.1 = aa.2 then 0 else if f aa.1 = f aa.2 then (1 : Error) else 0) *
      ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))







/-- The exact algebraic expansion/reindexing statement used in `mainFormal` Step 5.

Paper origin: `references/ldt-paper/inductive_step.tex:119-130`
(`\label{eq:G-self-consistency}`), with the collision estimate supplied by the
Schwartz--Zippel lemma.

Paper lines 119--128 compare the evaluated consistency defect

`E_u ∑_{a ≠ b} ⟨ψ| G^A_[g(u)=a] ⊗ G^B_[h(u)=b] |ψ⟩`

with the full-polynomial consistency defect

`∑_{g ≠ h} ⟨ψ| G^A_g ⊗ G^B_h |ψ⟩`.

The paper reuses `g` as the bound name in the Alice and Bob sums; Lean writes
these independently-bound polynomial outcomes as `g` and `h` to make the
independence explicit.

After expanding the postprocessed outcomes and separating the colliding pairs
`g(u)=h(u)`, the only extra term is the collision mass bounded by
Schwartz--Zippel in `Preliminaries.polynomialCollisionMass_le_mdq`.  This
predicate records precisely that expansion step, without bundling the
Schwartz--Zippel estimate itself into an unproved hypothesis. -/
def MainFormalStep5ExpansionBound
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB))
    (Left : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    Prop :=
  bipartiteConsError ψ (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right) ≤
    bipartiteConsError ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) +
    Preliminaries.polynomialCollisionMass params ψ Left Right







end Test

end MIPStarRE.LDT

end

end LIDT


