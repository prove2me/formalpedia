-- Prove2me | Definitions.Def_OAIQ11Fg006
-- name    : OAIQ11Fg006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:32:55.210292+00:00
-- url     : https://prove2.me/theorems/6e285769-556c-455f-8c03-7fd189b75e94
-- title:
--   Definitions bundle OAIQ11Fg006 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 19 definitions and 4 theorems. The definitions and types are `OAI.Generator.Tracial.expectationPosCStar`, `OAI.Generator.Tracial.expectationPosLE`, `OAI.Generator.Tracial.expectationPosOrder`, `OAI.Generator.Tracial.traceClip`, `OAI.Generator.Tracial.traceGenerationTransportCStar`, `OAI.Generator.Tracial.traceHilbertActionCStar`, `OAI.Generator.Tracial.traceHilbertBoundCStar`, `OAI.Generator.Tracial.traceHilbertBoundLE`, `OAI.Generator.Tracial.traceHilbertBoundOrder`, `OAI.Generator.Tracial.traceHilbertBoundPreorder`, `OAI.Generator.Tracial.traceHilbertImageCStar`, `OAI.Generator.Tracial.traceHilbertRightCStar`, `OAI.Generator.Tracial.traceHilbertTransportCStar`, `OAI.Generator.Tracial.traceHilbertWOTCStar`, `OAI.Generator.Tracial.traceNormalCStar`, `OAI.Generator.Tracial.traceNormalOrder`, `OAI.Generator.Tracial.traceSubalgebraBallCStar`, `OAI.Generator.Tracial.traceSubalgebraImageCStar`, `OAI.Generator.multiplicity`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Expectations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Expectations.lean), [`FactorGeneration_FreeWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FreeWords.lean), [`FactorGeneration_GroupTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/GroupTrace.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_SpectralTruncation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralTruncation.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`FactorGeneration_TraceTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg000` and `OAIQ11Fg001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ11Fg010`; the statements `OAI_Generator_Tracial_algebraWordCore_compress`, `OAI_Generator_Tracial_algebraWordCore_support`, `OAI_Generator_Tracial_betweenWord_absorb_left`, `OAI_Generator_Tracial_cyclicPredual_separable_of_given_membership`, `OAI_Generator_Tracial_exists_admissible_family_patch`, `OAI_Generator_Tracial_exists_coordinate_monotone_upper`, `OAI_Generator_Tracial_maskPartialSequence_mem`, `OAI_Generator_Tracial_maskPartialSequence_orthogonal`, `OAI_Generator_Tracial_maskPartialSequence_quotient`, `OAI_Generator_Tracial_maskedWord_two_trace_lt`, `OAI_Generator_Tracial_quotient_ordered_moment_zero`, `OAI_Generator_Tracial_quotient_partial_core_tendsto`, `OAI_Generator_finitePerturbationRow_norm_sq` and `OAI_Generator_finite_prefix_remainder_transfer`; the proofs of `OAI_Generator_Tracial_algebraWordCore_compress`, `OAI_Generator_Tracial_algebraWordCore_support`, `OAI_Generator_Tracial_betweenWord_absorb_left`, `OAI_Generator_Tracial_cyclicPredual_separable_of_given_membership`, `OAI_Generator_Tracial_exists_coordinate_monotone_upper`, `OAI.Generator.Tracial.exists_normal_matrix_approximation`, `OAI_Generator_Tracial_maskPartialSequence_mem`, `OAI_Generator_Tracial_quotient_partial_core_tendsto` and `OAI_Generator_Tracial_traceOrbit_isSeparable_of_separablePredual`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg000
import Definitions.Def_OAIQ11Fg001

section
-- module Solutions.OAIQ11_FG.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_smul (c : ℂ) (T : Algebra (M := M)) : τ.norm₂ (c • T) = ‖c‖*τ.norm₂ T :=
  norm_smul _ _

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def traceClip (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  -upperTruncate (-upperTruncate a C) C

theorem traceClip_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (traceClip a C) :=
  (upperTruncate_selfAdjoint _ (upperTruncate_selfAdjoint a ha C).neg C).neg

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationPosCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationPosOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationPosPreorder_rf6eb28_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationPosLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/
noncomputable section
open scoped BigOperators

attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions
def multiplicity (n : ℕ) (p : FreeGroup ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun ij : Fin n × Fin n => pairRatio ij = p).card

end

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceNormalCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceNormalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceNormalPreorder_rf6eb28_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE_rf6eb28_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceNormalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertBoundCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertBoundOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertBoundPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceHilbertBoundLE : LE M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance traceHilbertBoundStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertActionCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertRightCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertWOTCStar : CStarAlgebra M.toStarSubalgebra := {}

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertImageCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertTransportCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceSubalgebraBallCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceSubalgebraImageCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Generation pullback for the actual constructed trace representation. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceGenerationTransportCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

end Generator

end

end OAI
end


