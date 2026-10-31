-- Prove2me | Definitions.Def_OAIQ11Fg010
-- name    : OAIQ11Fg010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:41:39.859583+00:00
-- url     : https://prove2.me/theorems/22076dda-dacd-46bd-9cfd-5e45fcdf5abe
-- title:
--   Definitions bundle OAIQ11Fg010 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 10 definitions, 1 instance and 9 theorems. The definitions and types are `OAI.Generator.Tracial.includedUnitPartition`, `OAI.Generator.Tracial.norm₁`, `OAI.Generator.Tracial.relativeUnitaryWord`, `OAI.Generator.Tracial.residualCorner`, `OAI.Generator.Tracial.traceFunctionalSlice`, `OAI.Generator.Tracial.traceOrbitHull`, `OAI.Generator.Tracial.unitResidual`, `OAI.Generator.finitePerturbationRows`, `OAI.Generator.prefixLetterSupport`, `OAI.Generator.prefixWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Convolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Convolution.lean), [`FactorGeneration_CornerTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CornerTrace.lean), [`FactorGeneration_HilbertLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HilbertLimits.lean), [`FactorGeneration_LongWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LongWords.lean), [`FactorGeneration_RelativeGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RelativeGeneration.lean), [`FactorGeneration_ResidualEstimates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualEstimates.lean), [`FactorGeneration_SpectralApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralApproximation.lean), [`FactorGeneration_SpectralTruncation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralTruncation.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`FactorGeneration_TraceTopology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTopology.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg003`, `OAIQ11Fg004`, `OAIQ11Fg005` and `OAIQ11Fg006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg012` and `OAIQ11Fg014`; the statements `OAI.Generator.Tracial.exists_unitResidual_local_compression` and `OAI_Generator_Tracial_representedCorner_diffuse`; the proofs of `OAI.Generator.FiniteMatrixStage.generated_isII1`, `OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra`, `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget` and `OAI.Generator.Tracial.exists_matrixUnits_for_partition`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg003
import Definitions.Def_OAIQ11Fg004
import Definitions.Def_OAIQ11Fg005
import Definitions.Def_OAIQ11Fg006

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Convolution
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

def prefixLetterSupport (n : ℕ) : Finset (Letter (FreeGroup ℕ)) :=
  (ratioLabels n).product Finset.univ

def prefixWeight (n : ℕ) (α : ℝ) (a : Letter (FreeGroup ℕ)) : ℝ :=
  α / (2 * n) * multiplicity n a.1

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def traceOrbitHull (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) : Set H :=
  closure (convexHull ℝ (baseVector τ '' algebraOrbit G b))

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (τ : TracialRepresentation M)

def norm₁ (x : M.toStarSubalgebra) : ℝ := (τ.trace (traceAbs x)).re

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def traceFunctionalSlice (f : M.toStarSubalgebra →L[ℝ] ℝ) (r : ℝ) : Set H :=
  {ξ | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ 1 ∧ f a ≤ r ∧ a.val τ.vector = ξ}

end Tracial

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/
section
open scoped BigOperators
open Generator.CoefficientOrder
variable {G : Type*} [Monoid G]

@[simp] theorem normCoefficients_zero : normCoefficients (0 : MonoidAlgebra ℂ G) = 0 := by
  ext w; simp

@[simp] theorem normCoefficients_one : normCoefficients (1 : MonoidAlgebra ℂ G) = 1 := by
  classical
  ext w
  simp only [normCoefficients_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs <;> norm_num

omit [Monoid G] in
@[simp] theorem normCoefficients_single (g : G) (c : ℂ) :
    normCoefficients (MonoidAlgebra.single g c) = MonoidAlgebra.single g ‖c‖ := by
  classical
  ext w
  simp only [normCoefficients_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

end

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ

local instance instDecidableEqFreeGroupNat_solutions_3_re9a8ce_1 : DecidableEq G := Classical.decEq _
def finitePerturbationRows (n : ℕ) (α : ℝ) :=
  List.ofFn (finitePerturbationRow (n := n) α)

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def includedUnitPartition (h : N ≤ M) (Q : CornerPartition (identityProjection N)) :
    CornerPartition (identityProjection M) where
  size := Q.size
  piece i := includedProjection h (Q.piece i)
  orthogonal i j hij := by
    change algebraInclusion h (Q.piece i).val * algebraInclusion h (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,algebraInclusion h (Q.piece i).val)=1
    rw [← map_sum,Q.total]
    exact map_one (algebraInclusion h)

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

attribute [local instance] OAI.Generator.Tracial.clippingCStar
local instance clippingOrder_re9a8ce_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance clippingStarOrder_re9a8ce_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceSymmetrize_selfAdjoint (a : M.toStarSubalgebra) : IsSelfAdjoint (traceSymmetrize a) := by
  change star ((2 : ℂ)⁻¹ • (a+star a)) = (2 : ℂ)⁻¹ • (a+star a)
  simp [add_comm]

theorem traceSymmetrize_eq_self (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    traceSymmetrize a = a := by
  simp only [traceSymmetrize,ha.star_eq,← two_smul ℂ a,smul_smul]
  norm_num

theorem traceSymmetrize_sub (a b : M.toStarSubalgebra) :
    traceSymmetrize (a-b) = traceSymmetrize a-traceSymmetrize b := by
  simp only [traceSymmetrize,star_sub,smul_add,smul_sub]
  abel

theorem traceSymmetrize_norm₂_le (τ : TracialRepresentation M) (a : M.toStarSubalgebra) :
    τ.norm₂ (traceSymmetrize a) ≤ τ.norm₂ a := by
  rw [traceSymmetrize,τ.norm₂_smul,norm_inv]
  norm_num only [Complex.norm_ofNat]
  have h := τ.norm₂_add_le a (star a)
  rw [τ.norm₂_star] at h
  linarith

theorem traceClip_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    traceClip a C = cfc (fun t : ℝ => -min (-min t C) C) a := by
  rw [traceClip,upperTruncate_cfc _ (upperTruncate_selfAdjoint a ha C).neg C,
    upperTruncate_cfc a ha C,← cfc_neg (fun t : ℝ => min t C) a,
    ← cfc_comp (fun t : ℝ => min t C) (fun t : ℝ => -min t C) a]
  simp only [Function.comp_def]
  rw [cfc_neg (fun t : ℝ => min (-min t C) C) a]

theorem traceClip_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) : ‖traceClip a C‖ ≤ C := by
  rw [traceClip_cfc a ha C]
  apply norm_cfc_le hC
  intro t _
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · exact neg_le_neg (min_le_right _ _)
  · have h : -C ≤ min (-min t C) C :=
      le_min (neg_le_neg (min_le_right _ _)) (by linarith)
    linarith

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeUnitaryWord (u : TraceUnitary τ) (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    M.toStarSubalgebra :=
  coordinateInclusion hNM (t 0 : N.toStarSubalgebra)*
    ((List.range ell).map (fun j => u.algebra τ*
      coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod

end Tracial

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualEstimates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Correct residual-corner trace identity for arbitrary f. The first term
is trace(f*x), not trace(x); they agree when f=1. This is the distinction
at Popa 1308.3982v3 Lemma 3.2, equation (5). -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def residualCorner (f : AlgebraProjection M) (v : PartialUnitary M) (hv : v.support ≤ f) :
    AlgebraProjection M :=
  ⟨f.val-v.support.val,v.support.property.sub_of_mul_eq_right f.property hv⟩

end

/-! The justified f=1 scalar estimate in the support-growth argument.
Every estimate is tied to the current partial unitary's actual residual;
there is no arbitrary-corner centering assertion. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def unitResidual (v : PartialUnitary M) : AlgebraProjection M :=
  ⟨1-v.support.val,v.support.property.one_sub⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
attribute [local instance] OAI.Generator.Tracial.traceHilbertCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertOrder
attribute [local instance] OAI.Generator.Tracial.traceHilbertStarOrder
instance traceFreePreHilbertStarModule : StarModule ℂ E :=
  inferInstanceAs (StarModule ℂ M.toStarSubalgebra)

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end


