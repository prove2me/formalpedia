-- Prove2me | Definitions.Def_OAIQ11Fg022
-- name    : OAIQ11Fg022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:29:55.356232+00:00
-- url     : https://prove2.me/theorems/21008c75-d237-4c81-94e7-6fbd463fb37e
-- title:
--   Definitions bundle OAIQ11Fg022 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 9 definitions and 3 theorems. The definitions and types are `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugateUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateConjugates`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateLabels`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.labelUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.targetUnitary`, `OAI.Generator.Tracial.conjugateVariables`, `OAI.Generator.Tracial.prefixProduct`, `OAI.Generator.Tracial.prefixVariable`, `OAI.Generator.Tracial.unitaryRepresentation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CoordinatePerturbation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean), [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_FreeGroupMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FreeGroupMoments.lean), [`FactorGeneration_HaarSequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean).
--
--   **Imports.** It imports the bundle `OAIQ11Fg015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg017`, `OAIQ11Fg025`, `OAIQ11Fg026` and `OAIQ11Fg027`; the statements `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_negative_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_positive_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_trace`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateConjugates_quotient`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.label_mem`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.target_endpoints`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.variable_endpoints`, `OAI.Generator.Tracial.conjugate_freeGroup_trace`, `OAI.Generator.Tracial.coordinateGroupRing_orthonormal`, `OAI.Generator.Tracial.successive_freeGroup_trace`, `OAI_Generator_finitePerturbationRows_degree_bound` and `OAI_Generator_rowSignedWord_injective`; the proofs of `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_negative_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_positive_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_trace`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateConjugates_quotient`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.label_mem`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.target_endpoints`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.variable_endpoints`, `OAI.Generator.Tracial.conjugate_freeGroup_trace`, `OAI.Generator.Tracial.coordinateGroupRing_orthonormal`, `OAI_Generator_Tracial_representedCorner_diffuse`, `OAI.Generator.Tracial.successive_freeGroup_trace`, `OAI_Generator_finitePerturbationRow_norm_sq`, `OAI_Generator_finitePerturbationRows_degree_bound`, `OAI_Generator_finite_prefix_remainder_transfer` and `OAI_Generator_rowSignedWord_injective`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg015

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def prefixVariable (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) : ℕ → unitary (Q τ ω)
  | 0 => t 0
  | j+1 => u*t (j+1)

def prefixProduct (u : unitary (Q τ ω)) (t : ℕ → unitary (Q τ ω)) : ℕ → unitary (Q τ ω)
  | 0 => 1
  | j+1 => prefixProduct u t j*prefixVariable τ ω u t j

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/

/-! The actual free-group representation furnished by successive Haar variables. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def unitaryRepresentation {A : Type*} (v : A → unitary (Q τ ω)) :
    FreeGroup A →* unitary (Q τ ω) := FreeGroup.lift v

end

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {A : Type*}

def conjugateVariables (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
    (a : A) : unitary (Q τ ω) := p a*y*star (p a)

end

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.labelUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (ell : ℕ) (p : PrefixLabel ell) : unitary (Q τ ω) :=
  unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) p.val

def SuccessiveCoordinateHaar.targetUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (ell : ℕ) : unitary (Q τ ω) :=
  z*(prefixProduct τ ω u (fun k => (F.step k).t) (ell+1))⁻¹

def SuccessiveCoordinateHaar.conjugateUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary (Q τ ω)) (ell : ℕ) : PrefixLabel ell → unitary (Q τ ω) :=
  conjugateVariables τ ω (F.labelUnitary τ ω u ell) (F.targetUnitary τ ω u z ell)

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.coordinateLabels (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (ell : ℕ) (p : PrefixLabel ell) : unitary (Sequences M) :=
  FreeGroup.lift (F.coordinateVariables τ ω u) p.val

def SuccessiveCoordinateHaar.coordinateConjugates (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (p : PrefixLabel ell) : unitary (Sequences M) :=
  F.coordinateLabels τ ω u ell p*F.coordinateTarget τ ω u z ell*(F.coordinateLabels τ ω u ell p)⁻¹

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.commonPerturbation_skew
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    star (F.commonPerturbation τ ω u z ell α) = -F.commonPerturbation τ ω u z ell α := by
  let A : Sequences M := ∑ j : Fin ell,
    let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
      F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1))
    a-star a
  have hA : star A = -A := by
    unfold A
    rw [star_sum]
    calc
      _ = ∑ j : Fin ell, -(let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
          F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1)); a-star a) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only
        rw [star_sub,star_star,neg_sub]
      _ = _ := Finset.sum_neg_distrib _
  change star ((α/(2*ell) : ℝ) • A) = -((α/(2*ell) : ℝ) • A)
  calc
    _ = (α/(2*ell) : ℝ) • star A := by rw [star_smul,star_trivial]
    _ = (α/(2*ell) : ℝ) • (-A) := congrArg ((α/(2*ell) : ℝ) • ·) hA
    _ = _ := smul_neg _ _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_mono : Monotone (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.subequivalent_of_le h)

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_range_bddAbove {I : Type*} (q : I → AlgebraProjection M) :
    BddAbove (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) :=
  ⟨1,by rintro _ ⟨i,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q i)⟩

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end


