-- Prove2me | Definitions.Def_OAIQ11Fg015
-- name    : OAIQ11Fg015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:25:35.885096+00:00
-- url     : https://prove2.me/theorems/ab7ace1e-29cc-42f5-8582-497ad6b05e8f
-- title:
--   Definitions bundle OAIQ11Fg015 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 9 definitions, 1 inductive type or structure and 3 theorems. The definitions and types are `OAI.Generator.Tracial.ReducedIntegerGaps`, `OAI.Generator.Tracial.SignedReducedGaps`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinatePrefix`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateTarget`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateVariables`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.haarSequence`, `OAI.Generator.Tracial.boundedToSequence`, `OAI.Generator.Tracial.boundedUnitarySequence`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CoordinatePerturbation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean), [`FactorGeneration_HaarSequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg021` and `OAIQ11Fg014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg022` and `OAIQ11Fg036`; the statements `OAI.Generator.Tracial.HaarEndpoints.mul_left_signed`, `OAI.Generator.Tracial.HaarEndpoints.reduced_gaps`, `OAI.Generator.Tracial.HaarEndpoints.signed_gaps`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm`, `OAI_Generator_Tracial_conjugateWord_formula`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI_Generator_Tracial_maximal_word_gaps`, `OAI_Generator_Tracial_successive_reduced_word_zero`, `OAI_Generator_Tracial_unitaryRepresentation_mk`, `OAI_Generator_Tracial_unitaryWord_append`, `OAI_Generator_Tracial_unitaryWord_cons` and `OAI_Generator_Tracial_unitaryWord_mem`; the proofs of `OAI.Generator.Tracial.HaarEndpoints.mul_left`, `OAI.Generator.Tracial.HaarEndpoints.mul_left_signed`, `OAI.Generator.Tracial.HaarEndpoints.reduced_gaps`, `OAI.Generator.Tracial.HaarEndpoints.signed_gaps`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_perturbedUnitary_distance`, `OAI_Generator_Tracial_conjugateWord_formula`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI_Generator_Tracial_exists_represented_perturbation`, `OAI_Generator_Tracial_maximal_word_gaps`, `OAI_Generator_Tracial_successive_reduced_word_zero`, `OAI_Generator_Tracial_traceClip_mem_original`, `OAI_Generator_Tracial_unitaryRepresentation_mk`, `OAI_Generator_Tracial_unitaryWord_append`, `OAI_Generator_Tracial_unitaryWord_cons` and `OAI_Generator_Tracial_unitaryWord_mem`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg021
import Definitions.Def_OAIQ11Fg014

set_option maxHeartbeats 1000000

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
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def ReducedIntegerGaps (D : Subalgebra ℂ (Q τ ω)) : ℤ → List (Q τ ω × ℤ) → Prop
  | _,[] => True
  | n,(d,m)::xs => d ∈ D ∧ m ≠ 0 ∧
      (quotientTrace τ ω d=0 ∨ SamePowerSign n m) ∧ ReducedIntegerGaps D m xs

/-! Expand nonzero integer powers into signs while retaining the exact rule:
only an equal-sign gap may have a nonzero scalar part. -/

def SignedReducedGaps (D : Subalgebra ℂ (Q τ ω)) : Bool → List (Q τ ω × Bool) → Prop
  | _,[] => True
  | s,(d,t)::xs => d ∈ D ∧ (s ≠ t → quotientTrace τ ω d=0) ∧ SignedReducedGaps D t xs

end

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

structure SuccessiveCoordinateHaar (hNM : N ≤ M) (seed : Set (Q τ ω)) where
  algebra : ℕ → StarSubalgebra ℂ (Q τ ω)
  step : ∀ j,CoordinateHaarData τ ω hNM (algebra j).toSubalgebra
  initial : algebra 0=StarAlgebra.adjoin ℂ seed
  successor : ∀ j,algebra (j+1)=StarAlgebra.adjoin ℂ
    (insert ((step j).t : Q τ ω) (algebra j : Set (Q τ ω)))
  separable : ∀ j,TopologicalSpace.IsSeparable (algebra j : Set (Q τ ω))

end

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
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
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def boundedToSequence (b : Bounded M) : Sequences M :=
  Classical.choose (boundedMap_surjective b)

theorem boundedToSequence_map (b : Bounded M) : boundedMap (boundedToSequence b)=b :=
  Classical.choose_spec (boundedMap_surjective b)

theorem boundedToSequence_apply (b : Bounded M) (k : ℕ) : boundedToSequence b k=b.val k :=
  congrArg (fun a : Bounded M => a.val k) (boundedToSequence_map b)

def boundedUnitarySequence (b : Bounded M) (hb : ∀ k,b.val k ∈ unitary M.toStarSubalgebra) :
    unitary (Sequences M) :=
  ⟨boundedToSequence b,by
    apply Unitary.mem_iff.mpr
    constructor <;> apply BoundedContinuousFunction.ext <;> intro k
    · change star (boundedToSequence b k)*boundedToSequence b k=1
      rw [boundedToSequence_apply]
      exact Unitary.star_mul_self_of_mem (hb k)
    · change boundedToSequence b k*star (boundedToSequence b k)=1
      rw [boundedToSequence_apply]
      exact Unitary.mul_star_self_of_mem (hb k)⟩

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.haarSequence (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j : ℕ) : unitary (Sequences M) :=
  boundedUnitarySequence (boundedInclusion hNM (F.step j).coordinates)
    (fun k => Unitary.map_mem (coordinateInclusion hNM) ((F.step j).unitary_coordinates k))

def SuccessiveCoordinateHaar.coordinateVariables (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) : ℕ → unitary (Sequences M)
  | 0 => F.haarSequence τ ω 0
  | j+1 => constantSequenceUnitary u*F.haarSequence τ ω (j+1)

def SuccessiveCoordinateHaar.coordinateTarget (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) : unitary (Sequences M) :=
  constantSequenceUnitary z*(FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix (ell+1)))⁻¹

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.coordinatePrefix (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (k : ℕ) : unitary (Sequences M) :=
  FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix k)

def SuccessiveCoordinateHaar.commonPerturbation (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : Sequences M :=
  (α/(2*ell)) • ∑ j : Fin ell,
    let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
      F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1))
    a-star a

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- Every actual finite equivalent partition has the expected base dimension. -/
theorem EquivalentPartition.dimension_base
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {p : AlgebraProjection M} {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : EquivalentPartition p ι) :
    traceFreeDimension hfactor hdiff E.base=traceFreeDimension hfactor hdiff p/Fintype.card ι := by
  have he (i : ι) : traceFreeDimension hfactor hdiff (E.leg i).target=
      traceFreeDimension hfactor hdiff E.base :=
    (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show E.base.Equivalent (E.leg i).target from ⟨E.leg i,E.initial i,rfl⟩)).symm
  have h := traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => (E.leg i).target) E.orthogonal p E.total
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  apply (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℝ)≠0)).mpr
  linarith

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end


