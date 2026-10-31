-- Prove2me | Definitions.Def_OAIQ129G001
-- name    : OAIQ129G001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:12:21.776755+00:00
-- url     : https://prove2.me/theorems/26981ede-0c0b-4db7-ae6e-3dad365018d9
-- title:
--   Definitions bundle OAIQ129G001 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 226 declarations of OpenAI's Lean: 134 definitions, 4 inductive types or structures, 14 instances and 74 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage`, `OAI.Generator.FiniteMatrixStage.TensorExtension`, `OAI.Generator.FiniteMatrixStage.generated`, `OAI.Generator.FiniteMatrixStage.restrictStage`, `OAI.Generator.FiniteMatrixStage.scalarStage`, `OAI.Generator.FiniteMatrixStage.stageUnion`, `OAI.Generator.FreeConvolution.Letter`, `OAI.Generator.FreeConvolution.begins`, `OAI.Generator.FreeConvolution.cancellation`, `OAI.Generator.FreeConvolution.creation`, `OAI.Generator.FreeConvolution.delta`, `OAI.Generator.FreeConvolution.inverseLetter`, `OAI.Generator.FreeConvolution.leftRegular`, `OAI.Generator.FreeConvolution.leftRegularHom`, `OAI.Generator.FreeConvolution.letter`, `OAI.Generator.FreeConvolution.realRegular`, `OAI.Generator.FreeConvolution.regular`, `OAI.Generator.MatrixEncoding.E11`, `OAI.Generator.MatrixEncoding.E12`, `OAI.Generator.MatrixEncoding.E21`, `OAI.Generator.MatrixEncoding.E22`, `OAI.Generator.MatrixEncoding.corner`, `OAI.Generator.MatrixEncoding.encodeA`, `OAI.Generator.MatrixEncoding.encodeB`, `OAI.Generator.MatrixUnitSystem`, `OAI.Generator.MatrixUnitSystem.algebra`, `OAI.Generator.MatrixUnitSystem.amplify`, `OAI.Generator.MatrixUnitSystem.coefficientEval`, `OAI.Generator.MatrixUnitSystem.coefficientHom`, `OAI.Generator.MatrixUnitSystem.commutant`, `OAI.Generator.MatrixUnitSystem.concreteAlgebra`, `OAI.Generator.MatrixUnitSystem.concreteCoefficientHom`, `OAI.Generator.MatrixUnitSystem.concreteHom`, `OAI.Generator.MatrixUnitSystem.fullProjection`, `OAI.Generator.MatrixUnitSystem.fullProjectionMatrix`, `OAI.Generator.MatrixUnitSystem.hom`, `OAI.Generator.MatrixUnitSystem.linearMap`, `OAI.Generator.MatrixUnitSystem.map`, `OAI.Generator.MatrixUnitSystem.product`, `OAI.Generator.MatrixUnitSystem.reindex` and 98 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_AmplificationEncoding`, `FactorGeneration_Convolution`, `FactorGeneration_CyclicPredual`, `FactorGeneration_Dimension`, `FactorGeneration_Exponential`, `FactorGeneration_FreeWords`, `FactorGeneration_FunctionalLimits`, `FactorGeneration_GroupTrace`, `FactorGeneration_HaarPatches`, `FactorGeneration_HaarSequences`, `FactorGeneration_HilbertLimits`, `FactorGeneration_HilbertProjections`, `FactorGeneration_LocalizedStates`, `FactorGeneration_LongWords`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixEncoding`, `FactorGeneration_MatrixExpectation`, `FactorGeneration_MatrixGenerators`, `FactorGeneration_MatrixRefinement`, `FactorGeneration_MatrixSequence`, `FactorGeneration_MatrixUnits`, `FactorGeneration_MonotoneTrace`, `FactorGeneration_NormalDimension`, `FactorGeneration_OperatorLimits`, `FactorGeneration_OrbitMinima`, `FactorGeneration_PatchingBounds`, `FactorGeneration_PatchingWords`, `FactorGeneration_PerturbationBounds`, `FactorGeneration_PredualOrder`, `FactorGeneration_PredualRange`, `FactorGeneration_ProductWords`, `FactorGeneration_QuotientRepresentation`, `FactorGeneration_RelativeGeneration`, `FactorGeneration_ResidualMoments`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Target`, `FactorGeneration_TensorRefinement`, `FactorGeneration_TraceTopology`, `FactorGeneration_TraceTransport`, `FactorGeneration_TracialInclusion`, `FactorGeneration_Ultrapower`, `FactorGeneration_Words`, `RelativeGeneration_Topology`.
--
--   **Imports.** It imports the published bundles `Def_FactorGeneration` and `Def_RelativeGeneration`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G003`, `OAIQ129G004`, `OAIQ129G005` and `OAIQ129G006`; the statements `OAI.Generator.Tracial.exists_commuting_matrix_extension_q129`, `OAI.Generator.Tracial.exists_normal_matrix_approximation_q129` and `OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_RelativeGeneration

section
-- module Solutions.OAIQ129_RG2.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator.MatrixEncoding

/-! Algebraic encoding of four corner operators by two self-adjoint matrices. -/
section
variable {R : Type*} [Ring R] [StarRing R]
local notation "Mat" => Matrix (Fin 2) (Fin 2) R

def E11 : Mat := !![1, 0; 0, 0]
def E12 : Mat := !![0, 1; 0, 0]
def E21 : Mat := !![0, 0; 1, 0]
def E22 : Mat := !![0, 0; 0, 1]
def corner (a : R) : Mat := !![a, 0; 0, 0]
def encodeA (a₁ a₂ C : R) : Mat := !![a₁, 0; 0, a₂ + C]
def encodeB (a₃ a₄ : R) : Mat := !![a₃, 1; 1, a₄]

end

/-! Algebraic diagonal identities used by the analytic gap recovery. -/

end Generator.MatrixEncoding

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OperatorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance baseNormedAlgebraRat (M : VonNeumannAlgebra H) : NormedAlgebra ℚ M.toStarSubalgebra :=
  .restrictScalars ℚ ℂ M.toStarSubalgebra

end

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

def weakOperatorBall (M : VonNeumannAlgebra H) (C : ℝ) : Set (H →WOT[ℂ] H) :=
  {T | T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C}

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete finite tracial von Neumann algebra in a faithful vector-trace
representation. These are operator-algebra data, without approximation assumptions. -/
structure TracialRepresentation (M : VonNeumannAlgebra H) where
  vector : H
  norm_vector : ‖vector‖ = 1
  cyclic : ∀ S T : M.toStarSubalgebra,
    inner ℂ vector ((S : H →L[ℂ] H) ((T : H →L[ℂ] H) vector)) =
    inner ℂ vector ((T : H →L[ℂ] H) ((S : H →L[ℂ] H) vector))
  separating : ∀ T : M.toStarSubalgebra, (T : H →L[ℂ] H) vector = 0 → T = 0

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
abbrev Algebra := M.toStarSubalgebra

def trace (T : Algebra (M := M)) : ℂ := inner ℂ τ.vector ((T : H →L[ℂ] H) τ.vector)
def norm₂ (T : Algebra (M := M)) : ℝ := ‖(T : H →L[ℂ] H) τ.vector‖

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem operator_norm_one_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp)

/-- Operator-norm bounded sequences, as an actual star subalgebra of pointwise sequences. -/
def boundedSequences (M : VonNeumannAlgebra H) : StarSubalgebra ℂ (ℕ → M.toStarSubalgebra) where
  carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  one_mem' := ⟨1, by norm_num, fun n => operator_norm_one_le⟩
  add_mem' := by
    rintro a b ⟨C,hC,ha⟩ ⟨D,hD,hb⟩
    exact ⟨C+D, add_nonneg hC hD, fun n =>
      (norm_add_le _ _).trans (add_le_add (ha n) (hb n))⟩
  mul_mem' := by
    rintro a b ⟨C,hC,ha⟩ ⟨D,hD,hb⟩
    exact ⟨C*D, mul_nonneg hC hD, fun n =>
      (norm_mul_le _ _).trans (mul_le_mul (ha n) (hb n) (norm_nonneg _) hC)⟩
  algebraMap_mem' c := by
    refine ⟨‖c‖, norm_nonneg _, fun n => ?_⟩
    change ‖algebraMap ℂ M.toStarSubalgebra c‖ ≤ ‖c‖
    rw [Algebra.algebraMap_eq_smul_one, norm_smul]
    exact (mul_le_mul_of_nonneg_left operator_norm_one_le (norm_nonneg c)).trans_eq (mul_one _)
  star_mem' := by
    rintro a ⟨C,hC,ha⟩
    refine ⟨C,hC,fun n => ?_⟩
    change ‖star (a n : H →L[ℂ] H)‖ ≤ C
    simpa [ContinuousLinearMap.star_eq_adjoint] using ha n

abbrev Bounded (M : VonNeumannAlgebra H) := boundedSequences M

end

open Filter
open scoped Topology

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

def conjugateLinear (u : unitary M.toStarSubalgebra) :
    M.toStarSubalgebra →ₗ[ℂ] M.toStarSubalgebra where
  toFun a := (u : M.toStarSubalgebra) * a * star (u : M.toStarSubalgebra)
  map_add' _ _ := by simp only [mul_add, add_mul]
  map_smul' _ _ := by simp only [mul_smul_comm, smul_mul_assoc]; rfl

@[simp] theorem conjugateLinear_one (a : M.toStarSubalgebra) : conjugateLinear 1 a = a := by
  simp [conjugateLinear]

def algebraOrbit (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) : Set M.toStarSubalgebra :=
  {a | ∃ u : G, conjugateLinear u.val b = a}

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_TracialInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

def coordinateInclusion : P.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion hPM

/-- P, as a star subalgebra of M. Its completeness is derived, not assumed. -/
def insideAlgebra : StarSubalgebra ℂ M.toStarSubalgebra :=
  P.toStarSubalgebra.comap M.toStarSubalgebra.subtype

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OrbitMinima
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The least-norm unitary-orbit point is scalar when the coordinate inclusion has scalar commutant. -/
section
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def subalgebraUnitaries (P : StarSubalgebra ℂ M.toStarSubalgebra) : Subgroup (unitary M.toStarSubalgebra) where
  carrier := {u | (u : M.toStarSubalgebra) ∈ P}
  one_mem' := P.one_mem
  mul_mem' hu hv := P.mul_mem hu hv
  inv_mem' hu := by
    change star _ ∈ P
    exact star_mem hu

def ambientUnitary (P : StarSubalgebra ℂ M.toStarSubalgebra) (u : unitary P) :
    subalgebraUnitaries P :=
  ⟨Unitary.map { toFun := P.subtype, map_one' := map_one _, map_mul' := map_mul _, map_star' := map_star _ } u, u.val.property⟩

end

/-! Irreducibility excludes disconnected nonzero ambient projections.
This gives the projection part of irreducibility in every nonzero corner. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Target
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem subset_wstar (s : Set (H →L[ℂ] H)) : s ⊆ wstar s := by
  intro x hx
  exact StarSubalgebra.mem_sInf.mpr fun S hS => hS.2 hx

theorem wstar_closed (s : Set (H →L[ℂ] H)) : WOTClosed (wstar s) := by
  unfold WOTClosed
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ wstar s} =
      ⋂ (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_ : WOTClosed S ∧ s ⊆ S),
        {T : H →WOT[ℂ] H | T.toCLM ∈ S} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, wstar, StarSubalgebra.mem_sInf]
  rw [heq]
  exact isClosed_iInter fun S => isClosed_iInter fun h => h.1

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : S →ₗ[ℂ] H where
  toFun a := a.val ξ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (vectorOrbitMap S ξ).range.topologicalClosure

instance vectorOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (vectorOrbitClosure S ξ) :=
  inferInstanceAs (CompleteSpace (vectorOrbitMap S ξ).range.topologicalClosure)

theorem mem_vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ vectorOrbitClosure S ξ :=
  Submodule.le_topologicalClosure _ ⟨1,rfl⟩

theorem vectorOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (a : S) {y : H} (hy : y ∈ vectorOrbitClosure S ξ) : a.val y ∈ vectorOrbitClosure S ξ := by
  have h : (vectorOrbitMap S ξ).range.topologicalClosure ≤
      (vectorOrbitClosure S ξ).comap a.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨a*b,rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage a.val.continuous
  exact h hy

end

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem kernel_invariant_of_commutes (x y : H →L[ℂ] H) (h : x*y=y*x) :
    x.ker ∈ Module.End.invtSubmodule y.toLinearMap := by
  intro ξ hξ
  change x (y ξ)=0
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) h
  change x (y ξ)=y (x ξ) at he
  rw [he,show x ξ=0 from hξ,map_zero]

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_commutes_star_right {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) : Commute x (star y) := by
  have h := congrArg star hxy.eq
  simp only [star_mul,hx.star_eq] at h
  exact h.symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

def algebraInclusion (h : N ≤ M) : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion h

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

def traceSymmetrize (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (2 : ℂ)⁻¹ • (a+star a)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

structure MatrixUnitSystem (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [Ring A] [StarRing A] [Algebra ℂ A] where
  entry : ι → ι → A
  star_entry : ∀ i j, star (entry i j) = entry j i
  mul_entry : ∀ i j k l, entry i j * entry k l = if j = k then entry i l else 0
  total : ∑ i, entry i i = 1

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

def linearMap : Matrix ι ι ℂ →ₗ[ℂ] A where
  toFun a := ∑ i, ∑ j, a i j • E.entry i j
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem linearMap_apply (a : Matrix ι ι ℂ) :
    E.linearMap a = ∑ i, ∑ j, a i j • E.entry i j := rfl

@[simp] theorem linearMap_single (i j : ι) (c : ℂ) :
    E.linearMap (Matrix.single i j c) = c • E.entry i j := by
  simp [linearMap_apply, Matrix.single, ite_smul, ite_and]

theorem linearMap_one : E.linearMap 1 = 1 := by
  simpa [linearMap_apply, Matrix.one_apply, ite_smul] using E.total

theorem linearMap_mul (a b : Matrix ι ι ℂ) :
    E.linearMap (a*b) = E.linearMap a * E.linearMap b := by
  simp only [linearMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul, E.mul_entry]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  conv_rhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun k i => ∑ l, (a i k * b k l) • E.entry i l)]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

variable [StarModule ℂ A]

theorem linearMap_star (a : Matrix ι ι ℂ) :
    E.linearMap (star a) = star (E.linearMap a) := by
  simp only [linearMap_apply, star_sum, star_smul, E.star_entry]
  rw [Finset.sum_comm]
  rfl

def hom : Matrix ι ι ℂ →⋆ₐ[ℂ] A where
  toFun := E.linearMap
  map_one' := E.linearMap_one
  map_mul' := E.linearMap_mul
  map_zero' := E.linearMap.map_zero
  map_add' := E.linearMap.map_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, E.linearMap.map_smul, E.linearMap_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := E.linearMap_star

@[simp] theorem hom_apply (a : Matrix ι ι ℂ) :
    E.hom a = ∑ i, ∑ j, a i j • E.entry i j := rfl

@[simp] theorem hom_single (i j : ι) (c : ℂ) :
    E.hom (Matrix.single i j c) = c • E.entry i j := E.linearMap_single i j c

def algebra : StarSubalgebra ℂ A := E.hom.range

theorem entry_mem (i j : ι) : E.entry i j ∈ E.algebra := by
  exact ⟨Matrix.single i j 1, (E.hom_single i j 1).trans (one_smul _ _)⟩

instance algebra_finiteDimensional : FiniteDimensional ℂ E.algebra := by
  change FiniteDimensional ℂ E.hom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.hom.toAlgHom.rangeRestrict.toLinearMap
    E.hom.toAlgHom.rangeRestrict_surjective

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

def product : MatrixUnitSystem (ι × κ) A where
  entry a b := E.entry a.1 b.1 * F.entry a.2 b.2
  star_entry a b := by
    rw [star_mul,E.star_entry,F.star_entry]
    exact (hc _ _ _ _).eq.symm
  mul_entry a b c d := by
    have hr : (E.entry a.1 b.1*F.entry a.2 b.2)*(E.entry c.1 d.1*F.entry c.2 d.2)=
        (E.entry a.1 b.1*E.entry c.1 d.1)*(F.entry a.2 b.2*F.entry c.2 d.2) := by
      calc _ = E.entry a.1 b.1*(F.entry a.2 b.2*E.entry c.1 d.1)*F.entry c.2 d.2 := by
              simp only [mul_assoc]
           _ = _ := by rw [(hc c.1 d.1 a.2 b.2).eq.symm]; simp only [mul_assoc]
    rw [hr,E.mul_entry,F.mul_entry]
    by_cases h1 : b.1=c.1 <;> by_cases h2 : b.2=c.2 <;>
      simp [h1,h2,Prod.ext_iff]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,F.total,mul_one,E.total]

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def commutant : StarSubalgebra ℂ A where
  carrier := {x | ∀ i j, Commute (E.entry i j) x}
  zero_mem' := by intro i j; exact Commute.zero_right _
  one_mem' := by intro i j; exact Commute.one_right _
  add_mem' hx hy := fun i j => (hx i j).add_right (hy i j)
  mul_mem' hx hy := fun i j => (hx i j).mul_right (hy i j)
  algebraMap_mem' c := fun i j => (Algebra.commutes c _).symm
  star_mem' hx := by
    intro i j
    show E.entry i j*star _=star _*E.entry i j
    simpa only [star_mul,E.star_entry] using (congrArg star (hx j i).eq).symm

def amplify (o : ι) (x : A) : A := ∑ i, E.entry i o*x*E.entry o i

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

open scoped BigOperators
variable {ι κ A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B]
variable (E : MatrixUnitSystem ι A)

def map (f : A →⋆ₐ[ℂ] B) : MatrixUnitSystem ι B where
  entry i j := f (E.entry i j)
  star_entry i j := by rw [← map_star,E.star_entry]
  mul_entry i j k l := by
    rw [← map_mul,E.mul_entry]
    split <;> simp_all
  total := by rw [← map_sum,E.total,map_one]

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def coefficientEval (a : Matrix ι ι E.commutant) : A :=
  ∑ i,∑ j,E.commutant.subtype (a i j)*E.entry i j

theorem coefficientEval_mul (a b : Matrix ι ι E.commutant) :
    E.coefficientEval (a*b)=E.coefficientEval a*E.coefficientEval b := by
  simp only [coefficientEval,Matrix.mul_apply,map_sum,map_mul,
    Finset.sum_mul,Finset.mul_sum]
  have he (i j k l : ι) :
      ((a i j).val*E.entry i j)*((b k l).val*E.entry k l)=
        (a i j).val*(b k l).val*(E.entry i j*E.entry k l) := by
    rw [mul_assoc,← mul_assoc (E.entry i j),((b k l).property i j).eq]
    simp only [mul_assoc]
  change (∑ i,∑ j,∑ k,(a i k).val*(b k j).val*E.entry i j) =
    ∑ k,∑ l,∑ i,∑ j,((a i j).val*E.entry i j)*((b k l).val*E.entry k l)
  simp only [he,E.mul_entry,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem coefficientEval_star (a : Matrix ι ι E.commutant) :
    E.coefficientEval (star a)=star (E.coefficientEval a) := by
  simp only [coefficientEval,star_sum,star_mul,E.star_entry,Matrix.star_apply,
    map_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact ((star (a i j)).property j i).eq.symm

theorem coefficientEval_one : E.coefficientEval 1=1 := by
  simpa [coefficientEval,Matrix.one_apply,apply_ite,ite_mul] using E.total

def coefficientHom : Matrix ι ι E.commutant →⋆ₐ[ℂ] A where
  toFun := E.coefficientEval
  map_one' := E.coefficientEval_one
  map_mul' := E.coefficientEval_mul
  map_zero' := by simp [coefficientEval]
  map_add' a b := by simp [coefficientEval,add_mul,Finset.sum_add_distrib]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    change E.coefficientEval (c • 1)=algebraMap ℂ A c
    simp only [coefficientEval,Matrix.smul_apply,map_smul,smul_mul_assoc,
      ← Finset.smul_sum]
    change c • E.coefficientEval 1=algebraMap ℂ A c
    rw [E.coefficientEval_one,Algebra.algebraMap_eq_smul_one]
  map_star' := E.coefficientEval_star

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace MatrixUnitSystem
variable (E : Generator.MatrixUnitSystem ι M.toStarSubalgebra)

def concreteHom : Matrix ι ι ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.hom

def concreteAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) := E.concreteHom.range

theorem concreteAlgebra_le : E.concreteAlgebra ≤ M.toStarSubalgebra := by
  rintro x ⟨a,rfl⟩
  exact (E.hom a).property

theorem mem_concreteAlgebra (x : M.toStarSubalgebra) :
    x.val ∈ E.concreteAlgebra ↔ x ∈ E.algebra := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Subtype.val ha⟩

instance concrete_finiteDimensional : FiniteDimensional ℂ E.concreteAlgebra := by
  change FiniteDimensional ℂ E.concreteHom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.concreteHom.toAlgHom.rangeRestrict.toLinearMap
    E.concreteHom.toAlgHom.rangeRestrict_surjective

def wotLinearMap : Matrix ι ι ℂ →ₗ[ℂ] (H →WOT[ℂ] H) :=
  (ContinuousLinearMap.WOTofCLM.toLinearMap).comp E.concreteHom.toAlgHom.toLinearMap

theorem concreteAlgebra_wotClosed : WOTClosed E.concreteAlgebra := by
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ E.concreteAlgebra} =
      (E.wotLinearMap.range : Set (H →WOT[ℂ] H)) := by
    ext T
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a, congrArg ContinuousLinearMapWOT.ofCLM ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,congrArg ContinuousLinearMapWOT.toCLM ha⟩
  unfold WOTClosed
  rw [heq]
  exact E.wotLinearMap.range.closed_of_finiteDimensional

end MatrixUnitSystem

end

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

def relativeStar : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {x | ∃ a : E.commutant, a.val.val=x}
  zero_mem' := ⟨0,rfl⟩
  one_mem' := ⟨1,rfl⟩
  add_mem' := by rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,rfl⟩
  mul_mem' := by rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a*b,rfl⟩
  algebraMap_mem' z := ⟨algebraMap ℂ E.commutant z,rfl⟩
  star_mem' := by rintro x ⟨a,rfl⟩; exact ⟨star a,rfl⟩

theorem relativeStar_mem (x : H →L[ℂ] H) :
    x ∈ E.relativeStar ↔ x ∈ M ∧ ∀ i j, (E.entry i j).val*x=x*(E.entry i j).val := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a.val.property,fun i j => congrArg Subtype.val (a.property i j).eq⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨⟨x,hx⟩,fun i j => Subtype.ext (hc i j)⟩,rfl⟩

theorem relativeStar_bicommutant :
    Set.centralizer (Set.centralizer (E.relativeStar : Set (H →L[ℂ] H))) =
      (E.relativeStar : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · intro a ha
    apply (E.relativeStar_mem a).mpr
    constructor
    · rw [← SetLike.mem_coe,← M.centralizer_centralizer]
      exact fun b hb => ha b (fun c hc => hb c ((E.relativeStar_mem c).mp hc).1)
    · intro i j
      exact ha (E.entry i j).val
        (fun b hb => (((E.relativeStar_mem b).mp hb).2 i j).symm)
  · intro a ha b hb
    exact (hb a ha).symm

def relativeVonNeumann : VonNeumannAlgebra H where
  toStarSubalgebra := E.relativeStar
  centralizer_centralizer' := E.relativeStar_bicommutant

theorem relativeVonNeumann_le : E.relativeVonNeumann ≤ M := by
  intro x hx
  exact ((E.relativeStar_mem x).mp hx).1

def relativeEquiv : E.commutant ≃⋆ₐ[ℂ] E.relativeVonNeumann.toStarSubalgebra where
  toFun a := ⟨a.val.val,⟨a,rfl⟩⟩
  invFun a := ⟨⟨a.val,((E.relativeStar_mem a.val).mp a.property).1⟩,
    fun i j => Subtype.ext (((E.relativeStar_mem a.val).mp a.property).2 i j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def reindex (E : MatrixUnitSystem ι A) (e : κ ≃ ι) : MatrixUnitSystem κ A where
  entry i j := E.entry (e i) (e j)
  star_entry i j := E.star_entry _ _
  mul_entry i j k l := by simpa only [e.apply_eq_iff_eq] using E.mul_entry (e i) (e j) (e k) (e l)
  total := (e.sum_comp (fun i => E.entry i i)).trans E.total

open UltrapowerBridge

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure FiniteMatrixStage (N : VonNeumannAlgebra H) where
  size : ℕ
  positive : 0 < size
  units : MatrixUnitSystem (Fin size) N.toStarSubalgebra

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_wotClosed (M : VonNeumannAlgebra H) : WOTClosed M.toStarSubalgebra := by
  change IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ (M : Set (H →L[ℂ] H))}
  rw [← M.centralizer_centralizer]
  change IsClosed {T : H →WOT[ℂ] H |
    ∀ S ∈ Set.centralizer (M : Set (H →L[ℂ] H)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : H →WOT[ℂ] H | S*T.toCLM=T.toCLM*S} =
      {T : H →WOT[ℂ] H |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (H →WOT[ℂ] H) ≃ (H →L[ℂ] H) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generated (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  wstar (⋃ n,((A n).units.concreteAlgebra : Set (H →L[ℂ] H)))

theorem generated_closed (A : ℕ → FiniteMatrixStage N) : WOTClosed (generated A) := wstar_closed _

def scalarStage (N : VonNeumannAlgebra H) : FiniteMatrixStage N where
  size := 1
  positive := by norm_num
  units := {
    entry := fun _ _ => 1
    star_entry := by intros; simp
    mul_entry := by
      intro i j k l
      rw [ite_eq_left (Subsingleton.elim j k),one_mul]
    total := by simp }

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def bicommutantStar (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))

theorem bicommutantStar_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantStar S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  unfold bicommutantStar
  rw [StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

def bicommutantVonNeumann (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := bicommutantStar S
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (bicommutantStar S : Set (H →L[ℂ] H)))=
      (bicommutantStar S : Set (H →L[ℂ] H))
    rw [bicommutantStar_coe,Set.centralizer_centralizer_centralizer]

namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {N M : VonNeumannAlgebra H}

def stageUnion (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  ⨆ n,(A n).units.concreteAlgebra

end FiniteMatrixStage

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_AmplificationEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! One arbitrary operator and a pair of self-adjoint operators generate the same weakly closed star algebra. -/
open scoped ComplexStarModule

/-! Two self-adjoint generators for an actual two-by-two amplification
whose actual commutant has four self-adjoint generators. Spectral separation
is proved, and the final generation uses the surjective coefficient map. -/
open scoped BigOperators
namespace MatrixUnitSystem
open MatrixEncoding
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem (Fin 2) M.toStarSubalgebra)

def concreteCoefficientHom : Matrix (Fin 2) (Fin 2) E.commutant →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.coefficientHom

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FreeWords
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

def freePrefix : ℕ → FreeGroup ℕ
  | 0 => 1
  | n + 1 => freePrefix n * FreeGroup.of n

def prefixRatio (k j : ℕ) : FreeGroup ℕ := freePrefix k * (freePrefix j)⁻¹

def exponentCoordinate (i : ℕ) : FreeGroup ℕ →* Multiplicative ℤ :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if i = j then 1 else 0)

theorem exponentCoordinate_prefix (i n : ℕ) :
    Multiplicative.toAdd (exponentCoordinate i (freePrefix n)) =
      if i < n then 1 else 0 := by
  induction n with
  | zero => simp [freePrefix]
  | succ n ih =>
    rw [freePrefix, map_mul, toAdd_mul, ih]
    simp only [exponentCoordinate, FreeGroup.lift_apply_of, toAdd_ofAdd]
    split_ifs <;> omega

theorem freePrefix_injective : Function.Injective freePrefix := by
  intro k j h
  have hk := congrArg (fun g => Multiplicative.toAdd (exponentCoordinate k g)) h
  have hj := congrArg (fun g => Multiplicative.toAdd (exponentCoordinate j g)) h
  simp only [exponentCoordinate_prefix] at hk hj
  omega

theorem prefixRatio_eq_one_iff (k j : ℕ) : prefixRatio k j = 1 ↔ k = j := by
  rw [prefixRatio, mul_inv_eq_one]
  exact freePrefix_injective.eq_iff

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/
noncomputable section
open scoped BigOperators
local instance instDecidableEqFreeGroupNat_solutions : DecidableEq (FreeGroup ℕ) := Classical.decEq _

def pairRatio {n : ℕ} (ij : Fin n × Fin n) : FreeGroup ℕ :=
  prefixRatio (ij.1.val + 1) (ij.2.val + 1)

theorem pairRatio_eq_one_iff {n : ℕ} (ij : Fin n × Fin n) :
    pairRatio ij = 1 ↔ ij.1 = ij.2 := by
  simp [pairRatio, prefixRatio_eq_one_iff, Fin.ext_iff]

def multiplicity (n : ℕ) (p : FreeGroup ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun ij : Fin n × Fin n => pairRatio ij = p).card

def ratioLabels (n : ℕ) : Finset (FreeGroup ℕ) := by
  classical
  exact insert 1 ((Finset.univ : Finset (Fin n)).offDiag.image pairRatio)

/-- For n > 0 this is exactly the image of all ordered pairs in the source. -/
theorem ratioLabels_eq_image {n : ℕ} (hn : 0 < n) :
    ratioLabels n = (Finset.univ : Finset (Fin n × Fin n)).image pairRatio := by
  classical
  ext p
  simp only [ratioLabels, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨ij, _, hp⟩)
    · exact ⟨(⟨0, hn⟩, ⟨0, hn⟩), (pairRatio_eq_one_iff _).mpr rfl⟩
    · exact ⟨ij, hp⟩
  · rintro ⟨ij, rfl⟩
    by_cases hij : ij.1 = ij.2
    · exact Or.inl ((pairRatio_eq_one_iff _).mpr hij)
    · exact Or.inr ⟨ij, by simp [hij], rfl⟩

end

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/
variable {G : Type*} [Group G]

def prefixes : List G → List G
  | [] => []
  | s :: ss => s :: (prefixes ss).map (fun g => s * g)

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Convolution
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/
section
open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance] Classical.propDecidable
abbrev SquareSpace (X : Type*) := lp (fun _ : X => ℂ) 2

variable {X I : Type*}

theorem squareSpace_norm_sq (f : SquareSpace X) :
    ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f

def coordinateMask (s : Set X) (f : SquareSpace X) : SquareSpace X :=
  ⟨s.indicator f, f.property.mono' (fun x => by
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx])⟩

@[simp] theorem coordinateMask_apply (s : Set X) (f : SquareSpace X) (x : X) :
    coordinateMask s f x = if x ∈ s then f x else 0 := rfl

def coordinatePermute (e : X ≃ X) (f : SquareSpace X) : SquareSpace X :=
  ⟨fun x => f (e x), memℓp_gen ((e.summable_iff).2 (f.property.summable (by norm_num)))⟩

@[simp] theorem coordinatePermute_apply (e : X ≃ X) (f : SquareSpace X) (x : X) :
    coordinatePermute e f x = f (e x) := rfl

theorem coordinatePermute_norm (e : X ≃ X) (f : SquareSpace X) :
    ‖coordinatePermute e f‖ = ‖f‖ := by
  have h : ‖coordinatePermute e f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [squareSpace_norm_sq, squareSpace_norm_sq]
    exact e.tsum_eq (fun x => ‖f x‖ ^ 2)
  nlinarith [norm_nonneg (coordinatePermute e f), norm_nonneg f]

/-- Reindexing by a permutation, as a bounded complex linear operator. -/
def coordinatePermuteCLM (e : X ≃ X) : SquareSpace X →L[ℂ] SquareSpace X :=
  LinearMap.mkContinuous
    { toFun := coordinatePermute e
      map_add' := by intros; ext x; rfl
      map_smul' := by intros; ext x; rfl }
    1 (fun f => by simpa using (coordinatePermute_norm e f).le)

@[simp] theorem coordinatePermuteCLM_apply (e : X ≃ X) (f : SquareSpace X) (x : X) :
    coordinatePermuteCLM e f x = f (e x) := rfl

end

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}
abbrev Letter (A : Type*) := A × Bool

def inverseLetter (a : Letter A) : Letter A := (a.1, !a.2)
def letter (a : Letter A) : FreeGroup A := FreeGroup.mk [a]
def begins (a : Letter A) (w : FreeGroup A) : Prop := w.toWord.head? = some a

@[simp] theorem inverseLetter_inverse (a : Letter A) : inverseLetter (inverseLetter a) = a := by
  cases a; simp [inverseLetter]

@[simp] theorem letter_toWord (a : Letter A) : (letter a).toWord = [a] := by
  simp [letter]

@[simp] theorem letter_inverse (a : Letter A) : letter (inverseLetter a) = (letter a)⁻¹ := by
  simp [letter, FreeGroup.inv_mk, FreeGroup.invRev, inverseLetter]

@[simp] theorem letter_true (a : A) : letter (a, true) = FreeGroup.of a := rfl

/-- The actual left regular translation λ(g)η(x)=η(g⁻¹x). -/
def leftRegular (g : FreeGroup A) : SquareSpace (FreeGroup A) →L[ℂ] SquareSpace (FreeGroup A) :=
  coordinatePermuteCLM (Equiv.mulLeft g⁻¹)

@[simp] theorem leftRegular_apply (g : FreeGroup A) (f : SquareSpace (FreeGroup A))
    (x : FreeGroup A) : leftRegular g f x = f (g⁻¹ * x) := rfl

@[simp] theorem leftRegular_norm (g : FreeGroup A) (f : SquareSpace (FreeGroup A)) :
    ‖leftRegular g f‖ = ‖f‖ := coordinatePermute_norm _ _

def creation (a : Letter A) (f : SquareSpace (FreeGroup A)) : SquareSpace (FreeGroup A) :=
  leftRegular (letter a) (coordinateMask {w | ¬ begins (inverseLetter a) w} f)

def cancellation (a : Letter A) (f : SquareSpace (FreeGroup A)) : SquareSpace (FreeGroup A) :=
  leftRegular (letter a) (coordinateMask {w | begins (inverseLetter a) w} f)

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/
section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}
local notation "H" => SquareSpace (FreeGroup A)
local notation "Op" => H →L[ℂ] H

def leftRegularHom : FreeGroup A →* Op where
  toFun := leftRegular
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_inv_rev, mul_assoc]

def regular : MonoidAlgebra ℂ (FreeGroup A) →ₐ[ℂ] Op :=
  MonoidAlgebra.lift ℂ Op (FreeGroup A) leftRegularHom

def realRegular : MonoidAlgebra ℝ (FreeGroup A) →ₐ[ℝ] Op :=
  MonoidAlgebra.lift ℝ Op (FreeGroup A) leftRegularHom

def delta : H := lp.single 2 1 1

@[simp] theorem delta_apply (x : FreeGroup A) : (delta : H) x = if x = 1 then 1 else 0 := by
  by_cases hx : x = 1 <;> simp [delta, lp.single_apply, hx]

@[simp] theorem delta_norm : ‖(delta : H)‖ = 1 := by
  simp [delta, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

@[simp] theorem leftRegular_delta_apply (g x : FreeGroup A) :
    leftRegular g (delta : H) x = if x = g then 1 else 0 := by
  simp [inv_mul_eq_one, eq_comm]

end FreeConvolution

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_CyclicPredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A concrete candidate predual: the norm-closed complex span of vector
functionals from the faithful cyclic trace representation, with completeness,
separability, and an isometric evaluation map. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Name the existing operator-norm structure to keep the norm topology
explicit through the nested dual and submodule constructions. -/
instance algebraDualNormed (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (StrongDual ℂ M.toStarSubalgebra) := inferInstance

end

/-! Every functional in the constructed norm-closed vector-functional space is
weak-operator continuous on each bounded ball of the original algebra. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def ballContinuousFunctionals (M : VonNeumannAlgebra H) (C : ℝ) :
    Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) where
  carrier := {f | Continuous (fun T : weakOperatorBall M C => f ⟨T.val.toCLM,T.property.1⟩)}
  zero_mem' := by exact continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.const_smul c

end

/-! Recover every functional on the constructed predual from an actual algebra
element, using compact bounded balls and weak-dual Hahn--Banach separation. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem dual_norm_le_of_re_unitBall (f : StrongDual ℂ M.toStarSubalgebra) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a : M.toStarSubalgebra,‖a‖ ≤ 1 → (f a).re ≤ C) : ‖f‖ ≤ C := by
  let r : StrongDual ℝ M.toStarSubalgebra := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm f
  have hr : ‖r‖=‖f‖ := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm.norm_map f
  rw [← hr]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro a ha
  change |(f a).re| ≤ C
  apply abs_le.mpr
  refine ⟨?_,hf a ha.le⟩
  have hn := hf (-a) (by simpa only [norm_neg] using ha.le)
  simpa only [map_neg,Complex.neg_re,neg_le] using hn

theorem weakDual_separation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set (WeakDual ℂ E)} {x : WeakDual ℂ E}
    (hs : Convex ℝ s) (hclosed : IsClosed s) (hx : x ∉ s) :
    ∃ (g : StrongDual ℂ (WeakDual ℂ E)) (u : ℝ),
      (∀ a ∈ s, (g a).re < u) ∧ u < (g x).re := by
  let : AddCommGroup (WeakDual ℂ E) := inferInstance
  let : Module ℝ (WeakDual ℂ E) := inferInstanceAs (Module ℝ (StrongDual ℂ E))
  let : Module ℂ (WeakDual ℂ E) := inferInstanceAs (Module ℂ (StrongDual ℂ E))
  let : IsScalarTower ℝ ℂ (WeakDual ℂ E) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ E))
  let : LocallyConvexSpace ℝ (WeakDual ℂ E) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ E)))
  exact RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hs hclosed hx

end

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

instance functionalSubspaceNormed : NormedAddCommGroup F := inferInstance

instance functionalSubspaceNormedSpace : NormedSpace ℂ F := inferInstance

def functionalSubspaceEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ F :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict F

instance functionalSubspaceWeakScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ F) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ F))

instance functionalSubspaceWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ F) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ F)))

end

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {ι : Type*}
  [Fintype ι]

theorem exists_disjoint_card (s t : Finset ι) (h : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, Disjoint s u ∧ u.card=t.card := by
  classical
  have hc : t.card ≤ (Finset.univ \ s).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s),Finset.card_univ]
    omega
  obtain ⟨u,hu,huc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨u,Finset.disjoint_left.mpr ?_,huc⟩
  intro i hi hui
  exact (Finset.mem_sdiff.mp (hu hui)).2 hi

end EquivalentPartition
end

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem eq_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, |a-b| ≤ 2/2^n) : a=b := by
  by_contra hab
  have hp : 0 < |a-b|/2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring] at hh
  linarith

end Tracial

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
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem le_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, a ≤ b+1/2^n) : a ≤ b := by
  by_contra hab
  have hp : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  linarith

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Exponential
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! The homogeneous expansion of an ordered exponential product,
with factorial weights and multiplication order retained. -/
noncomputable section
open scoped BigOperators
section Algebra
variable {R : Type*} [Ring R] [Algebra ℝ R]

def exponentialDegree : List R → ℕ → R
  | [], d => if d = 0 then 1 else 0
  | a :: as, d => ∑ k ∈ Finset.range (d + 1),
      ((k.factorial : ℝ)⁻¹ • a ^ k) * exponentialDegree as (d - k)

@[simp] theorem exponentialDegree_zero (xs : List R) : exponentialDegree xs 0 = 1 := by
  induction xs with
  | nil => simp [exponentialDegree]
  | cons a as ih => simp [exponentialDegree, ih]

@[simp] theorem exponentialDegree_one (xs : List R) : exponentialDegree xs 1 = xs.sum := by
  induction xs with
  | nil => simp [exponentialDegree]
  | cons a as ih =>
    simp [exponentialDegree, Finset.sum_range_succ, ih, add_comm]

end Algebra

end

/-! Summation of homogeneous-degree remainder bounds, given the expansion and its coefficient estimates. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/
namespace Tracial

section
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem exists_inner_factor_of_bound (F : E →ₗ[ℂ] V) (φ : E →ₗ[ℂ] ℂ)
    (C : ℝ) (hb : ∀ x : E, ‖φ x‖ ≤ C*‖F x‖) :
    ∃ η : V, ∀ x : E, φ x=inner ℂ η (F x) := by
  classical
  have hfiber {x y : E} (h : F x=F y) : φ x=φ y := by
    have hb' := hb (x-y)
    rw [map_sub,map_sub,h,sub_self,norm_zero,mul_zero] at hb'
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb' (norm_nonneg _)))
  have hex (z : LinearMap.range F) : ∃ x : E, F x=z.val := z.property
  choose a ha using hex
  let L : LinearMap.range F →ₗ[ℂ] ℂ :=
    { toFun := fun z => φ (a z)
      map_add' := by
        intro z w
        calc φ (a (z+w)) = φ (a z+a w) := hfiber (by rw [ha,map_add,ha,ha]; rfl)
          _ = φ (a z)+φ (a w) := map_add φ _ _
      map_smul' := by
        intro c z
        calc φ (a (c • z)) = φ (c • a z) := hfiber (by rw [ha,map_smul,ha]; rfl)
          _ = c • φ (a z) := map_smul φ _ _ }
  have hL (x : E) : L ⟨F x,LinearMap.mem_range_self F x⟩=φ x := hfiber (ha _)
  let l : LinearMap.range F →L[ℂ] ℂ := L.mkContinuous C (fun z => by
    have h := hb (a z)
    rw [ha] at h
    exact h)
  obtain ⟨g,hg,_⟩ := exists_extension_norm_eq (LinearMap.range F) l
  refine ⟨(InnerProductSpace.toDual ℂ V).symm g,?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  exact ((hg ⟨F x,LinearMap.mem_range_self F x⟩).trans (hL x)).symm

end

/-! Pointwise ultrafilter limits of uniformly bounded complex functionals.
Compactness is used only for scalar closed balls, with no separability premise. -/
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_bounded_functional_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (f : ι → E →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ∃ φ : E →L[ℂ] ℂ, ‖φ‖ ≤ C ∧
      ∀ x : E, Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 (φ x)) := by
  have hex (x : E) : ∃ z : ℂ, ‖z‖ ≤ C*‖x‖ ∧
      Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 z) := by
    obtain ⟨z,hz,ht⟩ := (isCompact_closedBall (0 : ℂ) (C*‖x‖)).ultrafilter_le_nhds
      (ω.map (fun i => f i x)) (by
        apply le_principal_iff.mpr
        change ∀ᶠ i in (ω : Filter ι), f i x ∈ Metric.closedBall 0 (C*‖x‖)
        exact Eventually.of_forall (fun i => by
          simpa only [Metric.mem_closedBall,dist_zero_right] using
            (f i).le_of_opNorm_le (hf i) x))
    exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,ht⟩
  choose v hv ht using hex
  have hadd (x y : E) : v (x+y)=v x+v y := by
    apply tendsto_nhds_unique (ht (x+y))
    simpa only [map_add] using (ht x).add (ht y)
  have hsmul (c : ℂ) (x : E) : v (c • x)=c • v x := by
    apply tendsto_nhds_unique (ht (c • x))
    simpa only [map_smul,smul_eq_mul] using (ht x).const_mul c
  let φ : E →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨φ,φ.opNorm_le_bound hC hv,ht⟩

end Tracial

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def signedLetter (v : M.toStarSubalgebra) (s : Bool) : M.toStarSubalgebra :=
  if s then star v else v

def patchingWord (v : M.toStarSubalgebra) : List (Bool × M.toStarSubalgebra) → M.toStarSubalgebra
  | [] => 1
  | (s,x)::xs => signedLetter v s*x*patchingWord v xs

end

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- The last coefficient is an endpoint; all earlier coefficients are internal. -/
def patchingCoefficients (F : Set M.toStarSubalgebra) : List (Bool × M.toStarSubalgebra) → Prop
  | [] => True
  | [a] => a.2 ∈ F ∪ {1}
  | a::b::xs => a.2 ∈ F ∧ patchingCoefficients F (b::xs)

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- All lists of length at most n over a finite alphabet. -/
def boundedLists {α : Type*} (A : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => by
    classical
    exact insert [] ((A ×ˢ boundedLists A n).image (fun z => z.1 :: z.2))

/-- A finite alphabet of signs and coefficients. -/
def signedAlphabet (F : Finset M.toStarSubalgebra) : Finset (Bool × M.toStarSubalgebra) :=
  Finset.univ ×ˢ F

@[simp] theorem mem_signedAlphabet (F : Finset M.toStarSubalgebra)
    (a : Bool × M.toStarSubalgebra) : a ∈ signedAlphabet F ↔ a.2 ∈ F := by
  simp [signedAlphabet]

/-- The uncompressed middle coefficient between the first two patch letters.
Every coefficient here is internal to the original word. -/
def middleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset (M.toStarSubalgebra × List (Bool × M.toStarSubalgebra)) := by
  classical
  exact (F ×ˢ boundedLists (signedAlphabet F) n).filter (fun z => z.2.length+2 ≤ n)

/-- Actual fixed outer coefficients needed for one-patch terms. -/
def outerWordFamily (v : M.toStarSubalgebra) (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset M.toStarSubalgebra := by
  classical
  exact ((insert 1 F) ×ˢ boundedLists (signedAlphabet (insert 1 F)) n).image
    (fun z => z.1*patchingWord v z.2)

end

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- A_i is zero for an empty middle segment, since its sole coefficient is centered. -/
def middleMomentError (ε : ℕ → ℝ) (r : ℕ) : ℝ := if r=0 then 0 else ε r

end

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def patchingExpansion (v w : M.toStarSubalgebra) :
    List (Bool × M.toStarSubalgebra) → List (ℕ × M.toStarSubalgebra)
  | [] => [(0,1)]
  | (s,x)::xs =>
      (patchingExpansion v w xs).map (fun z => (z.1,signedLetter v s*x*z.2)) ++
      (patchingExpansion v w xs).map (fun z => (z.1+1,signedLetter w s*x*z.2))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PatchingBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact positive tolerance recurrence used in Popa Lemma 3.2. -/
section

def patchingTolerance (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | k+1 => (2 : ℝ)^(k+2)*patchingTolerance δ k

@[simp] theorem patchingTolerance_zero (δ : ℝ) : patchingTolerance δ 0=δ := rfl
@[simp] theorem patchingTolerance_succ (δ : ℝ) (k : ℕ) :
    patchingTolerance δ (k+1)=2^(k+2)*patchingTolerance δ k := rfl

end

/-! Explicit binary masks for the existing ordered expansion. A true bit is a
patch letter. Occurrences are retained even when their operator values coincide. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def binaryMasks : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (binaryMasks n).map (false :: ·) ++ (binaryMasks n).map (true :: ·)

def maskedWord (v w : M.toStarSubalgebra) :
    List (Bool × M.toStarSubalgebra) → List Bool → M.toStarSubalgebra
  | [], _ => 1
  | (s,x)::xs, bs =>
      signedLetter (if bs.headD false then w else v) s*x*maskedWord v w xs bs.tail

end

/-! Mask uniqueness and a deliberately coarse budget that avoids off-by-one
counts: 2^k ordinary budgets plus one exceptional budget fit epsilon_k. -/
section

def exceptionalMask (k : ℕ) : List Bool := true::(List.replicate (k-2) false++[true])

end

/-! Extract actual coefficient segments and fixed one-patch outer factors.
These lemmas apply to the source lists without assuming segment membership. -/

/-! The triangle inequality for the exact noncommutative mask expansion. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixExpectation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Construct contractive expectations onto the actual finite matrix stages.
For every element of their weak closure, these expectations converge in L2
and remain in its operator norm ball. -/
open Filter
open scoped Topology

/-! Construct scalarizing partitions for an actual finite matrix algebra
inside a diffuse finite factor. No chain or pinching hypothesis is assumed. -/

/-! Finite matrix approximation and Bell partitions give actual small
pinching energy. The commuting matrix factor is constructed, not assumed. -/
open Filter
open scoped BigOperators Topology
namespace FiniteMatrixStage

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

/-- View the same finite matrix stage inside any algebra containing it. -/
def restrictStage (E : FiniteMatrixStage N) (R : VonNeumannAlgebra H)
    (hER : E.units.concreteAlgebra ≤ R.toStarSubalgebra) : FiniteMatrixStage R where
  size := E.size
  positive := E.positive
  units := {
    entry := fun i j => ⟨(E.units.entry i j).val,
      hER ((E.units.mem_concreteAlgebra _).mpr (E.units.entry_mem i j))⟩
    star_entry := fun i j => Subtype.ext (congrArg (fun x : N.toStarSubalgebra => x.val) (E.units.star_entry i j))
    mul_entry := fun i j k l => by
      apply Subtype.ext
      simpa only [MulMemClass.coe_mul,ZeroMemClass.coe_zero,Subtype.coe_mk,
        apply_ite Subtype.val] using congrArg (fun x : N.toStarSubalgebra => x.val) (E.units.mul_entry i j k l)
    total := by
      apply Subtype.ext
      have h := congrArg (fun x : N.toStarSubalgebra => x.val) E.units.total
      change R.toStarSubalgebra.subtype (∑ i,_) = 1
      rw [map_sum]
      change N.toStarSubalgebra.subtype (∑ i,E.units.entry i i)=1 at h
      rw [map_sum] at h
      exact h }

end

/-! Countably many finite matrix algebras give L2 separability of their weak closure. -/
open UltrapowerBridge Tracial

end FiniteMatrixStage

/-! The actual finite-stage conditional expectations converge strongly and
adjoint-strongly on every vector in the given representation. The generated
algebra also has a constructed separable faithful cyclic Hilbert representation. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/
section
open UltrapowerBridge

def algebraSignedLetter {A : Type*} [Star A] (v : A) (s : Bool) : A :=
  if s then star v else v

def algebraPatchingWord {A : Type*} [Monoid A] [Star A] (v : A) :
    List (Bool × A) → A
  | [] => 1
  | (s,x)::xs => algebraSignedLetter v s*x*algebraPatchingWord v xs

def optionalCoefficient {A : Type*} [One A] (x : ℕ → A) : Option ℕ → A
  | none => 1
  | some i => x i

end

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def indexedCoefficient (x : ℕ → ℕ → M.toStarSubalgebra) (j : ℕ) :
    Option ℕ → M.toStarSubalgebra
  | none => 1
  | some i => x i j

end

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev ResidualWordIndex := ℕ ⊕ (Option ℕ × Option ℕ × List (Bool × ℕ) × Bool)

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

def algebraMixedTail {A : Type*} [Monoid A] [Star A] (v w : A) (x : ℕ → A)
    (last : Option ℕ) (b s : Bool) : List (Bool × Bool × ℕ) → A
  | [] => algebraSignedLetter (if b then w else v) s * optionalCoefficient x last
  | (c,t,i)::xs => algebraSignedLetter (if c then w else v) t*x i*
      algebraMixedTail v w x last b s xs

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/
section
open UltrapowerBridge Filter

def algebraWordCore {A : Type*} [Monoid A] [Star A] (v : A) (x : ℕ → A)
    (s : Bool) : List (Bool × ℕ) → A
  | [] => algebraSignedLetter v s
  | (t,i)::xs => algebraSignedLetter v t*x i*algebraWordCore v x s xs

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev CyclicFamilyIndex := ℕ ⊕ (Option ℕ × Option ℕ)

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def productLeft (u : A) (s : Bool) : A := if s then 1 else u
def productRight (u : A) (s : Bool) : A := if s then star u else 1

def betweenWord (v : A) (s : Bool) : List (A × Bool) → A → A
  | [], b => algebraSignedLetter v s*b
  | (d,t)::xs, b => algebraSignedLetter v s*d*betweenWord v t xs b

def productGapList (u : A) (s : Bool) : List (A × Bool) → List (Bool × A)
  | [] => []
  | (d,t)::xs => (s,productRight u s*d*productLeft u t)::productGapList u t xs

def finalWordSign (s : Bool) : List (A × Bool) → Bool
  | [] => s
  | (_,t)::xs => finalWordSign t xs

end Algebra

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev ProductFamilyIndex := ℕ ⊕ ((Bool × Option ℕ) ⊕ ℕ)

end

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def powerBlockGaps (s : Bool) (n : ℕ) : List (A × (Bool × ℕ)) → List (A × Bool)
  | [] => List.replicate n (1,s)
  | (d,(t,k))::xs => List.replicate n (1,s) ++ (d,t)::powerBlockGaps t k xs

def powerBlockWord (v : A) (s : Bool) (n : ℕ) : List (A × (Bool × ℕ)) → A → A
  | [],b => algebraSignedLetter v s^(n+1)*b
  | (d,(t,k))::xs,b => algebraSignedLetter v s^(n+1)*d*powerBlockWord v t k xs b

/-- Magnitude is encoded as predecessor, so every resulting block has positive length. -/
def integerPowerBlock : ℤ → Bool × ℕ
  | .ofNat n => (false,n-1)
  | .negSucc n => (true,n)

def integerWord (v : unitary A) (x : ℕ → A) (n : ℤ) : List (ℕ × ℤ) → A → A
  | [],b => (↑(v^n) : A)*b
  | (i,m)::xs,b => (↑(v^n) : A)*x i*integerWord v x m xs b

end Algebra

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev Sequences (M : VonNeumannAlgebra H) := BoundedContinuousFunction ℕ M.toStarSubalgebra

instance sequencesIsTopologicalRing : IsTopologicalRing (Sequences M) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (Sequences M) inferInstance

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Words
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! All alternating word shapes, allowing either algebra at either endpoint. -/

/-! Splitting a reduced word at its first occurrence of a specified generator. -/

/-! Noncommutative ordered row words and coefficient majorization, without commuting-row assumptions. -/
variable {R : Type*} [Semiring R]

def orderedWords : List R → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: as, d + 1 => a * orderedWords (a :: as) d + orderedWords as (d + 1)
termination_by xs d => (d, xs.length)

@[simp] theorem orderedWords_zero (xs : List R) : orderedWords xs 0 = 1 := by
  cases xs <;> simp [orderedWords]

@[simp] theorem orderedWords_nil (d : ℕ) : orderedWords ([] : List R) d = if d = 0 then 1 else 0 := by
  cases d <;> simp [orderedWords]

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

def SamePowerSign (n m : ℤ) : Prop := (0 < n ∧ 0 < m) ∨ (n < 0 ∧ m < 0)

/-! Expand nonzero integer powers into signs while retaining the exact rule:
only an equal-sign gap may have a nonzero scalar part. -/

def signExponent (s : Bool) : ℤ := if s then -1 else 1

end

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def absorbedGapList (u : A) (s : Bool) : List (A × Bool) → List (A × Bool)
  | [] => []
  | (d,t)::xs => (productRight u s*d*productLeft u t,t)::absorbedGapList u t xs

end Algebra

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertProjections
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/
section
open Set Filter Topology
variable {X : Type*} [TopologicalSpace X]

/-- An explicit countable intersection of open sets of continuity points. -/
def continuityCore (f : X → ℝ) : Set X :=
  ⋂ q : ℚ, (frontier {x | f x ≤ (q : ℝ)})ᶜ

end

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/
section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

def projectionNorm (ξ : E) : ℝ := ‖K.starProjection ξ‖

def residual (z : E) : E := z - K.starProjection z

end

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

/-- Every countable family in a directed preorder has an increasing majorant
above a specified index. This is not countable cofinality of the preorder. -/
theorem exists_monotone_dominating_from
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (f : ℕ → I) (i : I) :
    ∃ a : ℕ → I, Monotone a ∧ (∀ n, f n ≤ a n) ∧ (∀ n, i ≤ a n) := by
  classical
  let upper (x y : I) := (exists_ge_ge x y).choose
  have hl (x y : I) : x ≤ upper x y := (exists_ge_ge x y).choose_spec.1
  have hr (x y : I) : y ≤ upper x y := (exists_ge_ge x y).choose_spec.2
  let a : ℕ → I := Nat.rec (upper i (f 0)) (fun n j => upper j (f (n+1)))
  have ha : Monotone a := monotone_nat_of_le_succ (fun n => hl (a n) (f (n+1)))
  refine ⟨a,ha,?_,fun n => (hl i (f 0)).trans (ha (Nat.zero_le n))⟩
  intro n
  cases n with
  | zero => exact hr i (f 0)
  | succ n => exact hr (a n) (f (n+1))

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

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_unit_vector_of_unit_ne_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ ξ : H, ‖ξ‖=1 := by
  classical
  have hne : ∃ ξ : H, ξ≠0 := by
    by_contra h
    push Not at h
    apply hunit
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ,hξ⟩ := hne
  refine ⟨(‖ξ‖⁻¹ : ℂ) • ξ,?_⟩
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg ξ),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G
local instance instDecidableEqFreeGroupNat_solutions_1 : DecidableEq G := Classical.decEq _
local instance instDecidableEqFreeGroupNat_solutions_2 : DecidableEq F := Classical.decEq _

def positiveLetterPair (p : G) : MonoidAlgebra ℝ F :=
  MonoidAlgebra.single (letter (p, true)) 1 + MonoidAlgebra.single (letter (p, false)) 1

def negativeLetterPair (p : G) : MonoidAlgebra ℂ F :=
  MonoidAlgebra.single (letter (p, true)) 1 - MonoidAlgebra.single (letter (p, false)) 1

def perturbationRow {n : ℕ} (α : ℝ) (k : Fin n) : MonoidAlgebra ℂ F × MonoidAlgebra ℝ F :=
  ((α / (2 * n)) • ∑ j : Fin n, negativeLetterPair (pairRatio (k, j)),
   (α / (2 * n)) • ∑ j : Fin n, positiveLetterPair (pairRatio (k, j)))

def perturbationRows (n : ℕ) (α : ℝ) :
    List (MonoidAlgebra ℂ F × MonoidAlgebra ℝ F) := List.ofFn (perturbationRow (n := n) α)

end

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G

local instance instDecidableEqFreeGroupNat_solutions_3_rc298e9_1 : DecidableEq G := Classical.decEq _
/-- The manuscript's finite set S, including the identity prefix ratio as a label. -/
def PrefixLabel (n : ℕ) := {p : G // p ∈ ratioLabels n}

def pairLabel {n : ℕ} (k j : Fin n) : PrefixLabel n :=
  ⟨pairRatio (k, j), by
    rw [ratioLabels_eq_image (Nat.zero_lt_of_lt k.isLt)]
    exact Finset.mem_image.mpr ⟨(k, j), Finset.mem_univ _, rfl⟩⟩

def prefixWordEmbedding (n : ℕ) : FreeGroup (PrefixLabel n) →* F :=
  FreeGroup.map Subtype.val

def prefixRingEmbedding (n : ℕ) : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ]
    MonoidAlgebra ℂ F := MonoidAlgebra.mapDomainAlgHom ℂ ℂ (prefixWordEmbedding n)

@[simp] theorem prefixRingEmbedding_single (n : ℕ) (g : FreeGroup (PrefixLabel n)) (c : ℂ) :
    prefixRingEmbedding n (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (prefixWordEmbedding n g) c := by
  exact MonoidAlgebra.mapDomain_single

/-- Literal B_k in the free group on the finite label set S. -/
def finitePerturbationRow {n : ℕ} (α : ℝ) (k : Fin n) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) :=
  (α / (2 * n)) • ∑ j : Fin n,
    (MonoidAlgebra.single (FreeGroup.of (pairLabel k j)) 1 -
     MonoidAlgebra.single ((FreeGroup.of (pairLabel k j))⁻¹) 1)

def finitePerturbationRows (n : ℕ) (α : ℝ) :=
  List.ofFn (finitePerturbationRow (n := n) α)

@[simp] theorem finitePerturbationRow_embed {n : ℕ} (α : ℝ) (k : Fin n) :
    prefixRingEmbedding n (finitePerturbationRow α k) = (perturbationRow α k).1 := by
  have hs (c : ℝ) (f : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n))) :
      prefixRingEmbedding n (c • f) = c • prefixRingEmbedding n f :=
    map_smul ((prefixRingEmbedding n).restrictScalars ℝ).toLinearMap c f
  simp only [finitePerturbationRow, perturbationRow, hs, map_sum, map_sub,
    prefixRingEmbedding_single]
  congr 1

def embeddedCoefficientMap (n : ℕ) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₗ[ℂ] SquareSpace F :=
  (ContinuousLinearMap.apply ℂ (SquareSpace F) delta).toLinearMap.comp
    (regular.toLinearMap.comp (prefixRingEmbedding n).toLinearMap)

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TensorRefinement
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.FiniteMatrixStage

/-! A finite refinement retaining its actual commuting matrix factor.
The relation composes, so finite energy descent can retain these witnesses. -/
section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def TensorExtension (E F : FiniteMatrixStage N) : Prop :=
  ∃ G : FiniteMatrixStage N,
    (∀ i j k l,Commute (E.units.entry i j) (G.units.entry k l)) ∧
    F.units.algebra=E.units.algebra ⊔ G.units.algebra

end

/-! Tensor-factor-retaining compatible refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! A single increasing sequence of full matrix algebras simultaneously
kills every member of a supplied countable centered family in commutant L2. -/
open Filter
open scoped BigOperators Topology
open UltrapowerBridge Tracial

end Generator.FiniteMatrixStage

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixGenerators
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Diagonal projections and one full-support rank-one projection generate
every finite full matrix algebra, including matrices larger than size two. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def fullProjectionMatrix : Matrix ι ι ℂ := fun _ _ => (Fintype.card ι : ℂ)⁻¹

def fullProjection : A := E.hom (fullProjectionMatrix (ι := ι))

end MatrixUnitSystem

/-! Two actual self-adjoint generators for the weak closure of countably
many pairwise commuting finite full matrix factors. -/

/-! The retained tensor extensions supply commuting factors generating
exactly the original matrix-union weak closure. -/

/-! The represented irreducible matrix subfactor can be constructed together
with two self-adjoint generators, without hyperfinite uniqueness. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MonotoneTrace
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveResolvent (a : A) : A := cfc (fun t : ℝ => 1 - (1 + t)⁻¹) a

end

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PerturbationBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators InnerProductSpace
open FreeConvolution

def rowSignedWord {ell : ℕ} (k : Fin ell) (a : Fin ell × Bool) :
    FreeGroup (PrefixLabel ell) := letter (pairLabel k a.1,a.2)

end

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualOrder
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator norm geometry for the original existential Banach-predual gap.
These statements use only concrete Hilbert operators. They do not identify
any predual or prove trace-orbit separability. -/

/-! Bounded self-adjoint sets are weak-star compact for the actual Banach
predual isometry. No predual uniqueness or WOT compatibility is assumed. -/

/-! Positive operator balls are compact in the weak-star topology of the
given Banach predual. The isometry is not assumed weak-operator continuous. -/

/-! Closed and compact order intervals for the given Banach predual.
All inequalities are the concrete operator Loewner order. -/

/-! Monotone order limits in the algebra converge for the actual given
Banach predual. Greatest/least bounds are tested only against members of S,
not against all ambient operators. -/

/-! The actual given predual embeds isometrically into the norm dual of S.
Conjugation accounts for the conjugate-linear predual isometry. These
functionals preserve monotone order limits. No canonical-predual membership
or weak-operator continuity is assumed. -/
section
open Filter
open scoped Topology ComplexConjugate
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Evaluation by x, made complex-linear in the algebra argument. -/
def predualFunctional (x : X) : StrongDual ℂ S :=
  LinearMap.mkContinuous
    { toFun := fun a => conj (e.symm a x)
      map_add' := by intros; simp
      map_smul' := by
        intro c a
        rw [e.symm.map_smulₛₗ]
        simp }
    ‖x‖ (by
      intro a
      change ‖conj (e.symm a x)‖ ≤ ‖x‖ * ‖a‖
      simp only [Complex.norm_conj]
      exact ((e.symm a).le_opNorm x).trans_eq (by rw [e.symm.norm_map, mul_comm]))

@[simp] theorem predualFunctional_apply (x : X) (a : S) :
    predualFunctional S e x a = conj (e.symm a x) := rfl

end

/-! An arbitrary net squeezed into shrinking operator order intervals
converges in the topology of the given Banach predual. The net itself need
not be monotone. No normal-functional decomposition is used. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! An actual separable Banach predual for the constructed matrix-generated
factor. The existential convention is exactly Generator.HasSeparablePredual. -/

/-! Separability of the actual cyclic predual implies separability of the
trace-vector orbit. This does not identify an arbitrary given Banach predual
with the cyclic predual. -/

/-! The given predual as a closed separating subspace of the algebra norm dual, with its evaluation duality. -/
section
open scoped ComplexConjugate
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Keep the norm topology explicit through the nested dual construction. -/
instance predualAlgebraDualNormed : NormedAddCommGroup (StrongDual ℂ S) := inferInstance

end

/-! Hahn–Banach comparison of preduals from normal-functional membership and evaluation surjectivity. -/

/-! Conditional comparison with the constructed cyclic predual. Membership
of the given-predual evaluations in that space is an explicit unproved input;
it is not obtained merely from their order-limit convergence. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

inductive RelativePolynomial (A : Type*) where
  | coeff : A → RelativePolynomial A
  | indeterminate : RelativePolynomial A
  | add : RelativePolynomial A → RelativePolynomial A → RelativePolynomial A
  | mul : RelativePolynomial A → RelativePolynomial A → RelativePolynomial A
  | smul : ℂ → RelativePolynomial A → RelativePolynomial A
  | adjoint : RelativePolynomial A → RelativePolynomial A

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/
section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}
  {T : StarSubalgebra ℂ (K →L[ℂ] K)}

/-- Ambient concrete inverse image, contained in S. -/
def concretePreimage (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (Q.comap (T.subtype.comp φ)).map S.subtype

/-! Transport of the unchanged finite diffuse factor predicate.
The algebraic fields use the actual star isomorphism; target WOT closedness
is explicit. No trace or separability conclusion is inferred. -/

end

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

theorem traceHilbertVonNeumann_wotClosed {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (P : VonNeumannAlgebra J) : WOTClosed P.toStarSubalgebra := by
  change IsClosed {T : J →WOT[ℂ] J | T.toCLM ∈ (P : Set (J →L[ℂ] J))}
  rw [← P.centralizer_centralizer]
  change IsClosed {T : J →WOT[ℂ] J |
    ∀ S ∈ Set.centralizer (P : Set (J →L[ℂ] J)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : J →WOT[ℂ] J | S*T.toCLM=T.toCLM*S} =
      {T : J →WOT[ℂ] J |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (J →WOT[ℂ] J) ≃ (J →L[ℂ] J) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

theorem traceSymmetrize_mem_original (a : M.toStarSubalgebra) (ha : a.val ∈ Q) :
    (traceSymmetrize a).val ∈ Q := by
  have hs : star a.val ∈ Q := star_mem ha
  exact Q.smul_mem (Q.add_mem ha hs) _

end Tracial

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_Topology
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

universe level

namespace RelativeGeneration

variable {Hilbert : Type level} [NormedAddCommGroup Hilbert]
  [InnerProductSpace ℂ Hilbert] [CompleteSpace Hilbert]

/-- A metric presentation with the trace two-distance gives precisely the trace-ball topology
on all genuine unitaries. -/
def traceUnitaryHomeomorph (algebra : StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert))
    (trace : algebra →L[ℂ] ℂ) {UnitarySpace : Type*} [MetricSpace UnitarySpace]
    (unitaryEquiv : UnitarySpace ≃ unitary algebra)
    (distance_eq : ∀ first second, dist first second =
      traceDistance algebra trace (unitaryEquiv first) (unitaryEquiv second)) :
    @Homeomorph UnitarySpace (unitary algebra) inferInstance (traceTopology algebra trace) := by
  letI : TopologicalSpace (unitary algebra) := traceTopology algebra trace
  refine { unitaryEquiv with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_generateFrom_iff.mpr
    rintro ball ⟨center, radius, _, rfl⟩
    have preimage_ball : unitaryEquiv ⁻¹'
        {point | traceDistance algebra trace center point < radius} =
        Metric.ball (unitaryEquiv.symm center) radius := by
      ext point
      change traceDistance algebra trace center (unitaryEquiv point) < radius ↔
        dist point (unitaryEquiv.symm center) < radius
      rw [dist_comm, distance_eq, unitaryEquiv.apply_symm_apply]
    change IsOpen (unitaryEquiv ⁻¹' {point | traceDistance algebra trace center point < radius})
    rw [preimage_ball]
    exact Metric.isOpen_ball
  · apply continuous_def.mpr
    intro openSet isOpenSet
    refine isOpen_iff_forall_mem_open.mpr ?_
    intro point point_mem
    obtain ⟨radius, radius_pos, ball_subset⟩ :=
      Metric.isOpen_iff.mp isOpenSet (unitaryEquiv.symm point) point_mem
    refine ⟨{candidate | traceDistance algebra trace point candidate < radius}, ?_,
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨point, radius, radius_pos, rfl⟩, ?_⟩
    · intro candidate candidate_mem
      apply ball_subset
      change dist (unitaryEquiv.symm candidate) (unitaryEquiv.symm point) < radius
      rw [dist_comm, distance_eq, unitaryEquiv.apply_symm_apply, unitaryEquiv.apply_symm_apply]
      exact candidate_mem
    · change traceDistance algebra trace point point < radius
      calc
        traceDistance algebra trace point point =
            dist (unitaryEquiv.symm point) (unitaryEquiv.symm point) := by
          simpa only [unitaryEquiv.apply_symm_apply] using
            (distance_eq (unitaryEquiv.symm point) (unitaryEquiv.symm point)).symm
        _ = 0 := dist_self _
        _ < radius := radius_pos

end RelativeGeneration

end

end OAI
end


