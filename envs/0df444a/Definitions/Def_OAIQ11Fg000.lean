-- Prove2me | Definitions.Def_OAIQ11Fg000
-- name    : OAIQ11Fg000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:28:52.333544+00:00
-- url     : https://prove2.me/theorems/5f9b1495-62ad-4555-beb2-e92b4e998e00
-- title:
--   Definitions bundle OAIQ11Fg000 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 100 declarations of OpenAI's Lean: 38 definitions, 3 inductive types or structures, 4 instances and 55 theorems. The definitions and types are `OAI.FreeGroupFactorMain.GroupHilbert`, `OAI.FreeGroupFactorMain.GroupOperator`, `OAI.FreeGroupFactorMain.hilbertReindex`, `OAI.FreeGroupFactorMain.leftRegular`, `OAI.FreeGroupFactorMain.ultraweakOperatorTopology`, `OAI.Generator.Bell.leftEntry`, `OAI.Generator.Bell.projection`, `OAI.Generator.CommutingProjectionEncoding.tail`, `OAI.Generator.CommutingProjectionEncoding.weight`, `OAI.Generator.FiniteHilbert`, `OAI.Generator.FiniteMatrixStage`, `OAI.Generator.FiniteMatrixStage.TensorExtension`, `OAI.Generator.FreeConvolution.Letter`, `OAI.Generator.MatrixUnitSystem`, `OAI.Generator.MatrixUnitSystem.algebra`, `OAI.Generator.MatrixUnitSystem.commutant`, `OAI.Generator.MatrixUnitSystem.hom`, `OAI.Generator.MatrixUnitSystem.linearMap`, `OAI.Generator.MatrixUnitSystem.map`, `OAI.Generator.MatrixUnitSystem.relativeStar`, `OAI.Generator.MatrixUnitSystem.relativeVonNeumann`, `OAI.Generator.Tracial.coordinateInclusion`, `OAI.Generator.normCoefficients`, `OAI.Generator.normalizedCorrelation`, `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.Ell2`, `OAI.UltrapowerBridge.TraceRel`, `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.TracialRepresentation.Algebra`, `OAI.UltrapowerBridge.TracialRepresentation.norm₂`, `OAI.UltrapowerBridge.TracialRepresentation.trace`, `OAI.UltrapowerBridge.boundedSequences`, `OAI.UltrapowerBridge.leftRegular`, `OAI.UltrapowerBridge.quotientMap`, `OAI.UltrapowerBridge.quotientTrace`, `OAI.UltrapowerBridge.reindex`, `OAI.UltrapowerBridge.reindexVector`, `OAI.UltrapowerBridge.rightRegular`, `OAI.UltrapowerBridge.traceCongruence` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Bicommutant`, `FactorGeneration_Coefficients`, `FactorGeneration_Convolution`, `FactorGeneration_GroupTrace`, `FactorGeneration_HilbertProjections`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixSequence`, `FactorGeneration_MatrixUnits`, `FactorGeneration_ProjectionEncoding`, `FactorGeneration_TensorRefinement`, `FactorGeneration_TracialInclusion`, `FactorGeneration_Ultrapower`, `FreeGroupFactor_Model`, `FreeGroupFactor_Operators`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg003`, `OAIQ11Fg004` and `OAIQ11Fg006`; the statements `OAI_Generator_FiniteMatrixStage_exists_irreducible_matrix_sequence`, `OAI_Generator_MatrixUnitSystem_two_generators_of_four_commutant_generators`, `OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra`, `OAI_Generator_Tracial_bounded_coordinate_unitaries_inclusion`, `OAI_Generator_Tracial_exists_finite_partial_independence`, `OAI_Generator_Tracial_exists_irreducible_centered_partition`, `OAI_Generator_Tracial_exists_irreducible_corner_zero_trace_partition`, `OAI.Generator.Tracial.exists_matrixUnits_for_partition`, `OAI.Generator.Tracial.exists_normal_matrix_approximation`, `OAI_Generator_Tracial_exists_represented_perturbation`, `OAI_Generator_Tracial_exists_scalar_pinching_for_matrixUnits`, `OAI_Generator_Tracial_exists_supported_centered_contraction`, `OAI_Generator_Tracial_predualFunctional_unitBall_continuous`, `OAI.Generator.Tracial.predual_small_of_small_trace_sandwich`, `OAI_Generator_Tracial_quotientMap_eq_of_eventuallyEq`, `OAI_Generator_Tracial_represented_four_selfAdjoint_generators`, `OAI_Generator_Tracial_represented_two_selfAdjoint_generators`, `OAI_Generator_Tracial_traceOrbit_isSeparable_of_separablePredual` and `OAI_UltrapowerBridge_quotientTrace_mul_comm`; the proofs of `OAI_Generator_Tracial_unitary_norm_le` and `OAI_UltrapowerBridge_quotientTrace_mul_comm`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ11_FG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Bicommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

abbrev FiniteHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Coefficientwise absolute-value product comparison, retaining all convolution terms contributing to the same group element. -/
section
open scoped BigOperators
variable {G : Type*} [Monoid G]

def normCoefficients (f : MonoidAlgebra ℂ G) : MonoidAlgebra ℝ G :=
  .ofCoeff (f.coeff.mapRange (fun z => ‖z‖) norm_zero)

omit [Monoid G] in
@[simp] theorem normCoefficients_apply (f : MonoidAlgebra ℂ G) (g : G) :
    (normCoefficients f).coeff g = ‖f.coeff g‖ := rfl

end

/-! The coefficientwise ordered ring of real finite group-ring sums.
The multiplication is actual collected convolution. -/
open scoped BigOperators
namespace CoefficientOrder
variable {G : Type*} [Monoid G]

instance coefficientPartialOrder : PartialOrder (MonoidAlgebra ℝ G) :=
  PartialOrder.lift MonoidAlgebra.coeff MonoidAlgebra.coeff_injective

omit [Monoid G] in
@[simp] theorem le_iff (f g : MonoidAlgebra ℝ G) : f ≤ g ↔ ∀ w, f.coeff w ≤ g.coeff w := Iff.rfl

instance coefficientOrderedAdd : IsOrderedAddMonoid (MonoidAlgebra ℝ G) where
  add_le_add_left _f _g h _a w := add_le_add (h w) le_rfl

instance coefficientZeroLEOne : ZeroLEOneClass (MonoidAlgebra ℝ G) where
  zero_le_one := by
    intro w
    classical
    simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> norm_num

end CoefficientOrder

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Convolution
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}
abbrev Letter (A : Type*) := A × Bool

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FreeGroupFactor_Model
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u uG

open scoped ENNReal

abbrev GroupHilbert (G : Type u) := lp (fun _ : G => ℂ) 2
abbrev GroupOperator (G : Type u) := GroupHilbert G →L[ℂ] GroupHilbert G

@[instance_reducible] def ultraweakOperatorTopology (G : Type u) : TopologicalSpace (GroupOperator G) :=
  ⨅ (ξ : lp (fun _ : ℕ => GroupHilbert G) 2)
    (η : lp (fun _ : ℕ => GroupHilbert G) 2),
    TopologicalSpace.induced
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (T (ξ k)))
      inferInstance

end FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_42 u_43

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FreeGroupFactor_Operators
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def hilbertReindex {G : Type uG} {H : Type uH} (e : G ≃ H) :
    GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H where
  toFun ξ := ⟨fun h => ξ (e.symm h), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun η := ⟨fun g => η (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp η).summable (by norm_num))⟩
  left_inv ξ := by ext g; simp
  right_inv η := by ext h; simp
  map_add' ξ η := by rfl
  map_smul' c ξ := by rfl
  norm_map' ξ := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change (∑' h : H, ‖ξ (e.symm h)‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) =
      (∑' g : G, ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal))

@[simp] theorem hilbertReindex_apply {G : Type uG} {H : Type uH} (e : G ≃ H)
    (ξ : GroupHilbert G) (h : H) : hilbertReindex e ξ h = ξ (e.symm h) := rfl

def leftRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulLeft g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : leftRegular g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem leftRegular_one {G : Type uG} [Group G] :
    leftRegular (1 : G) = 1 := by
  ext ξ h
  simp

@[simp] theorem leftRegular_mul {G : Type uG} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext ξ b
  simp [mul_assoc]

@[simp] theorem leftRegular_star {G : Type uG} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulLeft g)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (g * b) = ξ ((g⁻¹)⁻¹ * b)
  simp

end FreeGroupFactorMain

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped ENNReal Pointwise
abbrev Ell2 (G : Type*) := FreeGroupFactorMain.GroupHilbert G
local instance groupAlgebraDecEq_rd2f871_1 (G : Type*) : DecidableEq G := Classical.decEq _
/-- Reindex a square-summable vector by a permutation. -/
abbrev reindexVector {G : Type*} (e : G ≃ G) (f : Ell2 G) : Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e f

@[simp] theorem reindexVector_apply {G : Type*} (e : G ≃ G) (f : Ell2 G) (g : G) :
    reindexVector e f g = f (e.symm g) := rfl

/-- The bounded unitary implementation of a permutation on ell2. -/
abbrev reindex {G : Type*} (e : G ≃ G) : Ell2 G ≃ₗᵢ[ℂ] Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e

/-- The left regular operator, constructed on every square-summable vector. -/
abbrev leftRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  FreeGroupFactorMain.leftRegular g

@[simp] theorem leftRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    leftRegular g f b = f (g⁻¹ * b) := rfl

@[simp] theorem leftRegular_one {G : Type*} [Group G] : leftRegular (1 : G) = 1 := by
  ext f b
  simp

@[simp] theorem leftRegular_mul {G : Type*} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext f b
  simp

variable (G : Type*) [Group G]

variable {G}
@[simp] theorem leftRegular_star {G : Type*} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((reindex (Equiv.mulLeft g)) : Ell2 G →L[ℂ] Ell2 G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext f b
  change f (g * b) = f ((g⁻¹)⁻¹ * b)
  simp

/-- Right translations, needed to prove that the identity vector is separating. -/
def rightRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  (reindex (Equiv.mulRight g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    rightRegular g f b = f (b * g⁻¹) := rfl

end

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

@[simp] theorem trace_one : τ.trace 1 = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vector]

theorem trace_mul_comm (S T : Algebra (M := M)) : τ.trace (S*T) = τ.trace (T*S) :=
  τ.cyclic S T

theorem trace_star_mul (T : Algebra (M := M)) :
    τ.trace (star T*T) = (τ.norm₂ T : ℂ)^2 := by
  unfold trace norm₂
  change inner ℂ τ.vector ((star (T : H →L[ℂ] H)) ((T : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem norm₂_star (T : Algebra (M := M)) : τ.norm₂ (star T) = τ.norm₂ T := by
  have h := τ.trace_mul_comm (star T) T
  have h2 := τ.trace_star_mul (star T)
  simp only [star_star] at h2
  rw [τ.trace_star_mul, h2] at h
  have hr := congrArg Complex.re h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
  have hn : 0 ≤ τ.norm₂ T := norm_nonneg _
  have hs : 0 ≤ τ.norm₂ (star T) := norm_nonneg _
  nlinarith

@[simp] theorem norm₂_zero : τ.norm₂ 0 = 0 := by simp [norm₂]
@[simp] theorem norm₂_sub (S T : Algebra (M := M)) :
    τ.norm₂ (S-T) = ‖(S : H →L[ℂ] H) τ.vector - (T : H →L[ℂ] H) τ.vector‖ := rfl

theorem norm₂_add_le (S T : Algebra (M := M)) : τ.norm₂ (S+T) ≤ τ.norm₂ S+τ.norm₂ T :=
  norm_add_le _ _

theorem norm₂_mul_le (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ ‖S‖ * τ.norm₂ T :=
  (S : H →L[ℂ] H).le_opNorm ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_mul_le_right (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ τ.norm₂ S * ‖T‖ := by
  rw [← τ.norm₂_star (S*T), star_mul]
  have h := τ.norm₂_mul_le (star T) (star S)
  simpa [τ.norm₂_star, mul_comm, ContinuousLinearMap.star_eq_adjoint] using h

theorem norm₂_le_norm (T : Algebra (M := M)) : τ.norm₂ T ≤ ‖T‖ := by
  have h := (T : H →L[ℂ] H).le_opNorm τ.vector
  simpa [norm₂, τ.norm_vector] using h

theorem norm_trace_le_norm₂ (T : Algebra (M := M)) : ‖τ.trace T‖ ≤ τ.norm₂ T := by
  simpa [trace, norm₂, τ.norm_vector] using norm_inner_le_norm τ.vector ((T : H →L[ℂ] H) τ.vector)

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertProjections
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def normalizedCorrelation (ξ w : E) : ℝ := ‖inner ℂ ξ w‖ / ‖w‖

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

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

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

variable (τ : TracialRepresentation M) (l : Filter ℕ)
/-- The trace-null equivalence relation, before descending algebra operations. -/
def TraceRel (a b : Bounded M) : Prop :=
  Tendsto (fun n => τ.norm₂ (a.val n-b.val n)) l (𝓝 0)

theorem traceRel_refl (a : Bounded M) : TraceRel τ l a a := by
  simp only [TraceRel, sub_self, τ.norm₂_zero]
  exact tendsto_const_nhds

theorem traceRel_symm {a b : Bounded M} (h : TraceRel τ l a b) : TraceRel τ l b a := by
  simpa only [TraceRel, τ.norm₂_sub, norm_sub_rev] using h

theorem traceRel_trans {a b c : Bounded M}
    (hab : TraceRel τ l a b) (hbc : TraceRel τ l b c) : TraceRel τ l a c := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hbc)
  have he : a.val n-c.val n = (a.val n-b.val n)+(b.val n-c.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_add {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a+c) (b+d) := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hcd)
  change τ.norm₂ ((a.val n+c.val n)-(b.val n+d.val n)) ≤ _
  have he : (a.val n+c.val n)-(b.val n+d.val n) =
      (a.val n-b.val n)+(c.val n-d.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_mul {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a*c) (b*d) := by
  obtain ⟨C,hC,hc⟩ := c.property
  obtain ⟨B,hB,hb⟩ := b.property
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using (hab.mul_const C).add (hcd.const_mul B))
  change τ.norm₂ (a.val n*c.val n-b.val n*d.val n) ≤ _
  have he : a.val n*c.val n-b.val n*d.val n =
      (a.val n-b.val n)*c.val n+b.val n*(c.val n-d.val n) := by noncomm_ring
  rw [he]
  exact (τ.norm₂_add_le _ _).trans (add_le_add
    ((τ.norm₂_mul_le_right _ _).trans (mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _)))
    ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))))

theorem traceRel_star {a b : Bounded M} (hab : TraceRel τ l a b) :
    TraceRel τ l (star a) (star b) := by
  change Tendsto (fun n => τ.norm₂ (star (a.val n)-star (b.val n))) l (𝓝 0)
  simpa only [TraceRel, ← star_sub, τ.norm₂_star] using hab

/-- Algebra congruence proved from actual trace-norm estimates. -/
def traceCongruence : RingCon (Bounded M) where
  r := TraceRel τ l
  iseqv := ⟨traceRel_refl τ l, traceRel_symm τ l, traceRel_trans τ l⟩
  add' := traceRel_add τ l
  mul' := traceRel_mul τ l

/-- Underlying ring of the tracial ultrapower when l is a free ultrafilter. -/
abbrev TracialQuotient := (traceCongruence τ l).Quotient

def quotientMap : Bounded M →+* TracialQuotient τ l := (traceCongruence τ l).mk'

end

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance instStarTracialQuotient : Star (TracialQuotient τ l) :=
  ⟨Quotient.map' star (fun _ _ h => traceRel_star τ l h)⟩

@[simp] theorem quotientMap_star (a : Bounded M) :
    quotientMap τ l (star a) = star (quotientMap τ l a) := rfl

@[simp] theorem quotientMap_smul (c : ℂ) (a : Bounded M) :
    quotientMap τ l (c • a) = c • quotientMap τ l a := rfl

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem TracialRepresentation.trace_sub (a b : M.toStarSubalgebra) :
    τ.trace (a-b) = τ.trace a-τ.trace b := inner_sub_right _ _ _

@[simp] theorem TracialRepresentation.trace_add (a b : M.toStarSubalgebra) :
    τ.trace (a+b) = τ.trace a+τ.trace b := inner_add_right _ _ _

@[simp] theorem TracialRepresentation.trace_smul (c : ℂ) (a : M.toStarSubalgebra) :
    τ.trace (c • a) = c*τ.trace a := inner_smul_right _ _ _

def traceRep (a : Bounded M) : ℂ := limUnder (ω : Filter ℕ) (fun n => τ.trace (a.val n))

theorem traceRep_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.trace (a.val n)) (ω : Filter ℕ) (𝓝 (traceRep τ ω a)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨C,_,ha⟩ := a.property
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
    (ω.map (fun n => τ.trace (a.val n))) (by
      apply le_principal_iff.mpr
      change {n | τ.trace (a.val n) ∈ Metric.closedBall 0 C} ∈ (ω : Filter ℕ)
      exact Filter.Eventually.of_forall (fun n => by
        simpa using ((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (ha n)))
  exact ⟨z,hz⟩

theorem traceRep_eq_of_rel {a b : Bounded M} (h : TraceRel τ (ω : Filter ℕ) a b) :
    traceRep τ ω a = traceRep τ ω b := by
  have hz : Tendsto (fun n => ‖τ.trace (a.val n)-τ.trace (b.val n)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
    rw [← τ.trace_sub]
    exact τ.norm_trace_le_norm₂ _
  have hnorm := ((traceRep_tendsto τ ω a).sub (traceRep_tendsto τ ω b)).norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hnorm hz))

/-- The actual ultralimit trace on the operator-algebra quotient. -/
def quotientTrace : TracialQuotient τ (ω : Filter ℕ) → ℂ :=
  Quotient.lift (traceRep τ ω) (fun _ _ h => traceRep_eq_of_rel τ ω h)

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

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

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators
namespace Bell
variable {n : ℕ} [NeZero n]

theorem char_sum (t : ZMod n) :
    (∑ i : ZMod n, ZMod.stdAddChar (t*i)) = if t=0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

theorem char_star (t : ZMod n) : star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle t)).symm

def projection (s f : ZMod n) : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ :=
  fun a b => if a.2=a.1+s ∧ b.2=b.1+s then
    (n : ℂ)⁻¹ * ZMod.stdAddChar (f*(a.1-b.1)) else 0

theorem projection_star (s f : ZMod n) : star (projection s f) = projection s f := by
  ext a b
  change star (projection s f b a)=projection s f a b
  simp only [projection, apply_ite star, star_mul, char_star, star_zero]
  rw [show -(f*(b.1-a.1))=f*(a.1-b.1) by ring]
  simp [and_comm, mul_comm]

theorem projection_mul (s f t g : ZMod n) :
    projection s f * projection t g = if s=t ∧ f=g then projection s f else 0 := by
  ext a b
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, projection]
  have hterm (i j : ZMod n) :
      (if a.2=a.1+s ∧ j=i+s then (n : ℂ)⁻¹*ZMod.stdAddChar (f*(a.1-i)) else 0) *
      (if j=i+t ∧ b.2=b.1+t then (n : ℂ)⁻¹*ZMod.stdAddChar (g*(i-b.1)) else 0) =
      if a.2=a.1+s ∧ b.2=b.1+t ∧ s=t then
        if j=i+s then (n : ℂ)⁻¹^2 *
          ZMod.stdAddChar (f*a.1-g*b.1) * ZMod.stdAddChar ((g-f)*i) else 0
      else 0 := by
    by_cases ha : a.2=a.1+s
    · by_cases hb : b.2=b.1+t
      · by_cases hs : s=t
        · subst t
          by_cases hj : j=i+s
          · simp only [ha,hb,hj,and_self,ite_true, if_true]
            calc
              _ = (n : ℂ)⁻¹^2 * (ZMod.stdAddChar (f*(a.1-i)) *
                    ZMod.stdAddChar (g*(i-b.1))) := by ring
              _ = _ := by
                rw [← AddChar.map_add_eq_mul,
                  show f*(a.1-i)+g*(i-b.1)=(f*a.1-g*b.1)+(g-f)*i by ring,
                  AddChar.map_add_eq_mul]
                ring
          · simp [ha,hb,hj]
        · by_cases hj : j=i+s
          · simp [ha,hb,hs,hj]
          · simp [ha,hb,hs,hj]
      · simp [hb]
    · simp [ha]
  simp_rw [hterm]
  by_cases hs : s=t
  · subst t
    by_cases ha : a.2=a.1+s ∧ b.2=b.1+s
    · simp only [ha.1,ha.2,and_self,ite_true, if_true,Finset.sum_ite_eq',Finset.mem_univ]
      rw [← Finset.mul_sum, char_sum]
      by_cases hf : f=g
      · subst g
        simp only [sub_self,ite_true, if_true,Matrix.ite_apply,Matrix.zero_apply, and_self, projection, ha, ite_true]
        rw [show f*a.1-f*b.1=f*(a.1-b.1) by ring]
        field_simp
      · simp [sub_eq_zero,Ne.symm hf,hf]
    · simp [ha,Matrix.ite_apply,projection]
  · simp [hs]

theorem projection_total : (∑ s : ZMod n, ∑ f : ZMod n, projection s f) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.one_apply]
  have hf (s : ZMod n) : (∑ f : ZMod n, projection s f a b) =
      if a.2=a.1+s ∧ b.2=b.1+s ∧ a.1=b.1 then 1 else 0 := by
    simp only [projection]
    by_cases h : a.2=a.1+s ∧ b.2=b.1+s
    · simp only [h.1,h.2,and_self,true_and,ite_true, if_true]
      rw [← Finset.mul_sum]
      simp_rw [mul_comm _ (a.1-b.1)]
      rw [char_sum]
      by_cases hab : a.1=b.1
      · simp [hab]
      · simp [hab,sub_eq_zero]
    · simp [h,show ¬(a.2=a.1+s ∧ b.2=b.1+s ∧ a.1=b.1) by tauto]
  simp_rw [hf]
  by_cases hab : a.1=b.1
  · have hs (s : ZMod n) : a.2=a.1+s ↔ s=a.2-a.1 := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; abel
    simp_rw [hs]
    simp only [hab, and_true]
    simp_rw [ite_and]
    simp [Prod.ext_iff,hab,eq_comm]
  · simp [hab,show a≠b by exact fun h => hab (congrArg Prod.fst h)]

/-- The matrix unit in the first tensor factor, with identity on the second. -/
def leftEntry (i j : ZMod n) : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ :=
  fun a b => if a.1=i ∧ b.1=j ∧ a.2=b.2 then 1 else 0

end Bell

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A separated idempotent is recovered from commutation with a norm-small
perturbation. This is an elementary substitute for the spectral-cut step. -/

/-! Countably many commuting projections have one self-adjoint generator.
We use coefficients 3*4^(-(n+1)), whose strict gap admits direct norm recovery
through the double commutant. No trace, tensor model, or uniqueness is used. -/
namespace CommutingProjectionEncoding
open scoped BigOperators Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weight (n : ℕ) : ℝ := (3/4)*(1/4)^n

def tail (e : ℕ → (H →L[ℂ] H)) (n : ℕ) : (H →L[ℂ] H) := ∑' k, weight (n+k) • e (n+k)

end CommutingProjectionEncoding

/-! The spectral separation step as an exact membership theorem for literal W*. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TensorRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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


