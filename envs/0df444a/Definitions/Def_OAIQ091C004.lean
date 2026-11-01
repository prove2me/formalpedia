-- Prove2me | Definitions.Def_OAIQ091C004
-- name    : OAIQ091C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:47:50.740985+00:00
-- url     : https://prove2.me/theorems/669c73fc-6536-40dc-ad0c-868b1613fcd2
-- title:
--   Definitions bundle OAIQ091C004 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 131 declarations of OpenAI's Lean: 56 definitions, 9 instances and 66 theorems. The definitions and types are `OAI.PositiveEinsteinFour.HighestHessian.plusCoordinates`, `OAI.PositiveEinsteinFour.MomentObstruction.H`, `OAI.PositiveEinsteinFour.MomentObstruction.Phi`, `OAI.PositiveEinsteinFour.MomentObstruction.constraint`, `OAI.PositiveEinsteinFour.MomentObstruction.dualPolynomial`, `OAI.PositiveEinsteinFour.MomentObstruction.lowerPolynomial`, `OAI.PositiveEinsteinFour.MomentObstruction.potential`, `OAI.PositiveEinsteinFour.MomentObstruction.rootMoment`, `OAI.PositiveEinsteinFour.MomentObstruction.rootWeight`, `OAI.PositiveEinsteinFour.Potential.f0`, `OAI.PositiveEinsteinFour.Potential.f1`, `OAI.PositiveEinsteinFour.Potential.f2`, `OAI.PositiveEinsteinFour.Potential.f3`, `OAI.PositiveEinsteinFour.Potential.normalForm`, `OAI.PositiveEinsteinFour.Potential.q0`, `OAI.PositiveEinsteinFour.Potential.q1`, `OAI.PositiveEinsteinFour.Potential.q2`, `OAI.PositiveEinsteinFour.Potential.q3`, `OAI.PositiveEinsteinFour.Potential.q4`, `OAI.PositiveEinsteinFour.Quadratic.A12`, `OAI.PositiveEinsteinFour.Quadratic.K1`, `OAI.PositiveEinsteinFour.Quadratic.K12`, `OAI.PositiveEinsteinFour.Quadratic.K2`, `OAI.PositiveEinsteinFour.Quadratic.P0`, `OAI.PositiveEinsteinFour.Quadratic.Pk`, `OAI.PositiveEinsteinFour.Quadratic.Pl`, `OAI.PositiveEinsteinFour.Quadratic.Sbound`, `OAI.PositiveEinsteinFour.Quadratic.axialCoefficient`, `OAI.PositiveEinsteinFour.Quadratic.denominator`, `OAI.PositiveEinsteinFour.Quadratic.radialDenominator`, `OAI.PositiveEinsteinFour.Quadratic.weight`, `OAI.PositiveEinsteinFour.Quartic.A`, `OAI.PositiveEinsteinFour.Quartic.G`, `OAI.PositiveEinsteinFour.Quartic.H`, `OAI.PositiveEinsteinFour.Quartic.L`, `OAI.PositiveEinsteinFour.Quartic.Z`, `OAI.PositiveEinsteinFour.Quartic.discriminant`, `OAI.PositiveEinsteinFour.Quartic.projectionBound`, `OAI.PositiveEinsteinFour.Quartic.quarticMargin`, `OAI.PositiveEinsteinFour.QuarticEnergy.projectionCoefficient` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_Coupling`, `EinsteinFour_HVarianceApproximation`, `EinsteinFour_HighestActionCoordinates`, `EinsteinFour_LowerVolumeIntegral`, `EinsteinFour_MomentObstruction`, `EinsteinFour_NormVarianceApproximation`, `EinsteinFour_Potential`, `EinsteinFour_Quartic`, `EinsteinFour_QuarticEnergy`, `EinsteinFour_RadialIntegrals`, `EinsteinFour_Variance`, `EinsteinFour_VolumeConstants`, `EinsteinFour_WeylEstimates00`, `EinsteinFour_WeylEstimates01`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ091C012`; the proof of `OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ091_EF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
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

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration in the one-block vanishing argument

The scalar one-block vanishing argument in Section 8 of
*Positively curved Einstein four-manifolds* (23 September 2026). -/

namespace PositiveEinsteinFour

open MeasureTheory Filter

noncomputable section

/-- The rational weight `R_v` in equation (15). -/
def normWeight (v : ℝ) : ℝ := 4 * (1 + v) / (1 + 6 * v + v ^ 2)

end

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MomentObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct polynomial proof of the manuscript's two-constrained-moments
obstruction. The variable `x` is `sqrt(z/2)`. Four rational interval
certificates replace the compact-measure optimization argument. -/

namespace PositiveEinsteinFour.MomentObstruction

open MeasureTheory Filter

noncomputable section

def rootWeight (x : ℝ) : ℝ := 1 + x ^ 4 / 10 - x ^ 8 / 72
def rootMoment (x : ℝ) : ℝ := x * rootWeight x
def constraint (x : ℝ) : ℝ := 56 * x ^ 2 + 24 * x ^ 4 - 25
def potential (x : ℝ) : ℝ := 32 * rootMoment x ^ 2 + 18 * x ^ 2 - 36 * x ^ 4
def lowerPolynomial (x : ℝ) : ℝ := 32 * rootWeight x ^ 2 + 18 - 52 * x ^ 2
def dualPolynomial (x : ℝ) : ℝ :=
  (33 / 50) * rootMoment x * constraint x - (403 / 2000) * constraint x -
    (33 / 50) ^ 2 * constraint x ^ 2 / 128 + 18 * x ^ 2 - 36 * x ^ 4

/-- The scalar test function in the manuscript. -/
def H (z : ℝ) : ℝ := Real.sqrt z * (1 + z ^ 2 / 40 - z ^ 4 / 1152)

def Phi (z : ℝ) : ℝ := 16 * H z ^ 2 + 9 * z * (1 - z)

end

end PositiveEinsteinFour.MomentObstruction

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted Poisson argument and the scalar weight used to balance the
Weyl moments. The Bochner and Poisson identities imply the exact bound for the test
function, including zero norm values. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

noncomputable section

/-- The derivative of `H` relative to the derivative of the square root. -/
def derivativeRatio (b : ℝ) : ℝ := 1 + b ^ 2 / 8 - b ^ 4 / 128

end

end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HVarianceApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth approximation of the scalar test used in the weighted-variance
argument, with domination by the actual square-root energy. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

def hRegularizedArgument (b ε : ℝ) : ℝ := Real.sqrt (b ^ 2 + ε ^ 2)

def hRegularizedValue (b ε : ℝ) : ℝ := MomentObstruction.H (hRegularizedArgument b ε)

def hRegularizedDerivative (b ε : ℝ) : ℝ :=
  derivativeRatio (hRegularizedArgument b ε) /
    (2 * Real.sqrt (hRegularizedArgument b ε)) * (b / hRegularizedArgument b ε)

def hRegularizedEnergy (b ε E K : ℝ) : ℝ :=
  derivativeRatio (hRegularizedArgument b ε) ^ 2 *
    (b / hRegularizedArgument b ε) ^ 2 * E / (4 * hRegularizedArgument b ε * K)

def hLimitEnergy (b E K : ℝ) : ℝ := derivativeRatio b ^ 2 * E / (4 * b * K)

end
end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestActionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total plus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators

/-- The same action in the twenty-one actual free coordinates. -/
def plusCoordinates (s : Fin 3) (c : Fin 21 → ℝ) : Fin 21 → ℝ :=
  ![
    ![-6 * c 1 - 2 * c 12 - 2 * c 20,
      6 * c 0 + 4 * c 7 + 6 * c 15 - 2 * c 16 - 2 * c 17,
      -5 * c 3 - c 4 + c 13,
      5 * c 2 - c 5 - 3 * c 8 - 2 * c 14,
      c 2 - 5 * c 5 + c 18,
      c 3 + 5 * c 4 - 3 * c 13 - 2 * c 19,
      -2 * c 11,
      -4 * c 10 - 2 * c 12,
      -2 * c 9 - 2 * c 13,
      2 * c 8 - 2 * c 14,
      2 * c 6 + 4 * c 7 - 2 * c 15,
      c 6 - c 16,
      c 7 - 4 * c 15 - c 17,
      c 8 - 2 * c 14 - c 18,
      c 9 + 2 * c 13 - c 19,
      c 10 + 2 * c 11 + 4 * c 12 - c 20,
      2 * c 11,
      2 * c 12 - 4 * c 20,
      2 * c 13 - 2 * c 19,
      2 * c 14 + 2 * c 18,
      2 * c 15 + 2 * c 16 + 4 * c 17],
    ![2 * c 4,
      2 * c 2 + 4 * c 5,
      -c 1 - c 20,
      c 0 + 3 * c 7 + 4 * c 15,
      -c 0 + c 17,
      -c 1 + 2 * c 12 + 3 * c 20,
      6 * c 9 - 2 * c 13,
      -2 * c 3 + 2 * c 13,
      4 * c 10 - 2 * c 12,
      -6 * c 6 - 4 * c 7 - 2 * c 15,
      2 * c 2 - 4 * c 8,
      c 8 + 6 * c 14 - c 18,
      -c 2 - c 5 + c 18,
      c 7 + 4 * c 15 - c 17,
      c 10 - 6 * c 11 - 4 * c 12 - c 20,
      -c 3 + c 4 - 3 * c 13,
      2 * c 13 + 6 * c 19,
      -2 * c 4,
      2 * c 12 + 4 * c 20,
      2 * c 15 - 6 * c 16 - 4 * c 17,
      -2 * c 5 - 2 * c 18],
    ![-6 * c 2 - 4 * c 5,
      -4 * c 3 + 2 * c 4 - 2 * c 13 - 2 * c 19,
      c 0 - 5 * c 7 - 4 * c 15,
      c 1 - 3 * c 10 + 2 * c 11 + 2 * c 12,
      -c 1 - 6 * c 12 - 5 * c 20,
      c 0 + c 7 - 2 * c 15 + 2 * c 16 + 2 * c 17,
      -6 * c 8 - 2 * c 14,
      2 * c 2 + 4 * c 8,
      2 * c 6 - 4 * c 7 - 2 * c 15,
      -4 * c 10 + 2 * c 11 + 2 * c 12,
      2 * c 3 + 2 * c 9,
      c 9 - 6 * c 13 - c 19,
      -c 3 + c 4 + 5 * c 13,
      c 10 + 2 * c 11 - 4 * c 12 - c 20,
      -c 6 - c 7 - 4 * c 15 + c 16 + c 17,
      c 2 + c 5 - c 8 + 2 * c 14,
      2 * c 14 - 6 * c 18,
      -2 * c 5 + 6 * c 18,
      2 * c 15 + 2 * c 16 - 4 * c 17,
      -2 * c 11 - 2 * c 12 - 4 * c 20,
      2 * c 4 - 2 * c 13 + 2 * c 19]
  ] s

@[simp] theorem plusCoordinates_0_0 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 0 = -6 * c 1 - 2 * c 12 - 2 * c 20 := rfl

@[simp] theorem plusCoordinates_0_1 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 1 = 6 * c 0 + 4 * c 7 + 6 * c 15 - 2 * c 16 - 2 * c 17 := rfl

@[simp] theorem plusCoordinates_0_2 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 2 = -5 * c 3 - c 4 + c 13 := rfl

@[simp] theorem plusCoordinates_0_3 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 3 = 5 * c 2 - c 5 - 3 * c 8 - 2 * c 14 := rfl

@[simp] theorem plusCoordinates_0_4 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 4 = c 2 - 5 * c 5 + c 18 := rfl

@[simp] theorem plusCoordinates_0_5 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 5 = c 3 + 5 * c 4 - 3 * c 13 - 2 * c 19 := rfl

@[simp] theorem plusCoordinates_0_6 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 6 = -2 * c 11 := rfl

@[simp] theorem plusCoordinates_0_7 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 7 = -4 * c 10 - 2 * c 12 := rfl

@[simp] theorem plusCoordinates_0_8 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 8 = -2 * c 9 - 2 * c 13 := rfl

@[simp] theorem plusCoordinates_0_9 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 9 = 2 * c 8 - 2 * c 14 := rfl

@[simp] theorem plusCoordinates_0_10 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 10 = 2 * c 6 + 4 * c 7 - 2 * c 15 := rfl

@[simp] theorem plusCoordinates_0_11 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 11 = c 6 - c 16 := rfl

@[simp] theorem plusCoordinates_0_12 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 12 = c 7 - 4 * c 15 - c 17 := rfl

@[simp] theorem plusCoordinates_0_13 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 13 = c 8 - 2 * c 14 - c 18 := rfl

@[simp] theorem plusCoordinates_0_14 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 14 = c 9 + 2 * c 13 - c 19 := rfl

@[simp] theorem plusCoordinates_0_15 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 15 = c 10 + 2 * c 11 + 4 * c 12 - c 20 := rfl

@[simp] theorem plusCoordinates_0_16 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 16 = 2 * c 11 := rfl

@[simp] theorem plusCoordinates_0_17 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 17 = 2 * c 12 - 4 * c 20 := rfl

@[simp] theorem plusCoordinates_0_18 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 18 = 2 * c 13 - 2 * c 19 := rfl

@[simp] theorem plusCoordinates_0_19 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 19 = 2 * c 14 + 2 * c 18 := rfl

@[simp] theorem plusCoordinates_0_20 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 20 = 2 * c 15 + 2 * c 16 + 4 * c 17 := rfl

@[simp] theorem plusCoordinates_1_0 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 0 = 2 * c 4 := rfl

@[simp] theorem plusCoordinates_1_1 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 1 = 2 * c 2 + 4 * c 5 := rfl

@[simp] theorem plusCoordinates_1_2 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 2 = -c 1 - c 20 := rfl

@[simp] theorem plusCoordinates_1_3 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 3 = c 0 + 3 * c 7 + 4 * c 15 := rfl

@[simp] theorem plusCoordinates_1_4 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 4 = -c 0 + c 17 := rfl

@[simp] theorem plusCoordinates_1_5 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 5 = -c 1 + 2 * c 12 + 3 * c 20 := rfl

@[simp] theorem plusCoordinates_1_6 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 6 = 6 * c 9 - 2 * c 13 := rfl

@[simp] theorem plusCoordinates_1_7 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 7 = -2 * c 3 + 2 * c 13 := rfl

@[simp] theorem plusCoordinates_1_8 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 8 = 4 * c 10 - 2 * c 12 := rfl

@[simp] theorem plusCoordinates_1_9 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 9 = -6 * c 6 - 4 * c 7 - 2 * c 15 := rfl

@[simp] theorem plusCoordinates_1_10 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 10 = 2 * c 2 - 4 * c 8 := rfl

@[simp] theorem plusCoordinates_1_11 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 11 = c 8 + 6 * c 14 - c 18 := rfl

@[simp] theorem plusCoordinates_1_12 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 12 = -c 2 - c 5 + c 18 := rfl

@[simp] theorem plusCoordinates_1_13 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 13 = c 7 + 4 * c 15 - c 17 := rfl

@[simp] theorem plusCoordinates_1_14 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 14 = c 10 - 6 * c 11 - 4 * c 12 - c 20 := rfl

@[simp] theorem plusCoordinates_1_15 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 15 = -c 3 + c 4 - 3 * c 13 := rfl

@[simp] theorem plusCoordinates_1_16 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 16 = 2 * c 13 + 6 * c 19 := rfl

@[simp] theorem plusCoordinates_1_17 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 17 = -2 * c 4 := rfl

@[simp] theorem plusCoordinates_1_18 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 18 = 2 * c 12 + 4 * c 20 := rfl

@[simp] theorem plusCoordinates_1_19 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 19 = 2 * c 15 - 6 * c 16 - 4 * c 17 := rfl

@[simp] theorem plusCoordinates_1_20 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 20 = -2 * c 5 - 2 * c 18 := rfl

@[simp] theorem plusCoordinates_2_0 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 0 = -6 * c 2 - 4 * c 5 := rfl

@[simp] theorem plusCoordinates_2_1 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 1 = -4 * c 3 + 2 * c 4 - 2 * c 13 - 2 * c 19 := rfl

@[simp] theorem plusCoordinates_2_2 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 2 = c 0 - 5 * c 7 - 4 * c 15 := rfl

@[simp] theorem plusCoordinates_2_3 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 3 = c 1 - 3 * c 10 + 2 * c 11 + 2 * c 12 := rfl

@[simp] theorem plusCoordinates_2_4 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 4 = -c 1 - 6 * c 12 - 5 * c 20 := rfl

@[simp] theorem plusCoordinates_2_5 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 5 = c 0 + c 7 - 2 * c 15 + 2 * c 16 + 2 * c 17 := rfl

@[simp] theorem plusCoordinates_2_6 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 6 = -6 * c 8 - 2 * c 14 := rfl

@[simp] theorem plusCoordinates_2_7 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 7 = 2 * c 2 + 4 * c 8 := rfl

@[simp] theorem plusCoordinates_2_8 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 8 = 2 * c 6 - 4 * c 7 - 2 * c 15 := rfl

@[simp] theorem plusCoordinates_2_9 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 9 = -4 * c 10 + 2 * c 11 + 2 * c 12 := rfl

@[simp] theorem plusCoordinates_2_10 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 10 = 2 * c 3 + 2 * c 9 := rfl

@[simp] theorem plusCoordinates_2_11 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 11 = c 9 - 6 * c 13 - c 19 := rfl

@[simp] theorem plusCoordinates_2_12 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 12 = -c 3 + c 4 + 5 * c 13 := rfl

@[simp] theorem plusCoordinates_2_13 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 13 = c 10 + 2 * c 11 - 4 * c 12 - c 20 := rfl

@[simp] theorem plusCoordinates_2_14 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 14 = -c 6 - c 7 - 4 * c 15 + c 16 + c 17 := rfl

@[simp] theorem plusCoordinates_2_15 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 15 = c 2 + c 5 - c 8 + 2 * c 14 := rfl

@[simp] theorem plusCoordinates_2_16 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 16 = 2 * c 14 - 6 * c 18 := rfl

@[simp] theorem plusCoordinates_2_17 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 17 = -2 * c 5 + 6 * c 18 := rfl

@[simp] theorem plusCoordinates_2_18 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 18 = 2 * c 15 + 2 * c 16 - 4 * c 17 := rfl

@[simp] theorem plusCoordinates_2_19 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 19 = -2 * c 11 - 2 * c 12 - 4 * c 20 := rfl

@[simp] theorem plusCoordinates_2_20 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 20 = 2 * c 4 - 2 * c 13 + 2 * c 19 := rfl


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_VolumeConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational integrations for the two volume margins. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory intervalIntegral

noncomputable section

def coefficients3 : List ℝ :=
  [0,
   0,
   0,
   0,
   0,
   0,
   0,
   (607573201 / 337500000),
   0,
   (-306685150357 / 173643750000),
   0,
   (-135232353083985393371 / 260465625000000000000),
   0,
   (1373915920394822497871201 / 2188822879687500000000000),
   0,
   (-75413266642703 / 328323431953125)]

def coefficients4 : List ℝ :=
  [0,
   0,
   0,
   0,
   0,
   0,
   (-228901607940150256386397 / 4377645759375000000000000),
   (277511380555616579483771 / 125075593125000000000000),
   (-650737227338084553261397 / 410404289941406250000000),
   (90092019317747091983771 / 46903347421875000000000),
   (-103650157254401643161257 / 17867941875000000000000),
   (11390703505018065378126733 / 1876133896875000000000000),
   (-1048724109786626929483771 / 187613389687500000000000),
   (9183941409583597502128799 / 2188822879687500000000000),
   (-75413266642703 / 46903347421875),
   (75413266642703 / 328323431953125)]

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RadialIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two analytic integral margins in the volume comparison. All numerical
bounds here follow from exact polynomial integrals and the proved sine bound;
no numerical integration or decimal error premise is used. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory

noncomputable section

def lowerKernel (u : ℝ) : ℝ :=
  (Real.pi ^ 3 / 27) * u ^ 2 * (u ^ 4 / 2 + u ^ 6 / 3) * Real.sin (Real.pi * u)

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_LowerVolumeIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact integral of the refined lower-volume comparison kernel. -/
namespace PositiveEinsteinFour.VolumeConstants
open MeasureTheory
noncomputable section

def lowerVolumeKernel (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 3 / 9) * u ^ 2 * Real.sin (Real.pi * u) + lowerKernel u

end
end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_NormVarianceApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated smooth approximation of both Weyl norms and their difference.
The gradient limit uses the actual zero-set support property. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter
open scoped _root_.Topology ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def regularizedRadialVector (b ε : ℝ) (p : F) : F :=
  (b / hRegularizedArgument b ε) • p

def regularizedNormEnergy (b ε K : ℝ) (p : F) : ℝ :=
  ‖regularizedRadialVector b ε p‖ ^ 2 / K

def regularizedDifferenceValue (v b ε : ℝ) : ℝ :=
  hRegularizedArgument v ε - hRegularizedArgument b ε

def regularizedDifferenceEnergy (v b ε K : ℝ) (p q : F) : ℝ :=
  ‖regularizedRadialVector v ε p - regularizedRadialVector b ε q‖ ^ 2 / K

end
end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The potential polynomial certificate

The five quotient polynomials and their quarter-interval Bernstein certificates
are those of Section 7, Lemma "The polynomial F" of the manuscript.
The polynomial identities and inequalities hold over the real numbers.
-/

namespace PositiveEinsteinFour.Potential

noncomputable section

def q0 (n : ℝ) : ℝ :=
  (17837 / 80) * n ^ 4 + (-50531 / 80) * n ^ 3 + (74179 / 80) * n ^ 2 + (-27869 / 80) * n + (641 / 15)

def q1 (n : ℝ) : ℝ :=
  (5687 / 40) * n ^ 6 + (47787 / 40) * n ^ 5 + (-60009 / 20) * n ^ 4 + (15206 / 5) * n ^ 3 + (-173651 / 120) * n ^ 2 + (28609 / 120) * n + (2641 / 60)

def q2 (n : ℝ) : ℝ :=
  (854819 / 240) * n ^ 7 + (-2708953 / 240) * n ^ 6 + (3899477 / 240) * n ^ 5 + (-197057 / 16) * n ^ 4 + (434263 / 90) * n ^ 3 + (-19423 / 20) * n ^ 2 + (2288 / 15) * n + (37 / 180)

def q3 (n : ℝ) : ℝ :=
  (431467 / 40) * n ^ 7 + (-198338 / 5) * n ^ 6 + (620453 / 10) * n ^ 5 + (-2004441 / 40) * n ^ 4 + (2521913 / 120) * n ^ 3 + (-84801 / 20) * n ^ 2 + (1906 / 5) * n + (299 / 120)

def q4 (n : ℝ) : ℝ :=
  (354025 / 16) * n ^ 7 + (-1369095 / 16) * n ^ 6 + (11028947 / 80) * n ^ 5 + (-1827129 / 16) * n ^ 4 + (247214 / 5) * n ^ 3 + (-154144 / 15) * n ^ 2 + (12268 / 15) * n + (62 / 15)

def f0 (n : ℝ) : ℝ :=
  n ^ 3 * (1 - n) *
    (53511 * n ^ 4 - 151593 * n ^ 3 + 222537 * n ^ 2 - 83607 * n + 10256) / 240

def f1 (n : ℝ) : ℝ :=
  n * (19389 * n ^ 5 - 418926 * n ^ 4 + 523719 * n ^ 3 -
    289776 * n ^ 2 + 67782 * n + 10564) / 60

def f2 (n : ℝ) : ℝ :=
  (-1260129 * n ^ 4 + 1370598 * n ^ 3 - 451164 * n ^ 2 + 23442 * n + 74) / 60

def f3 (n : ℝ) : ℝ := (-12200 * n ^ 2 + 2601 * n + 75) / 10

def normalForm (n t : ℝ) : ℝ :=
  f0 n + f1 n * t ^ 2 + f2 n * t ^ 4 + f3 n * t ^ 6 - (23 / 5) * t ^ 8

end

end PositiveEinsteinFour.Potential

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Quartic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar certificates for the quartic comparison

Exact rational signs for equation (20) and Lemma 7.2 of the manuscript.
The Bernstein expansions give exact rational coefficients and their signs.
-/

namespace PositiveEinsteinFour.Quartic

noncomputable section

def A (u : ℝ) : ℝ :=
  (67 / 50) * u ^ 2 + (67 / 50)

def G (u : ℝ) : ℝ :=
  (-9 / 800) * u ^ 4 + (-9 / 32) * u ^ 3 + (2889 / 3200) * u ^ 2 + (99 / 64) * u + (117 / 128)

def H (u : ℝ) : ℝ :=
  (315 / 512) * u ^ 4 + (243 / 256) * u ^ 3 + (2889 / 3200) * u ^ 2 + (81 / 256) * u + (3681 / 12800)

def L (u : ℝ) : ℝ :=
  (381 / 256) * u ^ 4 + (285 / 128) * u ^ 3 + (531 / 256) * u ^ 2 + (219 / 64) * u + (267 / 128)

def Z (u : ℝ) : ℝ := L u ^ 2 - 4 * A u * (G u + u ^ 2 * H u)

def discriminant (u : ℝ) : ℝ :=
  64 * A u ^ 2 * u ^ 2 * G u * H u - Z u ^ 2

/-- The upper bound for the projection coefficient after introducing the
nonnegative spectral defects `V = x-v` and `W = y-b`. -/
def projectionBound (v b V W : ℝ) : ℝ :=
  (7 / 12) * (4 + b + W) - v + 2 * V

/-- The difference between the two sides of the paper's equation (20). -/
def quarticMargin (v b V W P Q : ℝ) : ℝ :=
  (67 / 50 + 27 * v * b / 100) * (P ^ 2 + Q ^ 2) * (b * P ^ 2 + v * Q ^ 2) -
    ((27 / 128) * v * b * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) +
      (3 / 4) * v * b * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3))

end

end PositiveEinsteinFour.Quartic

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuarticEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full scalar quartic estimate, with both energy and spectral defects. -/

namespace PositiveEinsteinFour.QuarticEnergy

open Quartic

noncomputable section

/-- The coefficient `g` in the weighted Hessian projection bound. -/
def projectionCoefficient (v y σ ρ : ℝ) : ℝ :=
  (7 / 12) * (4 + y) - σ * v + ρ ^ 2 * v ^ 2 / 4

end
end PositiveEinsteinFour.QuarticEnergy

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

def weight (v b : ℝ) : ℝ := (1 - 3 * (v - b) / 8) ^ 2
def Pk (v b : ℝ) : ℝ := 300 * weight v b + 272 * (2 - v - b)
def Pl (v b : ℝ) : ℝ := 35 * weight v b * v
def P0 (v b : ℝ) : ℝ := Pk v b + 51 * v
def K2 (v b σ : ℝ) : ℝ :=
  weight v b * (42 + 3 * b ^ 2 + 10 * v ^ 2) -
    (17 / 10) * (6 * (σ * v ^ 2 + b ^ 2 - v - b) - 26 * (2 - v - b))
def K1 (v b σ : ℝ) : ℝ :=
  5 * K2 v b σ + weight v b * (300 * v * σ + 140 * v ^ 2) +
    272 * (2 - v - b) * v * σ
def K12 (v b σ : ℝ) : ℝ :=
  weight v b * (75 * v + 35 * v ^ 2 * σ) + 68 * (2 - v - b) * v
def A12 (v b σ : ℝ) : ℝ :=
  P0 v b * v * K12 v b σ - (1 + σ) * v ^ 2 * Pk v b * Pl v b

def denominator (v b : ℝ) : ℝ := 4 + v ^ 2 + b ^ 2
def radialDenominator (v : ℝ) : ℝ := 1 + 6 * v + v ^ 2
def axialCoefficient (v b : ℝ) : ℝ :=
  weight v b * (-70 + 100 * v - 25 * v ^ 2 - 5 * b ^ 2) +
    (17 / 6) * (6 * ((v - 1) ^ 2 + (b - 1) ^ 2) + 32 * (v - 1) * (2 - v - b))
def Sbound (v b : ℝ) : ℝ :=
  (41 / 5) * v * b + ((5 / 4) * b * (1 - v) ^ 2 + (4 / 5) * v * (1 - b) ^ 2) / 2

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Shifted positive Weyl coefficients give an upper bound on the scalar trace-free Hessian, using its actual nine real coefficients. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix HighestHessian

noncomputable section

def crossVector (t : Fin 3) (c : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![![0, -c 2, c 1], ![c 2, 0, -c 0], ![-c 1, c 0, 0]] t

end
end PositiveEinsteinFour.ScalarHessian
end


end OAI
end


