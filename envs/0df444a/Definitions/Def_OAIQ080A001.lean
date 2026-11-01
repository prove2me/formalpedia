-- Prove2me | Definitions.Def_OAIQ080A001
-- name    : OAIQ080A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:15:24.337678+00:00
-- url     : https://prove2.me/theorems/192a631e-4cfc-4f2b-a53c-f92da69eb1d6
-- title:
--   Definitions bundle OAIQ080A001 of the split of OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 92 definitions, 3 inductive types or structures, 11 instances and 34 theorems. The definitions and types are `OAI.BoltzmannNonuniqueness.Compactness.SupportedTest`, `OAI.BoltzmannNonuniqueness.Compactness.smoothTest`, `OAI.BoltzmannNonuniqueness.Compactness.supportedFn`, `OAI.BoltzmannNonuniqueness.Compactness.supportedSeq`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialEntropyCoefficient`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.maxwellianLower`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.windowInverseWeight`, `OAI.BoltzmannNonuniqueness.PeriodicExistenceInput`, `OAI.BoltzmannNonuniqueness.PositiveIteration.deletionCoefficient`, `OAI.BoltzmannNonuniqueness.PositiveMeasureHistories.historySum`, `OAI.BoltzmannNonuniqueness.PowerDiskMixture.mixingDensity`, `OAI.BoltzmannNonuniqueness.Published.FanPhase`, `OAI.BoltzmannNonuniqueness.Published.FanRemainder`, `OAI.BoltzmannNonuniqueness.Published.L1TruncationFamily`, `OAI.BoltzmannNonuniqueness.Published.L1TruncationLimit`, `OAI.BoltzmannNonuniqueness.Published.L1TruncationLimit.l1Value`, `OAI.BoltzmannNonuniqueness.Published.dampedCharacter`, `OAI.BoltzmannNonuniqueness.Published.entropyProduction`, `OAI.BoltzmannNonuniqueness.Published.fan`, `OAI.BoltzmannNonuniqueness.Published.l2Restrict`, `OAI.BoltzmannNonuniqueness.Published.survivalVolterra`, `OAI.BoltzmannNonuniqueness.Published.timeDifference`, `OAI.BoltzmannNonuniqueness.Published.timeExchange`, `OAI.BoltzmannNonuniqueness.Published.truncationError`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.CollisionWord`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.EventParameter`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.ThreeEvents`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.angularInterval`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.angularSquare`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamEntryMass`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.blockFirstTime`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.clockDensity`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedFiniteHistoryError`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedHistoryPerturbationError`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.firstEntryMass`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightWeight`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.growthDensity`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.growthWeight`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.realFlightWeight`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceClock` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Boltzmann_Admissibility`, `Boltzmann_Approximation_PositiveRestrictedChain`, `Boltzmann_Approximation_PositiveSourceFormula`, `Boltzmann_Branching_BoundedEntropyProduction`, `Boltzmann_Branching_BoundedMeshStep`, `Boltzmann_Branching_CompactParameterConvergence`, `Boltzmann_Branching_CumulativeIntervalBalance`, `Boltzmann_Branching_DampedCollisionHistories`, `Boltzmann_Branching_FanNullSet`, `Boltzmann_Branching_FirstEntryMass`, `Boltzmann_Branching_LinearCharacteristicBalance`, `Boltzmann_Branching_LogRenormalization`, `Boltzmann_Branching_LossIntegrability`, `Boltzmann_Branching_NormalReflectionGeometry`, `Boltzmann_Branching_PerturbedFiniteBlock`, `Boltzmann_Branching_PowerDiskMixture`, `Boltzmann_Branching_ProductionDualLimit`, `Boltzmann_Branching_PublishedInputs`, `Boltzmann_Branching_RationalUniformApproximation`, `Boltzmann_Branching_ReferenceAngularCharts`, `Boltzmann_Branching_ReferenceBranchingHistories`, `Boltzmann_Branching_ReferenceCollisionGeometry`, `Boltzmann_Branching_ReferenceFlightLaws`, `Boltzmann_Branching_ReferenceGrowthBlocks`, `Boltzmann_Branching_ReferenceHistoryMoments`, `Boltzmann_Branching_ReferenceMinorization`, `Boltzmann_Branching_SeparatedMeasureTail`, `Boltzmann_Branching_SmallFirstGain`, `Boltzmann_Branching_SmoothTestFamily`, `Boltzmann_Branching_TriangularLinearMap`, `Boltzmann_Branching_TruncatedExponential`, `Boltzmann_Branching_ZeroProfileParameters`, `Boltzmann_Collision_AngularPairTests`, `Boltzmann_Collision_CollisionParameterShuffle`, `Boltzmann_Collision_GaussianLocalExistence`, `Boltzmann_Collision_ScalarEntropyConvex`, `Boltzmann_Collision_SheetGain`, `Boltzmann_Collision_SphereAntipodal`, `Boltzmann_Collision_SphereIsometryMeasure`, `Boltzmann_Collision_TransverseAverage`, `Boltzmann_Collision_WeightAlgebra`, `Boltzmann_Compactness_ContinuationAdmissibility`, `Boltzmann_Compactness_EntropyDissipationAverage`, `Boltzmann_Compactness_EntropyIntegralBalance`, `Boltzmann_Compactness_L1TruncationCauchy`, `Boltzmann_Compactness_PeriodicInitialEntropyLimit`, `Boltzmann_Compactness_SelectedOriginDeletion`, `Boltzmann_Compactness_StrongCompactPairTests`, `Boltzmann_Compactness_WeakConservedMarginal`, `Boltzmann_Compactness_WeakL1Operations`, `Boltzmann_Jets_ColdMildRepresentative`, `Boltzmann_Jets_TorusChart`, `Boltzmann_Model`.
--
--   **Imports.** It imports the published bundle `Def_BoltzmannNonuniqueness`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ080A002`; the statement `OAI.BoltzmannNonuniqueness.periodicExistenceInput_q80`.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit 1581d4c

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness

section
-- module Solutions.OAIQ080_BZ.Compat
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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
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
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision model for periodic hard spheres

The normal parametrization and absolute angular kernel here are exactly those of
Sections 1–2 of the paper.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- A Gaussian with arbitrary amplitude, exponent, and center. -/
def gaussian (A β : ℝ) (u v : Velocity) : ℝ := A * Real.exp (-β * ‖v - u‖ ^ 2)

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Admissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The entropy-class solution and nonuniqueness statement

The solution class follows Definition 2.1 with explicit integrability conditions.
The renormalized equation uses derivatives of smooth periodic lifts, while
integrals use volume on the unit torus and Euclidean velocity space.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

/-- Periodic existence for continuation, as in Levermore–Masmoudi (2010), Theorem 4.1,
including separate renormalized gain and loss integrability. -/
def PeriodicExistenceInput : Prop :=
  ∀ f₀ : Density, FiniteEntropyDatum f₀ → ∃ F : Evolution, AdmissibleGlobal f₀ F

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CompactParameterConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact time primitives for the characteristic weak equation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def primitive (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in a..t, f s

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem sphereArea_real_univ : sphereArea.real univ = 4 * Real.pi := by
  rw [sphereArea, Measure.toSphere_real_apply_univ]
  simp only [Fintype.card_fin, finrank_euclideanSpace]
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  norm_num
  ring

theorem gaussian_radial_one :
    (∫ r : ℝ in Ioi 0, r * Real.exp (-r ^ 2)) = 1 / 2 := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r : ℝ => Real.exp (-r ^ 2))
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin 2)) (b := 1) zero_lt_one
  simp only [one_mul, neg_mul, finrank_euclideanSpace, Fintype.card_fin] at hg
  rw [hg] at h
  rw [Measure.real, EuclideanSpace.volume_ball_fin_two] at h
  norm_num [ENNReal.toReal_ofReal, Real.pi_pos.le] at h
  nlinarith [Real.pi_pos]

theorem gaussian_radial_three :
    (∫ r : ℝ in Ioi 0, r ^ 3 * Real.exp (-r ^ 2)) = 1 / 2 := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun r : ℝ => Real.exp (-r ^ 2))
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin 4)) (b := 1) zero_lt_one
  simp only [one_mul, neg_mul, finrank_euclideanSpace, Fintype.card_fin] at hg
  rw [hg] at h
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)] at h
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  norm_num at h
  nlinarith [sq_pos_of_pos Real.pi_pos]

theorem gaussian_abs_integral :
    (∫ x : ℝ, |x| * Real.exp (-x ^ 2)) = 1 := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ)
    (fun r : ℝ => r * Real.exp (-r ^ 2))
  norm_num [Measure.real, Real.volume_ball, Real.norm_eq_abs, sq_abs,
    gaussian_radial_one] at h
  exact h

theorem gaussian_coordinate_integral :
    (∫ x : Velocity, |x 0| * Real.exp (-‖x‖ ^ 2)) = Real.pi := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  let f : Fin 3 → ℝ → ℝ := fun i t =>
    if i = 0 then |t| * Real.exp (-t ^ 2) else Real.exp (-t ^ 2)
  have hf : ∀ x : Fin 3 → ℝ,
      |WithLp.toLp 2 x 0| * Real.exp (-‖WithLp.toLp 2 x‖ ^ 2) = ∏ i, f i (x i) := by
    intro x
    simp [f, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Real.exp_add, mul_assoc]
    left
    ring
  have hg : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian 1
  simp_rw [hf]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [f, Fin.prod_univ_succ, gaussian_abs_integral, hg,
    Real.sq_sqrt Real.pi_pos.le]

theorem gaussian_linear_integral (g : Velocity) :
    (∫ x : Velocity, |inner ℝ g x| * Real.exp (-‖x‖ ^ 2)) = Real.pi * ‖g‖ := by
  let a : Velocity := EuclideanSpace.single 0 ‖g‖
  let R : Velocity ≃ₗᵢ[ℝ] Velocity := (ℝ ∙ (g - a))ᗮ.reflection
  have hnorm : ‖g‖ = ‖a‖ := by simp [a, EuclideanSpace.single, PiLp.norm_single]
  have hRg : R g = a := Submodule.reflection_sub hnorm
  have hinner (x : Velocity) : inner ℝ g (R x) = ‖g‖ * x 0 := by
    have h := R.inner_map_eq_flip g x
    rw [hRg] at h
    simpa [R, a, EuclideanSpace.inner_single_left] using h.symm
  rw [← R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding]
  simp_rw [hinner, R.norm_map, abs_mul, abs_of_nonneg (norm_nonneg g), mul_assoc]
  rw [integral_const_mul, gaussian_coordinate_integral]
  ring

theorem gaussian_radial_weighted :
    (∫ r : Ioi (0 : ℝ), (r : ℝ) * Real.exp (-(r : ℝ) ^ 2)
      ∂Measure.volumeIoiPow 2) = 1 / 2 := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => r ^ 2 * (r * Real.exp (-r ^ 2)))]
  convert gaussian_radial_three using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext r
  ring

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LossIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Loss frequency and its first-moment bound

The angular normalization gives the loss-frequency formula from Section 2,
equation `eq:frequency`. Fubini is used only with an explicit integrability
hypothesis for the original collision integrand. Separate first-moment
conditions ensure that the frequency integral itself is finite.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

/-- The loss frequency in the paper's normal parametrization. -/
def frequency (f : Density) (x : Position) (v : Velocity) : ℝ :=
  2 * Real.pi * ∫ w : Velocity, ‖v - w‖ * f (x, w)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published analytic input for periodic hard-sphere nonuniqueness

`GLPS1988Proposition3` expresses the velocity-localized, time-dependent specialization of Proposition 3
of F. Golse, P.-L. Lions, B. Perthame and R. Sentis, "Regularity of the moments of the solution of
a transport equation", J. Functional Analysis 76 (1988), 110–125, pp. 115–116,
DOI: 10.1016/0022-1236(88)90051-1. The passage to evolution equations is explained in their
Remark (2), p. 119. In their notation, the velocity measure is supported on velocities `(1,v)`;
compact velocity support supplies their nonconcentration condition (2.14).

This compactness statement applies to uniformly integrable sources with bounded velocity
support, independently of the cap and branching constructions.

The global continuation input is Theorem 4.1 of C. D. Levermore and N. Masmoudi,
"From the Boltzmann equation to an incompressible Navier–Stokes–Fourier system",
Arch. Rational Mech. Anal. 196 (2010), 753–809, pp. 765–767,
DOI: 10.1007/s00205-009-0254-5. The elementary entropy estimate converts that
continuation theorem to separate gain and loss integrability.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

/-- The entropy-production integrand for strictly positive incoming and outgoing products. -/
def entropyProduction (A B : ℝ) : ℝ := (A - B) * Real.log (A / B)

/-! ## Scalar estimates in the reference branching process

The uniform distribution of a spherical coordinate gives a lower bound for
retention in the speed-five ball and a positive branching potential.
-/

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SphereAntipodal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Antipodal invariance of the actual angular area measure -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness

theorem sphereArea_antipodal :
    MeasurePreserving (Neg.neg : Sphere → Sphere) sphereArea sphereArea := by
  refine ⟨measurable_neg,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs]
  change (volume : Measure Velocity).toSphere (Neg.neg ⁻¹' s) =
    (volume : Measure Velocity).toSphere s
  rw [Measure.toSphere_apply' _ (measurable_neg hs),Measure.toSphere_apply' _ hs]
  have he : Ioo (0 : ℝ) 1 • ((↑) '' (Neg.neg ⁻¹' s)) =
      (Neg.neg : Velocity → Velocity) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,y,⟨n,hn,rfl⟩,rfl⟩
      change -(r • (n : Velocity)) ∈ Ioo (0 : ℝ) 1 • ((↑) '' s)
      exact ⟨r,hr,(-n : Velocity),⟨-n,hn,rfl⟩,by simp⟩
    · rintro ⟨r,hr,y,⟨n,hn,rfl⟩,hy⟩
      refine ⟨r,hr,(-n : Velocity),⟨-n,?_,rfl⟩,?_⟩
      · simpa using hn
      · simpa only [smul_neg,neg_neg] using congrArg Neg.neg hy
  rw [he,Measure.measure_preimage_neg]

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceCollisionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform angular caps about collision endpoints -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def sphereCapMass (r : ℝ) : ℝ := (Measure.toSphereBallBound 3 r : ℝ)/3

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalReflectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact reflected relative direction in the hard-sphere angular map -/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

def normalReflectionVector (g n : Velocity) : Velocity := g-(2*inner ℝ g n) • n

theorem normalReflectionVector_norm (g n : Velocity) (hn : ‖n‖ = 1) :
    ‖normalReflectionVector g n‖ = ‖g‖ := by
  have hs : ‖normalReflectionVector g n‖^2 = ‖g‖^2 := by
    unfold normalReflectionVector
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs,hn,mul_one]
    ring
  nlinarith [norm_nonneg (normalReflectionVector g n),norm_nonneg g]

def normalReflection (e n : Sphere) : Sphere :=
  ⟨normalReflectionVector e.1 n.1,by
    rw [Metric.mem_sphere,dist_zero_right,normalReflectionVector_norm _ _
      (mem_sphere_zero_iff_norm.mp n.property)]
    exact mem_sphere_zero_iff_norm.mp e.property⟩

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SphereIsometryMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal changes of coordinates preserve the actual sphere area measure -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness

def sphereIsometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) : Sphere ≃ᵐ Sphere where
  toFun n := ⟨R n.1,by simpa only [Metric.mem_sphere,dist_zero_right,R.norm_map] using n.property⟩
  invFun n := ⟨R.symm n.1,by simpa only [Metric.mem_sphere,dist_zero_right,R.symm.norm_map] using n.property⟩
  left_inv n := by apply Subtype.ext; exact R.symm_apply_apply _
  right_inv n := by apply Subtype.ext; exact R.apply_symm_apply _
  measurable_toFun := by
    exact (R.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    exact (R.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Transverse angular averages

The angular singularity in `ker:transverse-expectation` is integrable when
`q < 2`. Gaussian Cartesian integration and polar coordinates prove this
without choosing a trigonometric chart on the unit circle.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.TransverseAverage

def radialGaussian (q : ℝ) (r : Ioi (0 : ℝ)) : ℝ :=
  (r : ℝ) ^ (1 - q) * Real.exp (-(r : ℝ) ^ 2)

def radialCutoff (D : ℝ) (r : Ioi (0 : ℝ)) : ℝ :=
  if (r : ℝ) < D then (r : ℝ)⁻¹ else 0

end BoltzmannNonuniqueness.TransverseAverage

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TriangularLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertibility of a triangular scalar extension -/

noncomputable section

namespace BoltzmannNonuniqueness

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem triangular_bijective (L : P × ℝ →L[ℝ] P × ℝ)
    (hf : ∀ x, (L x).1 = x.1) (hd : (L (0,1)).2 ≠ 0) :
    Function.Bijective L := by
  have he (p : P) (u : ℝ) : (L (p,u)).2 = (L (p,0)).2 + u*(L (0,1)).2 := by
    have h : (p,u) = (p,0) + u • (0,1) := by ext <;> simp
    rw [h,map_add,map_smul]
    rfl
  constructor
  · rintro ⟨p,u⟩ ⟨q,v⟩ h
    have hp : p = q := by simpa only [hf] using congrArg Prod.fst h
    subst q
    refine Prod.ext rfl ?_
    have hu := congrArg Prod.snd h
    rw [he p u,he p v] at hu
    exact mul_right_cancel₀ hd (add_left_cancel hu)
  · rintro ⟨p,u⟩
    refine ⟨(p,(u-(L (p,0)).2)/(L (0,1)).2),?_⟩
    refine Prod.ext (hf _) ?_
    rw [he,div_mul_cancel₀ _ hd]
    ring

def triangularEquiv [FiniteDimensional ℝ P] (L : P × ℝ →L[ℝ] P × ℝ)
    (hf : ∀ x, (L x).1 = x.1) (hd : (L (0,1)).2 ≠ 0) :
    (P × ℝ) ≃L[ℝ] (P × ℝ) :=
  (LinearEquiv.ofBijective L.toLinearMap (triangular_bijective L hf hd)).toContinuousLinearEquiv

@[simp] theorem triangularEquiv_coe [FiniteDimensional ℝ P]
    (L : P × ℝ →L[ℝ] P × ℝ) (hf : ∀ x, (L x).1 = x.1)
    (hd : (L (0,1)).2 ≠ 0) : (triangularEquiv L hf hd).toContinuousLinearMap = L := rfl

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weight transfer on a collision plane

The exact Gaussian identity and polynomial transfer turn the normalized
gain weight into the tilted cold measure used in `ker:tilted-kernel`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.VelocityWeight

/-- The axial exponential moment removes the tilted large-velocity tail. -/
theorem axial_tilt_tail {a u : ℝ} (hu : 0 ≤ u) (ha : u ≤ |a|) :
    Real.exp (2 * a ^ 2) ≤ Real.exp (-6 * u ^ 2) * Real.exp (8 * a ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_abs a]

end BoltzmannNonuniqueness.VelocityWeight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyIntegralBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The regularized entropy primitive used at zeros of finite approximations -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

def scalarRelativeEntropy (m f : ℝ) : ℝ := f*Real.log f-f*(1+Real.log m)+m

def regularizedEntropy (m e δ f : ℝ) : ℝ :=
  scalarRelativeEntropy m (f+δ*e)-scalarRelativeEntropy m (δ*e)+m

end BoltzmannNonuniqueness

end

end

section

/-! # Integrating the entropy chain rule over the characteristic labels -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def entropyPath (a : Phase → ℝ) (r : ℝ × Phase → ℝ) (t : ℝ) (p : Phase) : ℝ :=
  a p+∫ s in 0..t, r (s,p)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_ScalarEntropyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded dual tests for relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

def entropyDual (m u s : ℝ) : ℝ := u*s-m*(Real.exp s-1)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exponential tilting of cold sheets

These are the transverse density domination and axial moment-tail estimates
used in the proof of the uniform sheet gain bound, Section 3.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.SheetTails

theorem integrable_axial_tilt {ρ : Measure ℝ}
    (hρ : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ) :
    Integrable (fun a : ℝ => Real.exp (2 * a ^ 2)) ρ := by
  apply hρ.mono' (by fun_prop)
  filter_upwards [] with a
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg a]

theorem integral_axial_tilt_le {ρ : Measure ℝ} {L : ℝ}
    (hρ : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ)
    (hL : (∫ a, Real.exp (8 * a ^ 2) ∂ρ) ≤ L) :
    (∫ a, Real.exp (2 * a ^ 2) ∂ρ) ≤ L := by
  apply le_trans (integral_mono (integrable_axial_tilt hρ) hρ _) hL
  intro a
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg a]

theorem integral_axial_tilt_tail_le {ρ : Measure ℝ} {L U : ℝ}
    (hρ : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ)
    (hL : (∫ a, Real.exp (8 * a ^ 2) ∂ρ) ≤ L) (hU : 0 ≤ U) :
    (∫ a in {a : ℝ | U < |a|}, Real.exp (2 * a ^ 2) ∂ρ) ≤
      Real.exp (-6 * U ^ 2) * L := by
  have hs : MeasurableSet {a : ℝ | U < |a|} := measurableSet_lt measurable_const measurable_abs
  calc
    _ ≤ ∫ a in {a : ℝ | U < |a|}, Real.exp (-6 * U ^ 2) * Real.exp (8 * a ^ 2) ∂ρ :=
      setIntegral_mono_on (integrable_axial_tilt hρ).integrableOn
        (hρ.const_mul _).integrableOn hs (fun a ha => axial_tilt_tail hU ha.le)
    _ = Real.exp (-6 * U ^ 2) * (∫ a in {a : ℝ | U < |a|}, Real.exp (8 * a ^ 2) ∂ρ) :=
      integral_const_mul _ _
    _ ≤ Real.exp (-6 * U ^ 2) * (∫ a, Real.exp (8 * a ^ 2) ∂ρ) :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hρ
        (Filter.Eventually.of_forall (fun a => (Real.exp_pos _).le))) (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hL (Real.exp_nonneg _)

end BoltzmannNonuniqueness.SheetTails

end

end

section

/-!
# Probability sheets and their exponential tilts

An elementary sheet is the coordinate pushforward of a centered transverse
Gaussian (or the atom at zero) and an arbitrary axial probability law. The axial
exponential-moment hypothesis is recorded explicitly. All domination statements
below are inequalities of measures, so they also apply to nonnegative kernels.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetTails

namespace BoltzmannNonuniqueness.SheetMeasures

/-- The exact axial hypothesis used throughout the sheet estimates. -/
structure AxialMoment (ρ : Measure ℝ) (L : ℝ) : Prop where
  integrable : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ
  bound : (∫ a, Real.exp (8 * a ^ 2) ∂ρ) ≤ L

def axialTilt (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity (fun a => ENNReal.ofReal (Real.exp (2 * a ^ 2)))

theorem axialTilt_mass {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ univ = ENNReal.ofReal (∫ a, Real.exp (2 * a ^ 2) ∂ρ) := by
  rw [axialTilt, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_axial_tilt h.integrable)]
  exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)

theorem axialTilt_mass_le {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ univ ≤ ENNReal.ofReal L := by
  rw [axialTilt_mass h]
  exact ENNReal.ofReal_le_ofReal (integral_axial_tilt_le h.integrable h.bound)

theorem axialTilt_finite {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    IsFiniteMeasure (axialTilt ρ) :=
  ⟨(axialTilt_mass_le h).trans_lt ENNReal.ofReal_lt_top⟩

/-- Normalization is defined even for the zero measure, using a harmless atom. -/
def normalizeFinite (μ : Measure ℝ) (hμ : μ univ < ∞) : ProbabilityMeasure ℝ :=
  MeasureTheory.FiniteMeasure.normalize (⟨μ, ⟨hμ⟩⟩ : FiniteMeasure ℝ)

def axialProbability (ρ : Measure ℝ) {L : ℝ} (h : AxialMoment ρ L) : ProbabilityMeasure ℝ :=
  normalizeFinite (axialTilt ρ) (axialTilt_finite h).measure_univ_lt_top

def axialTail (ρ : Measure ℝ) (U : ℝ) : Measure ℝ :=
  (axialTilt ρ).restrict {a : ℝ | U < |a|}

theorem axialTail_mass_le {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) :
    axialTail ρ U univ ≤ ENNReal.ofReal (Real.exp (-6 * U ^ 2) * L) := by
  have hs : MeasurableSet {a : ℝ | U < |a|} := measurableSet_lt measurable_const measurable_abs
  rw [axialTail, Measure.restrict_apply_univ, axialTilt, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_axial_tilt h.integrable).integrableOn]
  · exact ENNReal.ofReal_le_ofReal (integral_axial_tilt_tail_le h.integrable h.bound hU)
  · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)

theorem axialTail_finite {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) : IsFiniteMeasure (axialTail ρ U) :=
  ⟨(axialTail_mass_le h hU).trans_lt ENNReal.ofReal_lt_top⟩

def axialTailProbability (ρ : Measure ℝ) {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) : ProbabilityMeasure ℝ :=
  normalizeFinite (axialTail ρ U) (axialTail_finite h hU).measure_univ_lt_top

/-- The common decay coefficient for the two probability sheets in the tail. -/
def tailCoefficient (L u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 * Real.exp (-(3 / 2) * u ^ 2) * L)

end BoltzmannNonuniqueness.SheetMeasures

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PowerDiskMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The positive disk mixture for the truncated transverse power

The hot-gain estimate uses the finite measure with density
`(1 + ‖p‖⁻ᑫ) 1_{‖p‖ < D}`. Its singular part is a positive radius mixture
of centered disks. Values at the origin are irrelevant for this identity.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PowerDiskMixture

def mixingDensity (q a : ℝ) : ℝ := Real.pi * q * a ^ (1 - q)

end BoltzmannNonuniqueness.PowerDiskMixture

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A centered fundamental cube for the periodic spatial variable -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusChart

def interval : Set ℝ := Ioc (-(1 / 2 : ℝ)) (1 / 2)

end BoltzmannNonuniqueness.TorusChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Support and integrability of the weak limits of finite-window truncations -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def l2Restrict (S : Set X) (hS : MeasurableSet S) (g : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp g).indicator hS).toLp (S.indicator g)

theorem L2_integrable_of_support {S : Set X} (hS : MeasurableSet S)
    (hμS : μ S < ∞) (g : Lp ℝ 2 μ)
    (hs : ∀ᵐ x ∂μ, x ∉ S → g x = 0) : Integrable g μ := by
  have : Fact (μ S < ∞) := ⟨hμS⟩
  have hgi : Integrable g (μ.restrict S) :=
    ((Lp.memLp g).restrict S).integrable (by norm_num)
  have hi := (integrable_indicator_iff hS).mpr hgi
  apply hi.congr
  filter_upwards [hs] with x hx
  by_cases hxs : x ∈ S <;> simp [hxs,hx]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The time primitive is weakly continuous on a finite time interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

def timeExchange : ((ℝ × P) × ℝ) ≃ᵐ ((ℝ × P) × ℝ) :=
  MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmoothTestFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A countable smooth compact family determining integrable velocity densities -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

abbrev SupportedTest (n : ℕ) :=
  {f : C(Velocity,ℝ) // ContDiff ℝ (⊤ : ℕ∞) (f : Velocity → ℝ) ∧
    tsupport (f : Velocity → ℝ) ⊆ Metric.closedBall 0 (n+1 : ℝ)}

instance instNonemptySupportedTest (n : ℕ) : Nonempty (SupportedTest n) :=
  ⟨⟨0,contDiff_const,by simp⟩⟩

instance instSecondCountableTopologySupportedTest (n : ℕ) : SecondCountableTopology (SupportedTest n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

def supportedSeq (n m : ℕ) : SupportedTest n :=
  TopologicalSpace.denseSeq (SupportedTest n) m

def supportedFn (n m : ℕ) : C(Velocity,ℝ) := (supportedSeq n m).1

def smoothTest (j : ℕ) : Velocity → ℝ :=
  supportedFn (Nat.unpair j).1 (Nat.unpair j).2

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceAngularCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Two-dimensional angular parameter patches and sphere area -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def angularInterval (d : ℝ) : Set ℝ := Ioo (-d) d
def angularSquare (d : ℝ) : Set (ℝ × ℝ) := angularInterval d ×ˢ angularInterval d

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual two-angle collision law dominates its local parameter patch -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance angularSquare_isFinite (d : ℝ) : IsFiniteMeasure (volume.restrict (angularSquare d)) where
  measure_univ_lt_top := by
    rw [Measure.restrict_apply_univ]
    change (volume : Measure ℝ).prod volume (Ioo (-d) d ×ˢ Ioo (-d) d) < ⊤
    rw [Measure.prod_prod,Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceMinorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform entry into an arbitrarily small neighborhood of the positive beam -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamEntryMass (δ : ℝ) : ℝ := (δ/24)*sphereCapMass (δ/12)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # A bounded comparison variable for two positive characteristic equations -/
noncomputable section
namespace BoltzmannNonuniqueness.TransportPrimitive

def positiveDifference (u v : ℝ) : ℝ := (u-v)/(1+u+v)

def positiveDifferenceDamping (u v a b k l e f : ℝ) : ℝ :=
  (a+b+e+f+(k+l)/2)/(1+u+v)

def positiveDifferenceForcing (u v a b k l e f : ℝ) : ℝ :=
  (a-b+e-f)/(1+u+v)+(l-k)*(u+v+4*u*v)/(2*(1+u+v)^2)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Finite positive measure histories below a renewal supersolution -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.PositiveMeasureHistories

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def historySum (K : Kernel X X) (seed : Measure X) : ℕ → Measure X
  | 0 => 0
  | n+1 => seed+K ∘ₘ historySum K seed n

end BoltzmannNonuniqueness.PositiveMeasureHistories

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_L1TruncationCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably many L² approximations with uniform vanishing L¹ errors -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

def truncationError (m : ℕ) : ℝ := 2 / ((m : ℝ)+1)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure L1TruncationFamily (f : ℕ → X → ℝ) (μ : Measure X) where
  region : ℕ → Set X
  measurable : ∀ m, MeasurableSet (region m)
  finite : ∀ m, μ (region m) < ∞
  value : ℕ → ℕ → Lp ℝ 2 μ
  radius : ℕ → ℝ
  bounded : ∀ m n, ‖value m n‖ ≤ radius m
  support : ∀ m n, ∀ᵐ x ∂μ, x ∉ region m → value m n x = 0
  error : ∀ m n, eLpNorm (f n-(value m n : X → ℝ)) 1 μ ≤ ENNReal.ofReal (truncationError m)
  fn_measurable : ∀ n, AEStronglyMeasurable (f n) μ

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The weak truncation limits form a Cauchy sequence in L¹ -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}

structure L1TruncationLimit (F : L1TruncationFamily f μ) where
  indices : ℕ → ℕ
  increasing : StrictMono indices
  value : ℕ → Lp ℝ 2 μ
  support : ∀ m, ∀ᵐ x ∂μ, x ∉ F.region m → value m x = 0
  weak : ∀ m h, Tendsto (fun n => inner ℝ (F.value m (indices n)) h)
    atTop (𝓝 (inner ℝ (value m) h))

namespace L1TruncationLimit

variable {F : L1TruncationFamily f μ} (L : L1TruncationLimit F)

theorem integrable (m : ℕ) : Integrable (L.value m) μ :=
  L2_integrable_of_support (F.measurable m) (F.finite m) _ (L.support m)

def l1Value (m : ℕ) : Lp ℝ 1 μ := (L.integrable m).toL1 (L.value m)

end L1TruncationLimit

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform absolute-entropy moment from the relative-entropy bound -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

def entropyMomentCoefficient : ℝ :=
  2+3*|1-(3/2:ℝ)*Real.log (2*Real.pi)|

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedEntropyProduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded logarithmic tests recovering nonnegative relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

/-- Outside the bounded logarithmic window use the zero test. At a zero density,
use the negative endpoint, which recovers the Maxwellian contribution. -/
def boundedEntropyTest (n : ℕ) (m u : ℝ) : ℝ :=
  if u = 0 then -(n:ℝ) else if |Real.log (u/m)| ≤ n then Real.log (u/m) else 0

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceFlightLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The exact time-simplex factor for a fixed number of collisions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def simplexTime (n : ℕ) (T : ℝ) : ℝ≥0∞ := ENNReal.ofReal (T^n/(n.factorial : ℝ))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The first two time moments on a collision simplex -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def simplexVolume (n : ℕ) (T : ℝ) : ℝ := T^n/(n.factorial : ℝ)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual free-flight law with a fixed Poisson collision rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightWeight (rate T : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rate : ℝ)*T) * (rate : ℝ)^n)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Jointly measurable flight laws with remaining time as a kernel input -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def realFlightWeight (rate : ℝ≥0) (n : ℕ) (T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rate : ℝ)*T)*(rate : ℝ)^n)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceBranchingHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cutting the first-event formula at an intermediate time -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def clockDensity (rate : ℝ≥0) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The scalar exponential factor in the reference branching equation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def growthWeight (c t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c*t))
def growthDensity (c T s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (c*Real.exp (c*(T-s)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponentially growing reference flight is dominated by actual positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def referenceClock : ℝ≥0 := ⟨48*Real.pi,by positivity⟩
def referenceGrowth : ℝ := 11*Real.pi/6

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceHistoryMoments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite time-and-angle parameter measures for the selected positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev EventParameter := ℝ × Sphere

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceGrowthBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform positive displacement block at every sufficiently large duration -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def blockFirstTime (A κ : ℝ) : ℝ≥0 := Real.toNNReal ((1-κ)*A-1)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PerturbedFiniteBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite positive-history weights remain close under beam perturbations -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def wordWeightError (M : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n+1 => M^n+M*wordWeightError M n

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ProductionDualLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded linear tests for the extended entropy production -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

def productionDual (a b s : ℝ) : ℝ :=
  entropyDual b a s+entropyDual a b (-s)

def rawProductionTest (n : ℕ) (a b : ℝ) : ℝ :=
  if a = 0 then -(n:ℝ) else if b = 0 then n else
    if |Real.log (a/b)| ≤ n then Real.log (a/b) else 0

def boundedProductionTest (n : ℕ) (a b : ℝ) : ℝ :=
  if 0 ≤ productionDual a b (rawProductionTest n a b) then rawProductionTest n a b else 0

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LogRenormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic renormalization and its positive derivative -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.Renormalization

theorem logOneAdd_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun x : ℝ => Real.log (1+x)) (1/(1+z)) z := by
  convert ((hasDerivAt_id z).const_add 1).log (show (1+z:ℝ) ≠ 0 by positivity) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

theorem logOneAdd_derivWithin {z : ℝ} (hz : 0 ≤ z) :
    derivWithin (fun x : ℝ => Real.log (1+x)) (Ici 0) z = 1/(1+z) :=
  (logOneAdd_hasDerivAt hz).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici (0:ℝ) z hz)

def logarithm : Renormalization where
  toFun := fun x => Real.log (1+x)
  regular := (contDiffOn_const.add contDiffOn_id).log (fun x hx => by have : 0 ≤ x := hx; positivity)
  at_zero := by simp
  derivative_bound := ⟨1,zero_le_one,fun z hz => by
    have hz' : 0 ≤ z := hz
    rw [logOneAdd_derivWithin hz,abs_of_nonneg (by positivity)]⟩

end BoltzmannNonuniqueness.Renormalization

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedCollisionHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Lower transfer at the same enlarged reference and physical damping -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedHistoryPerturbationError (Cmax : ℝ≥0) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  wordWeightError (ENNReal.ofReal (Cmax:ℝ)) n *
    ENNReal.ofReal (4*Real.pi*((2*(n:ℝ)+8)*ε))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The Fourier multiplier of the exponentially damped characteristic integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def dampedCharacter (β s : ℝ) : ℂ :=
  (Real.exp (-s) : ℂ)*Complex.exp (-Complex.I*(β*s))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform smallness of the finite-history perturbation error -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedFiniteHistoryError (Cmax : ℝ≥0) (N : ℕ) (T ε : ℝ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LinearCharacteristicBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive linear characteristic solution with locally integrable data -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

def linearSolution (a : ℝ) (k g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(∫ s in 0..t, k s))*(a+
    ∫ s in 0..t, Real.exp (∫ r in 0..s, k r)*g s)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite time measure equivalent to Lebesgue measure on every time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def windowInverseWeight (T t : ℝ) : ℝ := (Icc 0 T).indicator (fun t => Real.exp (t^2)) t

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ZeroProfileParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A polynomial zero-seed supersolution uniform in the smallest jet scale -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.ZeroProfile

def profile (D : ℝ) (m : ℕ) (t : ℝ) : ℝ := D*t^(m+1)

def source (M C B δ : ℝ) (m : ℕ) (t y : ℝ) : ℝ := M/(t+δ)*y+C*y^2+B*t^m

end BoltzmannNonuniqueness.ZeroProfile

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdMildRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The polynomial optical depth used in the cold-core survival estimate -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def coldOpticalDepth (B A δ D : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  B*t+A*(t^2/2+δ*t)+D*t^(m+1)/(m+1)

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform optical-depth errors on bounded dilation windows -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

/-- `S` bounds the rescaled jet size, and `U` bounds rescaled time. -/
def coldDilationError (C A D S U : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  C*S^9*U*r^10+A*(U^2/2+U)*r^2+D*U^(m+1)*r^(m+1)/(m+1)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicInitialEntropyLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform relative entropy of the actual initial truncations -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def initialEntropyCoefficient : ℝ := 1+|1-(3/2:ℝ)*Real.log (2*Real.pi)|

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CumulativeIntervalBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite source measure and its weak time primitive -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def cumulative (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Iic t)

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TruncatedExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded exponential weights on a time slab -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def slabExponential (a b C : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun t => Real.exp (C*t))

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RationalUniformApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded rational renormalizations increasing to the identity -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.Renormalization

def rationalFunction (k z : ℝ) : ℝ := k*z/(k+z)

theorem rationalFunction_hasDerivAt {k z : ℝ} (hk : 0 < k) (hz : 0 ≤ z) :
    HasDerivAt (rationalFunction k) (k^2/(k+z)^2) z := by
  have hd := ((hasDerivAt_id z).const_mul k).div
    ((hasDerivAt_id z).const_add k) (show k+z ≠ 0 by positivity)
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [id_eq]
    congr 1
    ring

theorem rationalFunction_derivWithin {k z : ℝ} (hk : 0 < k) (hz : 0 ≤ z) :
    derivWithin (rationalFunction k) (Ici 0) z = k^2/(k+z)^2 :=
  (rationalFunction_hasDerivAt hk hz).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Ici (0:ℝ) z hz)

def rational (k : ℝ) (hk : 1 ≤ k) : Renormalization where
  toFun := rationalFunction k
  regular := (contDiffOn_const.mul contDiffOn_id).div
    (contDiffOn_const.add contDiffOn_id) (fun z hz => by have : 0 ≤ z := hz; positivity)
  at_zero := by simp [rationalFunction]
  derivative_bound := by
    have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
    refine ⟨k,hk0.le,fun z hz => ?_⟩
    have hz0 : 0 ≤ z := hz
    rw [rationalFunction_derivWithin hk0 hz,abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < k+z)) (by linarith : 0 < 1+z)).mpr
    have ha : 0 ≤ k*(k-1) := mul_nonneg hk0.le (sub_nonneg.mpr hk)
    have hb : 0 ≤ k*z := mul_nonneg hk0.le hz
    nlinarith [sq_nonneg z]

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Uniform entropy-controlled approximation by rational renormalizations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def maxwellianLower (R : ℝ) : ℝ :=
  (2*Real.pi)^(-(3/2:ℝ))*Real.exp (-R^2/2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongCompactPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong convergence of physical survival kernels with two time endpoints -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

def timeDifference (u : ℝ × P → ℝ) (z : (ℝ × P) × ℝ) : ℝ := u z.1-u (z.2,z.1.2)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakConservedMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak positive source integrals with strongly convergent survival kernels -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def survivalVolterra (μ : Measure ℝ) (a : (ℝ × P) × ℝ → ℝ)
    (f : ℝ × P → ℝ) (z : ℝ × P) : ℝ :=
  ∫ s, if s ≤ z.1 then a (z,s)*f (s,z.2) else 0 ∂μ

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmallFirstGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform small-input bound for small transverse incoming velocities -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.SmallInputGeometry

def threshold (r R : ℝ) : ℝ := r ^ 2 / (8 * R)

end BoltzmannNonuniqueness.SmallInputGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FanNullSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nullity of a set whose lines through one point have null sections -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
namespace BoltzmannNonuniqueness.Published

abbrev FanRemainder := Fin 19 → ℝ
abbrev FanPhase := ℝ × FanRemainder

def fan (a : FanPhase) (y : FanRemainder) (t : ℝ) : FanPhase :=
  (a.1+t,a.2+t • y)

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveRestrictedChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Propagation of a small deleted kernel through finitely many gains -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def deletionCoefficient (B P : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n+1 => B*P^n+P*deletionCoefficient B P n

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMeshStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded sources give bounded L2 velocity averages -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem integrable_bounded_memLp_two {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) : MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (hf.norm.const_mul B).mono' (hf.aestronglyMeasurable.norm.pow 2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FirstEntryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform positive first-collision weight into the beam neighborhood -/

noncomputable section

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def firstEntryMass (R δ c : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (3*Real.pi*c)*ENNReal.ofReal (sphereCapMass (δ/(R+2)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SeparatedMeasureTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact approximation by bounded separated spacetime–velocity tests -/

noncomputable section

open Set
open scoped BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def atom (p : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) : C(X × Y,ℝ) :=
  ⟨fun z => p.1 z.1*p.2 z.2,(p.1.continuous.comp continuous_fst).mul
    (p.2.continuous.comp continuous_snd)⟩

def eval : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) → C(X × Y,ℝ)
  | [] => 0
  | p::ps => atom p+eval ps

theorem eval_append (ps qs : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    eval (ps++qs) = eval ps+eval qs := by
  induction ps with
  | nil => simp [eval]
  | cons p ps ih => simp [eval,ih,add_assoc]

def product (ps qs : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) :=
  ps.flatMap (fun p => qs.map (fun q => (p.1*q.1,p.2*q.2)))

theorem eval_product (ps qs : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    eval (product ps qs) = eval ps*eval qs := by
  have hrow (p : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
      eval (qs.map (fun q => (p.1*q.1,p.2*q.2))) = atom p*eval qs := by
    induction qs with
    | nil => simp [eval]
    | cons q qs ih =>
      simp only [List.map_cons,eval,ih,mul_add]
      congr 1
      ext z
      change (p.1 z.1*q.1 z.1)*(p.2 z.2*q.2 z.2) =
        (p.1 z.1*p.2 z.2)*(q.1 z.1*q.2 z.2)
      ring
  induction ps with
  | nil => simp [product,eval]
  | cons p ps ih =>
    change eval ((qs.map (fun q => (p.1*q.1,p.2*q.2)))++product ps qs) = _
    rw [eval_append,hrow,ih,eval,add_mul]

def algebra : Subalgebra ℝ C(X × Y,ℝ) where
  carrier := {f | ∃ ps, eval ps = f}
  zero_mem' := ⟨[],rfl⟩
  one_mem' := ⟨[(1,1)],by ext z; simp [eval,atom]⟩
  add_mem' := by
    rintro f g ⟨ps,rfl⟩ ⟨qs,rfl⟩
    exact ⟨ps++qs,eval_append ps qs⟩
  mul_mem' := by
    rintro f g ⟨ps,rfl⟩ ⟨qs,rfl⟩
    exact ⟨product ps qs,eval_product ps qs⟩
  algebraMap_mem' := by
    intro r
    refine ⟨[(BoundedContinuousFunction.const X r,1)],?_⟩
    ext z
    simp [eval,atom]

def probe (x : X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => min (dist x y) 1,(continuous_const.dist continuous_id).min continuous_const⟩ 1
    (by
      intro y z
      rw [Real.dist_eq]
      change |min (dist x y) 1-min (dist x z) 1| ≤ 1
      apply abs_le.mpr
      have hy : 0 ≤ min (dist x y) 1 := le_min dist_nonneg zero_le_one
      have hz : 0 ≤ min (dist x z) 1 := le_min dist_nonneg zero_le_one
      have hy1 := min_le_right (dist x y) (1:ℝ)
      have hz1 := min_le_right (dist x z) (1:ℝ)
      constructor <;> linarith)

end BoltzmannNonuniqueness.SeparatedTests

end

end

section

/-! # Globally uniform separated approximation for compactly supported tests -/

noncomputable section

open Set Metric
open scoped BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def cutoff (x : X) (R : ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => max 0 (min 1 (R+1-dist y x)),
      continuous_const.max (continuous_const.min
        (continuous_const.sub (continuous_id.dist continuous_const)))⟩ 1
    (by
      intro y z
      rw [Real.dist_eq]
      change |max 0 (min 1 (R+1-dist y x))-max 0 (min 1 (R+1-dist z x))| ≤ 1
      have hy0 : 0 ≤ max 0 (min 1 (R+1-dist y x)) := le_max_left _ _
      have hz0 : 0 ≤ max 0 (min 1 (R+1-dist z x)) := le_max_left _ _
      have hy1 : max 0 (min 1 (R+1-dist y x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hz1 : max 0 (min 1 (R+1-dist z x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      exact abs_le.mpr ⟨by linarith,by linarith⟩)

end BoltzmannNonuniqueness.SeparatedTests

end

end

section

/-! # Extending separated-test convergence to compactly supported kinetic tests -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def evalBound : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) → ℝ
  | [] => 0
  | p::ps => ‖p.1‖*‖p.2‖+evalBound ps

end BoltzmannNonuniqueness.SeparatedTests

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionParameterShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regrouping collision times and outgoing angles preserves their product law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev ThreeEvents := EventParameter × (EventParameter × EventParameter)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_ContinuationAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Pasting a local solution to a global admissible continuation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def continuedEvolution (T : ℝ) (F G : Evolution) : Evolution :=
  fun t => if t ≤ T then F t else G (t-T)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedOriginDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Fixed products for selected physical collision words -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev CollisionWord : ℕ → Type
  | 0 => PUnit
  | n+1 => EventParameter × CollisionWord n

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end


