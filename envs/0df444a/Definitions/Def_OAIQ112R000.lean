-- Prove2me | Definitions.Def_OAIQ112R000
-- name    : OAIQ112R000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:33:36.483362+00:00
-- url     : https://prove2.me/theorems/da6c561c-397e-485d-b834-a955975f4c7d
-- title:
--   Definitions bundle OAIQ112R000 of the split of OpenAI, A radial continuum phase transition with algebraic decay
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RadialTransition.main`, carved from OpenAI's openai/math development (OpenAI, *A radial continuum phase transition with algebraic decay*, OpenAI Math Release, September 24, 2026, result family 228, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 274 declarations of OpenAI's Lean: 169 definitions, 13 instances and 92 theorems. The definitions and types are `OAI.RadialTransition.ActiveShift`, `OAI.RadialTransition.AdmissibleFamily`, `OAI.RadialTransition.Cell`, `OAI.RadialTransition.CellReach`, `OAI.RadialTransition.ContinuousConfiguration`, `OAI.RadialTransition.CoreFree`, `OAI.RadialTransition.CroppedCell`, `OAI.RadialTransition.GridIndex`, `OAI.RadialTransition.HasBoxReplication`, `OAI.RadialTransition.HasPhaseGroups`, `OAI.RadialTransition.IsPacking`, `OAI.RadialTransition.MacroState`, `OAI.RadialTransition.MeasurableConfiguration`, `OAI.RadialTransition.Parameter`, `OAI.RadialTransition.ParticleState`, `OAI.RadialTransition.Pressure`, `OAI.RadialTransition.SupportsOn`, `OAI.RadialTransition.attractionBranch`, `OAI.RadialTransition.attractionProfile`, `OAI.RadialTransition.badLabels`, `OAI.RadialTransition.bareAlpha`, `OAI.RadialTransition.bareLimit`, `OAI.RadialTransition.blobTetraConstant`, `OAI.RadialTransition.blockEmbed`, `OAI.RadialTransition.boltzmannMeasure`, `OAI.RadialTransition.boltzmannPartition`, `OAI.RadialTransition.boundaryCoord`, `OAI.RadialTransition.boundaryGrid`, `OAI.RadialTransition.boundarySlice`, `OAI.RadialTransition.boxOrigin`, `OAI.RadialTransition.boxPressureConstant`, `OAI.RadialTransition.boxRegion`, `OAI.RadialTransition.bump`, `OAI.RadialTransition.bumpIntegral`, `OAI.RadialTransition.bumpLip`, `OAI.RadialTransition.bumpProfile`, `OAI.RadialTransition.canonicalThermo`, `OAI.RadialTransition.cellClusterWeight`, `OAI.RadialTransition.cellHamiltonian`, `OAI.RadialTransition.cellMajorant` and 129 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `RadialTransition_BadRemoval`, `RadialTransition_BoltzmannMeasure`, `RadialTransition_BoundedCore`, `RadialTransition_BoxEnsembles`, `RadialTransition_CanonicalCosts`, `RadialTransition_CanonicalLimit`, `RadialTransition_CellInteractions`, `RadialTransition_CellMoments`, `RadialTransition_CellStability`, `RadialTransition_ClusterConvolution`, `RadialTransition_ClusterWeights`, `RadialTransition_ConfigurationMaps`, `RadialTransition_CoreConvergence`, `RadialTransition_CoreLocalLower`, `RadialTransition_CoreUpper`, `RadialTransition_CroppedCells`, `RadialTransition_DeletedInteractions`, `RadialTransition_DensityMixtures`, `RadialTransition_FamilyControls`, `RadialTransition_FamilyStep`, `RadialTransition_FinitePartition`, `RadialTransition_FockIntegral`, `RadialTransition_FreeGeometry`, `RadialTransition_GrandPartition`, `RadialTransition_GridPressure`, `RadialTransition_IdealAttraction`, `RadialTransition_IdealLimit`, `RadialTransition_InitialSlopes`, `RadialTransition_InteriorGrid`, `RadialTransition_KacDeletion`, `RadialTransition_KacPressure`, `RadialTransition_LatticeStability`, `RadialTransition_LinearInteractions`, `RadialTransition_MacroLower`, `RadialTransition_MacroRegions`, `RadialTransition_MeasurableFock`, `RadialTransition_MixtureBounds`, `RadialTransition_MultiConvolution`, `RadialTransition_MultisetEnergy`, `RadialTransition_PackingBlob`, `RadialTransition_PackingLimit`, `RadialTransition_PairEnsembles`, `RadialTransition_ParameterPressure`, `RadialTransition_ParticleMeasure`, `RadialTransition_PartitionReplication`, `RadialTransition_PhaseGeometry`, `RadialTransition_PhysicalIteration`, `RadialTransition_PressureContinuity`, `RadialTransition_ProductConfigurations`, `RadialTransition_ProductFock`, `RadialTransition_RadialKernel`, `RadialTransition_RangeBounds`, `RadialTransition_ScaleSequence`, `RadialTransition_ScaledKernels`, `RadialTransition_ShellGeometry`, `RadialTransition_SpatialProducts`, `RadialTransition_SpatialReplication`, `RadialTransition_SupportGeometry`, `RadialTransition_TetraGeometry`, `RadialTransition_ThermodynamicLimit`, `RadialTransition_TruncatedFamily`.
--
--   **Imports.** It imports the published bundle `Def_RadialTransition`.
--
--   **Imported by** (directly, in this split): the statements `OAI.RadialTransition.admissible_pressure_convex_rt2`, `OAI.RadialTransition.corePressure_uniform_bare_rt2`, `OAI.RadialTransition.exists_family_pressure_ball_rt2`, `OAI.RadialTransition.family_controls_rt2`, `OAI.RadialTransition.family_ideal_exists_active_rt2`, `OAI.RadialTransition.family_kac_deletion_rt2`, `OAI.RadialTransition.family_kac_lower_limit_rt2`, `OAI.RadialTransition.family_kac_upper_limit_rt2`, `OAI.RadialTransition.family_kac_variational_grid_rt2`, `OAI.RadialTransition.finiteGrandPressure_family_box_error_rt2`, `OAI.RadialTransition.grandPressure_reversePrefix_tendsto_rt2` and `OAI.RadialTransition.initial_separation_rt2`; the proofs of `OAI.RadialTransition.admissible_pressure_convex_rt2`, `OAI.RadialTransition.corePressure_uniform_bare_rt2`, `OAI.RadialTransition.exists_family_pressure_ball_rt2`, `OAI.RadialTransition.family_controls_rt2`, `OAI.RadialTransition.family_ideal_exists_active_rt2`, `OAI.RadialTransition.family_kac_deletion_rt2`, `OAI.RadialTransition.family_kac_lower_limit_rt2`, `OAI.RadialTransition.family_kac_upper_limit_rt2`, `OAI.RadialTransition.family_kac_variational_grid_rt2`, `OAI.RadialTransition.finiteGrandPressure_family_box_error_rt2`, `OAI.RadialTransition.grandPressure_reversePrefix_tendsto_rt2`, `OAI.RadialTransition.initial_separation_rt2` and `OAI.RadialTransition.main`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_RadialTransition

section
-- module Solutions.OAIQ112_RT.Compat
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
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_IdealAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Pressure := ℝ → ℝ → ℝ

def pressureSupport (Q : Pressure) (β h e d : ℝ) : Prop :=
  ∀ β' h', 0 < β' →
    Q β h + e * (β' - β) + d * (h' - h) ≤ Q β' h'

def attractionBranch (Q : Pressure) (a u : ℝ) : Pressure :=
  fun β h => Q β (h + β * a * u) - β * a / 2 * u ^ 2

def idealAttraction (Q : Pressure) (a : ℝ) : Pressure :=
  fun β h => sSup (Set.range fun u => attractionBranch Q a u β h)

def ActiveShift (Q : Pressure) (a β h u : ℝ) : Prop :=
  ∀ v : ℝ, attractionBranch Q a v β h ≤ attractionBranch Q a u β h

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section InnerSupport

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SupportsOn (F : E → ℝ) (D : Set E) (x v : E) : Prop :=
  ∀ y ∈ D, F x + inner ℝ v (y - x) ≤ F y

def supportSet (F : E → ℝ) (D : Set E) (x : E) : Set E :=
  {v | SupportsOn F D x v}

end InnerSupport

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uIndex uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section Shell

def shellGraph {V : Type uV} (x : V → Position) (l : ℝ) : SimpleGraph V where
  Adj i j := i ≠ j ∧ l ≤ dist (x i) (x j) ∧
    dist (x i) (x j) ≤ (1 + (1 : ℝ) / 1000) * l
  symm := ⟨by intro i j h; exact ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

end Shell

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoundedCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

def microLength (t : ℝ) : ℝ := Real.exp (-t)
def shellStep (t : ℝ) : ℝ := microLength t / 3000

def coreReal (t r : ℝ) : ℝ :=
  t ^ 2 * min
    (1 - clamp01 ((r - microLength t) / shellStep t) +
      clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t))
    (clamp01 (1 + t * (1 - r)))

def corePotential (t : ℝ) : Potential := fun r => coreReal t r

theorem microLength_pos (t : ℝ) : 0 < microLength t := Real.exp_pos _

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def IsPacking (L : ℝ) (X : Finset Position) : Prop :=
  (∀ x ∈ X, x ∈ cube L) ∧ (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)

def packingTranslate {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) (x : Position) : Position :=
  WithLp.toLp 2 (fun k => (j k : ℝ) * (s + 1) + x k)

@[simp] theorem packingTranslate_apply {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n)
    (x : Position) (k : Fin 3) : packingTranslate s j x k = (j k : ℝ) * (s + 1) + x k := rfl

def packingDensity : ℝ :=
  sSup {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3}

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_RadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def rawBumpProfile (r : ℝ) : ℝ := Real.smoothTransition (2 - 2 * r ^ 2)

def rawBump (x : Position) : ℝ := rawBumpProfile ‖x‖

theorem rawBumpProfile_zero {r : ℝ} (hr : 1 ≤ r) : rawBumpProfile r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

theorem contDiff_rawBump : ContDiff ℝ ∞ rawBump := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem compactSupport_rawBump : HasCompactSupport rawBump := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Position) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (rawBumpProfile_zero (le_of_not_ge h))

def bumpIntegral : ℝ := ∫ x : Position, rawBump x

def bumpProfile (r : ℝ) : ℝ := rawBumpProfile r / bumpIntegral

def bump (x : Position) : ℝ := bumpProfile ‖x‖

theorem contDiff_bump : ContDiff ℝ ∞ bump := contDiff_rawBump.div_const _

theorem compactSupport_bump : HasCompactSupport bump := by
  apply compactSupport_rawBump.mono
  intro x hx hr
  apply hx
  change rawBump x / bumpIntegral = 0
  rw [hr, zero_div]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def occupation {V : Type uV} {I : Type uI} [Fintype V] (q : V → I) (i : I) : ℝ := by
  classical
  exact (Fintype.card {a : V // q a = i} : ℝ)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ScaledKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def scaledBumpProfile (R r : ℝ) : ℝ := (R ^ 3)⁻¹ * bumpProfile (r / R)

def scaledBump (R : ℝ) (x : Position) : ℝ := (R ^ 3)⁻¹ * bump (R⁻¹ • x)

def attractionProfile (a R : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' n, a n * scaledBumpProfile (R n) r

def familyPotential (t : ℝ) (a R : ℕ → ℝ) : Potential :=
  fun r => coreReal t r - t * attractionProfile a R r

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_LatticeStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Cell := Fin 3 → ℤ

def cellOf (x : Position) : Cell := fun k => ⌊4 * x k⌋

def cellMargin (R : ℝ) : ℤ := ⌈4 * R⌉ + 1

def CellReach (R : ℝ) (i j : Cell) : Prop := ∀ k, |j k - i k| ≤ cellMargin R

instance instDecidableCellReach (R : ℝ) (i j : Cell) : Decidable (CellReach R i j) := inferInstanceAs (Decidable (∀ _k, _))

def rangeCells (R : ℝ) (i : Cell) : Finset Cell :=
  Fintype.piFinset fun k => Finset.Icc (i k - cellMargin R) (i k + cellMargin R)

def cellMajorant (R W : ℝ) (i j : Cell) : ℝ :=
  if CellReach R i j then (R ^ 3)⁻¹ * W else 0

def familyCellMajorant (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) : ℝ :=
  t * ∑' n, a n * cellMajorant (R n) bumpIntegral⁻¹ i j

def cubeCells (L : ℝ) : Finset Cell :=
  Fintype.piFinset (fun _ => Finset.Icc 0 ⌊4 * L⌋)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def finiteCanonical (φ : Potential) (t L : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  -Real.log (partition φ L N β) / (t * L ^ 3)

def grandPartition (φ : Potential) (t L β h : ℝ) : ℝ :=
  ∑' N : ℕ, Real.exp (t * h * N) * partition φ L N β

def cubeProbability (L : ℝ) : Measure Position :=
  (ENNReal.ofReal (L ^ 3))⁻¹ • volume.restrict (cube L)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CanonicalCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def coreLift (t : ℝ) (x : Position) : ℝ := coreReal t ‖x‖

def coreIntegral (t : ℝ) : ℝ := ∫ x : Position, coreLift t x

def densityAt (L : ℝ) (N : ℕ) : ℝ := (N : ℝ) / L^3

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SpatialProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex uOtherIndex uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def orderedEnergy (φ : Potential) {ι : Type uIndex} [Fintype ι] (x : ι → Position) : ℝ := by
  classical
  exact (∑ i, ∑ j, if i ≠ j then φ (nndist (x i) (x j)) else 0) / 2

def rawPartition (φ : Potential) (A : Set Position) (ι : Type uIndex) [Fintype ι] (β : ℝ) : ℝ :=
  ∫ x : ι → Position, Real.exp (-β * orderedEnergy φ x) ∂Measure.pi (fun _ : ι => volume.restrict A)

def partitionOn (φ : Potential) (A : Set Position) (N : ℕ) (β : ℝ) : ℝ :=
  (N.factorial : ℝ)⁻¹ * rawPartition φ A (Fin N) β

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PartitionReplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex uI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def translateSet (a : Position) (A : Set Position) : Set Position :=
  (fun x => x - a) ⁻¹' A

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_GrandPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def grandOn (φ : Potential) (A : Set Position) (β z : ℝ) : ℝ :=
  ∑' N : ℕ, Real.exp (z * N) * partitionOn φ A N β

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SpatialReplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def boxOrigin {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) : Position :=
  WithLp.toLp 2 (fun k => (j k : ℝ) * (s + 2))

def boxRegion {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) : Set Position :=
  translateSet (boxOrigin s j) (cube s)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ThermodynamicLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def thermodynamicFilter (d : ℝ) : Filter (ℝ × ℕ) :=
  Filter.comap Prod.fst atTop ⊓
    Filter.comap (fun z : ℝ × ℕ => (z.2 : ℝ) / z.1 ^ 3) (nhds d)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CanonicalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

instance instIsCountablyGeneratedProdRealNatThermodynamicFilter (d : ℝ) : IsCountablyGenerated (thermodynamicFilter d) := by
  unfold thermodynamicFilter
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def HasBoxReplication (H : ℝ → ℕ → ℝ) : Prop :=
  ∀ (s L : ℝ) (b : ℕ), 0 < s → 0 < L → (b : ℝ) * (s + 2) ≤ L →
    ∀ m : Fin (b ^ 3) → ℕ,
      H L (∑ j, m j) ≤ s ^ 3 / L ^ 3 * ∑ j, H s (m j)

def canonicalThermo (φ : Potential) (t β d : ℝ) : ℝ :=
  liminf (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β) (thermodynamicFilter d)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_DensityMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def finiteGrandPressure (φ : Potential) (t L β h : ℝ) : ℝ :=
  Real.log (grandPartition φ t L β h) / (t * L ^ 3)

def grandPressure (φ : Potential) (t : ℝ) : Pressure :=
  fun β h => limsup (fun L : ℝ => finiteGrandPressure φ t L β h) atTop

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ParticleMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev ParticleState (X : Type uX) := Σ n : ℕ, Fin n → X

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]
instance instMeasurableSpaceParticleState : MeasurableSpace (ParticleState X) := borel (ParticleState X)
instance instBorelSpaceParticleState : BorelSpace (ParticleState X) := ⟨rfl⟩

def particleCount (x : ParticleState X) : ℕ := x.1

def particleBase (ν : Measure X) (z : ℝ) : Measure (ParticleState X) :=
  Measure.sum (fun n : ℕ => ENNReal.ofReal (Real.exp (z*n) / n.factorial) •
    Measure.map (Sigma.mk n) (Measure.pi (fun _ : Fin n => ν)))

def particleVacuum : ParticleState X := ⟨0, Fin.elim0⟩

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoltzmannMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def boltzmannPartition {X : Type uX} [MeasurableSpace X] (μ : Measure X) (E : X → ℝ) : ℝ :=
  ∫ x, Real.exp (-E x) ∂μ

def boltzmannMeasure {X : Type uX} [MeasurableSpace X] (μ : Measure X) (E : X → ℝ) : Measure X :=
  (ENNReal.ofReal (boltzmannPartition μ E))⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x)))

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uI

noncomputable section


open MeasureTheory Filter Set

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

section ProductCells
variable {I : Type uI} [Fintype I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

def cellN (i : I) (x : ∀ j, ParticleState (X j)) : ℝ := particleCount (x i)

end ProductCells
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellInteractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX uY uZ

noncomputable section


open MeasureTheory Filter Set

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

section AbstractCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

def cellHamiltonian (U : ∀ i, X i → ℝ) (W : ∀ i j, X i → X j → ℝ)
    (x : ∀ i, X i) : ℝ :=
  ∑ i, U i (x i) + (1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else W i j (x i) (x j)

end AbstractCells

section PairCells
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}

def pairWithin (v : X → X → ℝ) (s : ParticleState X) : ℝ := by
  classical
  exact (1/2:ℝ) * ∑ i : Fin s.1, ∑ j : Fin s.1, if i = j then 0 else v (s.2 i) (s.2 j)

def pairBetween (v : X → Y → ℝ) (s : ParticleState X) (t : ParticleState Y) : ℝ :=
  ∑ i : Fin s.1, ∑ j : Fin t.1, v (s.2 i) (t.2 j)

@[simp] theorem pairWithin_vacuum (v : X → X → ℝ) : pairWithin v particleVacuum = 0 := by
  change (1/2:ℝ) * (∑ i : Fin 0, ∑ j : Fin 0, if i = j then 0 else v (Fin.elim0 i) (Fin.elim0 j)) = 0
  rw [Fin.sum_univ_zero, mul_zero]

@[simp] theorem pairBetween_vacuum (v : X → Y → ℝ) (t : ParticleState Y) :
    pairBetween v particleVacuum t = 0 := by
  change (∑ i : Fin 0, ∑ j : Fin t.1, v (Fin.elim0 i) (t.2 j)) = 0
  rw [Fin.sum_univ_zero]

end PairCells

section PhysicalCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

def pairCellEnergy (v : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) : ℝ :=
  cellHamiltonian (fun i => pairWithin (v i i)) (fun i j => pairBetween (v i j)) x

end PhysicalCells
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FockIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def fockCoeff (z : ℝ) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (z*n)/n.factorial)

section FockAdd
variable {X : Type uX} [MeasurableSpace X]
variable (F : ∀ (ι : Type) [Fintype ι], (ι → X) → ℝ≥0∞)
variable (heq : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X),
  F ι (x ∘ e) = F κ x)

def fockIntegral (μ : Measure X) (z : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, fockCoeff z n * ∫⁻ x : Fin n → X, F _ x ∂Measure.pi (fun _ => μ)

end FockAdd
section MultisetFock
variable {X : Type uX}

def configurationMultiset {ι : Type} [Fintype ι] (x : ι → X) : Multiset X := ∑ i, {x i}

def particleMultiset (x : ParticleState X) : Multiset X := configurationMultiset x.2

variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (F : Multiset X → ℝ≥0∞)

def ContinuousConfiguration : Prop :=
  ∀ (s : Multiset X) (ι : Type) [Fintype ι], Continuous (fun x : ι → X => F (s+configurationMultiset x))

end MultisetFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ProductConfigurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section ProductConfigurations
variable {I : Type} [Fintype I] (X : I → Type uX) [∀ i, TopologicalSpace (X i)]

def configurationsEquiv : (Σ n : I → ℕ, ∀ i, Fin (n i) → X i) ≃ (∀ i, ParticleState (X i)) where
  toFun s i := ⟨s.1 i, s.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv s := by cases s; rfl
  right_inv x := rfl

def configurationsHomeomorph : (Σ n : I → ℕ, ∀ i, Fin (n i) → X i) ≃ₜ (∀ i, ParticleState (X i)) :=
  (configurationsEquiv X).toHomeomorphOfContinuousOpen
    (continuous_sigma (fun _n => continuous_pi (fun i => continuous_sigmaMk.comp (continuous_apply i))))
    (isOpenMap_sigma.mpr (fun n => (Topology.IsOpenEmbedding.piMap
      (fun i => (Topology.IsOpenEmbedding.sigmaMk (i := n i) :
        Topology.IsOpenEmbedding (@Sigma.mk ℕ (fun k => Fin k → X i) (n i))))).isOpenMap))

end ProductConfigurations
section MultiObservable
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X]

def multiParticleMultiset (x : I → ParticleState X) : Multiset X := ∑ i, particleMultiset (x i)

end MultiObservable
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ConfigurationMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MapConfigurations
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

def mapParticle (f : X → Y) (x : ParticleState X) : ParticleState Y := ⟨x.1, f ∘ x.2⟩

end MapConfigurations
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ProductFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section GeneralFock
variable {I : Type} [Fintype I] {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

variable (Y : I → Type uY) [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
  [∀ i, BorelSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]

def mappedMultiParticleMultiset (pos : ∀ i, Y i → X) (x : ∀ i, ParticleState (Y i)) : Multiset X :=
  ∑ i, particleMultiset (mapParticle (pos i) (x i))

end GeneralFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MultisetEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uM uIndex uY

noncomputable section


open MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section MultisetEnergy
variable {X : Type uX}

def multisetPairing (v : X → X → ℝ) (s t : Multiset X) : ℝ :=
  (s.map (fun x => (t.map (v x)).sum)).sum

def multisetDiagonal (v : X → X → ℝ) (s : Multiset X) : ℝ :=
  (s.map (fun x => v x x)).sum

def multisetEnergy (v : X → X → ℝ) (s : Multiset X) : ℝ :=
  (1/2:ℝ) * (multisetPairing v s s - multisetDiagonal v s)

@[simp] lemma multisetPairing_zero_left (v : X → X → ℝ) (s : Multiset X) :
    multisetPairing v 0 s = 0 := by simp [multisetPairing]
@[simp] lemma multisetPairing_zero_right (v : X → X → ℝ) (s : Multiset X) :
    multisetPairing v s 0 = 0 := by simp [multisetPairing]
@[simp] lemma multisetPairing_add_left (v : X → X → ℝ) (s t u : Multiset X) :
    multisetPairing v (s+t) u = multisetPairing v s u + multisetPairing v t u := by
  simp [multisetPairing]
@[simp] lemma multisetPairing_add_right (v : X → X → ℝ) (s t u : Multiset X) :
    multisetPairing v s (t+u) = multisetPairing v s t + multisetPairing v s u := by
  simp [multisetPairing, Multiset.sum_map_add]
@[simp] lemma multisetDiagonal_add (v : X → X → ℝ) (s t : Multiset X) :
    multisetDiagonal v (s+t) = multisetDiagonal v s + multisetDiagonal v t := by
  simp [multisetDiagonal]
@[simp] lemma multisetDiagonal_zero (v : X → X → ℝ) : multisetDiagonal v 0 = 0 := by simp [multisetDiagonal]

end MultisetEnergy

def radialPair (φ : Potential) (x y : Position) : ℝ := φ (nndist x y)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CroppedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open MeasureTheory Set Filter Function

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def gridRegion (k : Cell) : Set Position := {x | cellOf x = k}

abbrev CroppedCell (A : Set Position) (k : Cell) := {x : Position // x ∈ A ∩ gridRegion k}

def croppedCellMeasure (A : Set Position) (k : Cell) : Measure (CroppedCell A k) :=
  volume.comap Subtype.val

def gridOrigin (k : Cell) : Position := WithLp.toLp 2 (fun i => (k i : ℝ)/4)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PressureContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def localMomentBound (t β z : ℝ) : ℝ :=
  Real.exp (16/15*(1/64)*Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4)

def familyPressureLipschitz (t β h : ℝ) : ℝ :=
  216*(β/2*localMomentBound t β (t*h))*2197*bumpIntegral⁻¹

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MeasurableFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uIndex uY uZ

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MeasurableFock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

variable (F : Multiset X → ℝ≥0∞)
def MeasurableConfiguration : Prop :=
  ∀ (s : Multiset X) (ι : Type) [Fintype ι], Measurable (fun x : ι → X => F (s+configurationMultiset x))

end MeasurableFock
end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PairEnsembles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section GeneralGrand
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

def pairGrand (v : X → X → ℝ) (μ : Measure X) (β z : ℝ) : ℝ :=
  ∫ x, Real.exp (-β * multisetEnergy v (particleMultiset x)) ∂particleBase μ z

end GeneralGrand

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_DeletedInteractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def deletedPair {G : Type uG} [DecidableEq G] (g : Cell → G) (φ χ : Potential)
    (x y : Position) : ℝ :=
  (if g (cellOf x) = g (cellOf y) then radialPair φ x y else 0) + radialPair χ x y

def deletionMajorant {G : Type uG} [DecidableEq G] (g : Cell → G) (W : Cell → Cell → ℝ)
    (i j : Cell) : ℝ := if g i = g j then 0 else W i j

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoxEnsembles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open MeasureTheory Set Filter Function

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def halfCube (L : ℝ) : Set Position := {x | ∀ k, 0 ≤ x k ∧ x k < L}

abbrev GridIndex (q : ℕ) := Fin 3 → Fin q

def gridEmbed {q : ℕ} (i : GridIndex q) : Cell := fun k => (i k : ℤ)

def macroOf (q : ℕ) (k : Cell) : Cell := fun d => k d / (q:ℤ)

def blockEmbed {m q : ℕ} (i : GridIndex m) (j : GridIndex q) : GridIndex (m*q) :=
  fun d => ⟨(i d : ℕ)*q+(j d : ℕ), by
    calc
      _ < (i d : ℕ)*q+q := Nat.add_lt_add_left (j d).isLt _
      _ = ((i d : ℕ)+1)*q := by ring
      _ ≤ m*q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt (i d).isLt)⟩

def boundaryCoord (q D : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun a => (a:ℕ) < D ∨ q-D ≤ (a:ℕ))

def boundarySlice (q D : ℕ) (d : Fin 3) : Finset (GridIndex q) :=
  Fintype.piFinset (fun k => if k = d then boundaryCoord q D else Finset.univ)

def boundaryGrid (q D : ℕ) : Finset (GridIndex q) :=
  Finset.univ.biUnion (boundarySlice q D)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MacroRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def macroRegion (q : ℕ) (k : Cell) : Set Position := {x | macroOf q (cellOf x) = k}

def macroOrigin (q : ℕ) (k : Cell) : Position := WithLp.toLp 2 (fun d => (q:ℝ)*(k d:ℝ)/4)

def regionMeasure (A : Set Position) : Measure A := volume.comap Subtype.val

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_RangeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def referenceMajorant (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) : ℝ :=
  cellMajorant 2 (8*t^2) i j + familyCellMajorant t a R i j

def referenceRowBound (t A : ℝ) : ℝ := 2197*8*t^2+2197*t*bumpIntegral⁻¹*A

def boxPressureConstant (t β h A : ℝ) : ℝ :=
  288*β*localMomentBound t β (t*h)*referenceRowBound t A/t

def bumpLip : ℝ≥0 := Classical.choose
  (ContDiff.lipschitzWith_of_hasCompactSupport compactSupport_bump contDiff_bump (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

def macroKernel (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  scaledBump R (macroOrigin q i-macroOrigin q j)

def macroKernelError (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  if CellReach (R/q+1) i j then (bumpLip:ℝ)/R^4*q else 0

def macroKernelUpper (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  macroKernel q R i j+macroKernelError q R i j

def macroKernelLower (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  max 0 (macroKernel q R i j-macroKernelError q R i j)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_InteriorGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition

def kernelRowError (q : ℕ) (R : ℝ) : ℝ :=
  (10000*(bumpLip:ℝ)+bumpIntegral⁻¹)*(q:ℝ)/R

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MacroLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def kernelInterior (m q : ℕ) (R : ℝ) : Finset (GridIndex m) :=
  Finset.univ \ boundaryGrid m (cellMargin (R/q+1)).toNat

abbrev MacroState (m q : ℕ) := ∀ i : GridIndex m, ParticleState (macroRegion q (gridEmbed i))

def macroKacEnergy (φ : Potential) (m q : ℕ) (R lam : ℝ) (x : MacroState m q) : ℝ :=
  (∑ i, pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i)) -
    lam*pairCellEnergy (fun i j (y : macroRegion q (gridEmbed i)) (z : macroRegion q (gridEmbed j)) => scaledBump R ((y:Position)-(z:Position))) x

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MixtureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def quadraticTerm (φ : Potential) (L β z b : ℝ) (n : ℕ) : ℝ :=
  Real.exp (z*n) * partition φ L n β * Real.exp (b*(n:ℝ)^2/L^3)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_GridPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def macroMeasure (m q : ℕ) (z : ℝ) : Measure (MacroState m q) :=
  Measure.pi (fun i : GridIndex m => particleBase (regionMeasure (macroRegion q (gridEmbed i))) z)

def macroProduct (φ : Potential) (m q : ℕ) (β : ℝ) (F : ℕ → ℝ) (x : MacroState m q) : ℝ :=
  ∏ i : GridIndex m, (F (particleCount (x i))*
    Real.exp (-β*pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i)))

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_LinearInteractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX uY uZ

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def singleAttraction (R lam : ℝ) : Potential := fun r => -lam*scaledBumpProfile R r

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ClusterConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def clusterConvolution {X : Type uX} (F G : Multiset X → ℝ≥0∞) (s : Multiset X) : ℝ≥0∞ :=
  (s.antidiagonal.map (fun p => F p.1 * G p.2)).sum

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ClusterWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uM uY uZ

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def nearCube (r : ℝ) (x : Position) : Set Position :=
  {y | ∀ k, |y k-x k| ≤ r}

def nearMask (r : ℝ) (x y : Position) : ℝ≥0∞ := (nearCube r x).indicator (fun _ => 1) y

def regionMask (A : Set Position) (x : Position) : ℝ≥0∞ := A.indicator (fun _ => 1) x

def starWeight (A : Set Position) (r : ℝ) (s : Multiset Position) : ℝ≥0∞ :=
  (s.map (fun x => regionMask A x * (s.map (nearMask r x)).prod)).sum

def emptyWeight {X : Type uX} (s : Multiset X) : ℝ≥0∞ := if s.card = 0 then 1 else 0

def cellClusterWeight (t α r : ℝ) (k : Cell) (s : Multiset Position) : ℝ≥0∞ :=
  emptyWeight s + if s.card ≤ 4 then ENNReal.ofReal (Real.exp (-t*α))*starWeight (gridRegion k) r s else 0

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MultiConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

section Multi
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def finClusterProduct : (n : ℕ) → (Fin n → Multiset X → ℝ≥0∞) → Multiset X → ℝ≥0∞
  | 0, _ => emptyWeight
  | n+1, W => clusterConvolution (W 0) (finClusterProduct n (fun i => W i.succ))

variable {I : Type} [Fintype I]

def indexedClusterProduct (W : I → Multiset X → ℝ≥0∞) : Multiset X → ℝ≥0∞ :=
  finClusterProduct (Fintype.card I) (fun i => W ((Fintype.equivFin I).symm i))

end Multi
end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def CoreFree {ι : Type uIndex} (t : ℝ) (x : ι → Position) : Prop :=
  ∀ i j, i ≠ j → dist (x i) (x j) < 1 →
    microLength t ≤ dist (x i) (x j) ∧
      dist (x i) (x j) ≤ (1+(1:ℝ)/1000)*microLength t

lemma CoreFree.dist_bound {ι : Type uIndex} {t : ℝ} {x : ι → Position} (hx : CoreFree t x)
    (i j : ι) (hij : dist (x i) (x j) < 1) :
    dist (x i) (x j) ≤ (1+(1:ℝ)/1000)*microLength t := by
  by_cases he : i = j
  · subst j; simp only [dist_self]; exact mul_nonneg (by norm_num) (microLength_pos t).le
  · exact (hx i j he hij).2

def coreFreeSetoid {ι : Type uIndex} {t : ℝ} {x : ι → Position} (hx : CoreFree t x)
    (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1) : Setoid ι where
  r i j := dist (x i) (x j) < 1
  iseqv := ⟨fun _ => by simp, fun h => by simpa only [dist_comm] using h, by
    intro i j k hij hjk
    have h1 := hx.dist_bound i j hij
    have h2 := hx.dist_bound j k hjk
    linarith [dist_triangle (x i) (x j) (x k)]⟩

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BadRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def badLabels {ι : Type uIndex} [Fintype ι] (t : ℝ) (x : ι → Position) : Finset ι :=
  Finset.univ.filter (fun i => ∃ j, i ≠ j ∧ dist (x i) (x j) < 1 ∧
    ¬ (microLength t ≤ dist (x i) (x j) ∧ dist (x i) (x j) ≤ (1+(1:ℝ)/1000)*microLength t))

def removalWeight (t β : ℝ) (s : Multiset Position) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β*t^2*s.card/2))

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CoreUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def freeCoverWeight (L t α : ℝ) : Multiset Position → ℝ≥0∞ :=
  indexedClusterProduct (fun k : cubeCells L =>
    cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_TetraGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def tetraEdge (t : ℝ) : ℝ := microLength t + microLength t/2000

def tetraVertex (t : ℝ) (i : Fin 4) : Position :=
  WithLp.toLp 2 (fun k : Fin 3 => if i.val=0 ∨ i.val=k.val+1 then 0 else tetraEdge t*Real.sqrt 2/2)

def tetraEpsilon (t : ℝ) : ℝ := microLength t/100000

def tetraRegion (t a : ℝ) : Set (Fin 4 → Position) :=
  {x | x 0 ∈ cube a ∧ ∀ j : Fin 3, x j.succ - x 0 - tetraVertex t j.succ ∈ cube (tetraEpsilon t)}

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PackingBlob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def packingBlob (ν b : ℝ) (z : Position) : Set Position := translateSet ((1+ν) • z) (cube b)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CoreLocalLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def blobTetraConstant (b : ℝ) : ℝ := (b/2)^3/((100000:ℝ)^9*24)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CoreConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def bareAlpha (h : ℝ) : ℝ := max 0 (max h (4*h-9))
def bareLimit (h : ℝ) : ℝ := max 0 (max (packingDensity*h) (packingDensity*(4*h-9)))

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FamilyStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uAlpha

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def prepend {α : Type uAlpha} (v : α) (f : ℕ → α) : ℕ → α := fun n => Nat.casesOn n v f

@[simp] lemma prepend_zero {α : Type uAlpha} (v : α) (f : ℕ → α) : prepend v f 0 = v := rfl
@[simp] lemma prepend_succ {α : Type uAlpha} (v : α) (f : ℕ → α) (n : ℕ) : prepend v f (n+1) = f n := rfl

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KacDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def deletedKacPressure (φ : Potential) (m q : ℕ) (R t a β h : ℝ) : ℝ :=
  Real.log (boltzmannPartition (macroMeasure m q (t*h)) (fun x => β*macroKacEnergy φ m q R (t*a) x))/(t*((m:ℝ)*q/4)^3)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KacPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def kernelUpperError (q : ℕ) (R : ℝ) : ℝ := 10000*(bumpLip:ℝ)*q/R

def kacSeries (φ : Potential) (q : ℕ) (R t a β h : ℝ) : ℕ → ℝ :=
  quadraticTerm φ ((q:ℝ)/4) β (t*h) (β*(t*a)*(1+kernelUpperError q R)/2)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ParameterPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

abbrev Parameter := EuclideanSpace ℝ (Fin 2)
def parameter (β h : ℝ) : Parameter := WithLp.toLp 2 ![β,h]
def positiveParameters : Set Parameter := {x | 0 < x 0}
def onParameters (Q : Pressure) (x : Parameter) : ℝ := Q (x 0) (x 1)

@[simp] lemma parameter_zero (β h : ℝ) : parameter β h 0 = β := rfl
@[simp] lemma parameter_one (β h : ℝ) : parameter β h 1 = h := rfl
@[simp] lemma parameter_eta (x : Parameter) : parameter (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_IdealLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def finiteMax {ι : Type uIndex} [Fintype ι] (f : ι → ℝ) : ℝ := sSup (range f)

def phaseMass : ℝ := 3/(2*packingDensity)
def phaseDensity : Fin 3 → ℝ := ![0,packingDensity,4*packingDensity]
def phaseOffset : Fin 3 → ℝ := ![0,0,-9*packingDensity]
def limitingPlane (i : Fin 3) (β h : ℝ) : ℝ :=
  phaseDensity i*h+phaseOffset i+β*phaseMass/2*(phaseDensity i)^2
def threePlane (β h : ℝ) : ℝ := finiteMax (fun i => limitingPlane i β h)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_InitialSlopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def phaseSlope (i : Fin 3) : Parameter := parameter (phaseMass/2*(phaseDensity i)^2) (phaseDensity i)
def phaseCenter : Parameter := parameter 1 (-3/4)
def targetSlope : Parameter := parameter (17*packingDensity/4) (5*packingDensity/3)
def phaseWindow (r : ℝ) : Set Parameter := Metric.closedBall phaseCenter r

def HasPhaseGroups (Q : Pressure) (x : Parameter) (r : ℝ) : Prop :=
  supportSet (onParameters Q) positiveParameters x = closure (convexHull ℝ
    {v : Parameter | v ∈ supportSet (onParameters Q) positiveParameters x ∧
      ∃ i : Fin 3, v ∈ Metric.closedBall (phaseSlope i) r})

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FamilyControls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def AdmissibleFamily (_t A : ℝ) (b S : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ b n) ∧ (∀ n, 1 ≤ S n) ∧ Summable b ∧ ∑' n, b n ≤ A

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ScaleSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set Filter
namespace RadialTransition

def doublePower (q : ℝ) (n : ℕ) : ℝ := q^(2^n)

def scaleRange (b : ℝ) (n : ℕ) : ℝ := (doublePower b n)^32

def scaleTail (b : ℝ) (n : ℕ) : ℝ := (doublePower b n)⁻¹^4

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_TruncatedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

def reversePrefix (v : ℝ) (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => v
  | n+1 => prepend (f n) (reversePrefix v f n)
@[simp] lemma reversePrefix_zero (v : ℝ) (f : ℕ → ℝ) : reversePrefix v f 0=(fun _ => v) := rfl
@[simp] lemma reversePrefix_succ (v : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    reversePrefix v f (n+1)=prepend (f n) (reversePrefix v f n) := rfl

def cutMass (f : ℕ → ℝ) (n j : ℕ) : ℝ := if j<n then f j else 0

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PhaseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def phaseRadius : ℝ := packingDensity/128
def pressureRadius : ℝ := packingDensity/32

def directionalMax (z : Parameter) : ℝ := finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z)

def exclusionNormal : Fin 3 → Parameter := ![parameter 1 (-15/4),parameter (-1) 3,parameter 1 (-3/4)]

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PhysicalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

def iterationMass (b : ℝ) : ℕ → ℝ := prepend phaseMass (scaleTail b)
def iterationBudget : ℝ := phaseMass+1

def iterationQ (t b : ℝ) (n : ℕ) : Pressure :=
  grandPressure (familyPotential t (reversePrefix 0 (iterationMass b) (n+1))
    (reversePrefix 1 (scaleRange b) (n+1))) t
def iterationP (t b : ℝ) (n : ℕ) : Pressure :=
  idealAttraction (grandPressure (familyPotential t (reversePrefix 0 (iterationMass b) n)
    (reversePrefix 1 (scaleRange b) n)) t) (iterationMass b n)

end RadialTransition
end

end OAI
end


