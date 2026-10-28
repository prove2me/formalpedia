-- Prove2me | Definitions.Def_OAIB3Bs000
-- name    : OAIB3Bs000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T15:56:13.433147+00:00
-- url     : https://prove2.me/theorems/f7b7994e-400d-4159-b187-38a5a8c5ab9b
-- title:
--   Definitions bundle OAIB3Bs000 of the split of OpenAI, Row–column symmetry and contraction of coordinate sweeps
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.binary_sweep_contraction_and_mixing`, carved from OpenAI's openai/math development (OpenAI, *Row–column symmetry and contraction of coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 647 declarations of OpenAI's Lean: 462 definitions, 2 inductive types or structures, 22 instances and 161 theorems. The definitions and types are `OAI.BinaryCoordinateSweeps.Assigns`, `OAI.BinaryCoordinateSweeps.BinaryMainTarget`, `OAI.BinaryCoordinateSweeps.BinarySplit.choicesEquiv`, `OAI.BinaryCoordinateSweeps.BinarySplit.columnChoices`, `OAI.BinaryCoordinateSweeps.BinarySplit.fillSlot`, `OAI.BinaryCoordinateSweeps.BinarySplit.joinChoices`, `OAI.BinaryCoordinateSweeps.BinarySplit.leftOutsideEquiv`, `OAI.BinaryCoordinateSweeps.BinarySplit.rightOutsideEquiv`, `OAI.BinaryCoordinateSweeps.BinarySplit.rowChoices`, `OAI.BinaryCoordinateSweeps.BoardChoices`, `OAI.BinaryCoordinateSweeps.ConditionalChoices`, `OAI.BinaryCoordinateSweeps.ConditionalMomentTarget`, `OAI.BinaryCoordinateSweeps.ConstantSweepMixingTarget`, `OAI.BinaryCoordinateSweeps.Cyclic.chainWeight`, `OAI.BinaryCoordinateSweeps.Cyclic.deletedWeight`, `OAI.BinaryCoordinateSweeps.Density.MatchedPair`, `OAI.BinaryCoordinateSweeps.Density.WordType`, `OAI.BinaryCoordinateSweeps.Density.blockVec`, `OAI.BinaryCoordinateSweeps.Density.densityChannel`, `OAI.BinaryCoordinateSweeps.Density.empirical`, `OAI.BinaryCoordinateSweeps.Density.hamming`, `OAI.BinaryCoordinateSweeps.Density.kraus`, `OAI.BinaryCoordinateSweeps.Density.matchedEmbedding`, `OAI.BinaryCoordinateSweeps.Density.matrixSlice`, `OAI.BinaryCoordinateSweeps.Density.matrixTensorPower`, `OAI.BinaryCoordinateSweeps.Density.matrixTensorRect`, `OAI.BinaryCoordinateSweeps.Density.meanDensity`, `OAI.BinaryCoordinateSweeps.Density.pairVector`, `OAI.BinaryCoordinateSweeps.Density.parityProjection`, `OAI.BinaryCoordinateSweeps.Density.phaseAverage`, `OAI.BinaryCoordinateSweeps.Density.phasedVector`, `OAI.BinaryCoordinateSweeps.Density.piTensorMatrices`, `OAI.BinaryCoordinateSweeps.Density.pinch`, `OAI.BinaryCoordinateSweeps.Density.projectionMatrix`, `OAI.BinaryCoordinateSweeps.Density.rankOne`, `OAI.BinaryCoordinateSweeps.Density.reducedPhaseDensity`, `OAI.BinaryCoordinateSweeps.Density.regularizedMean`, `OAI.BinaryCoordinateSweeps.Density.reshape`, `OAI.BinaryCoordinateSweeps.Density.siteMatrix`, `OAI.BinaryCoordinateSweeps.Density.subsetCode` and 424 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `BinarySweep_Analytic_AnalyticTransfer`, `BinarySweep_Analytic_ComplexGrid`, `BinarySweep_Analytic_OneAxis`, `BinarySweep_Analytic_OneAxisBase`, `BinarySweep_Conditional_AugmentedBlock`, `BinarySweep_Conditional_AugmentedComplement`, `BinarySweep_Conditional_ComplementBlocks`, `BinarySweep_Conditional_ConditionalAverage`, `BinarySweep_Conditional_MainMomentInterface`, `BinarySweep_Conditional_Placement`, `BinarySweep_Conditional_PlacementAlternation`, `BinarySweep_Conditional_PlacementBlocks`, `BinarySweep_Conditional_PlacementCycleMoment`, `BinarySweep_Conditional_WeightedCycle`, `BinarySweep_FiniteLaws_ActiveTypes`, `BinarySweep_FiniteLaws_CyclicHolder`, `BinarySweep_FiniteLaws_FiniteLawAverage`, `BinarySweep_FiniteLaws_FiniteProductProbability`, `BinarySweep_FiniteLaws_IndependentOperator`, `BinarySweep_FiniteLaws_IndependentPush`, `BinarySweep_FiniteLaws_LightLineBound`, `BinarySweep_FiniteLaws_OccurrenceMoment`, `BinarySweep_FiniteLaws_OneCard`, `BinarySweep_FiniteLaws_PiCentrality`, `BinarySweep_FiniteLaws_SampleMoment`, `BinarySweep_FiniteLaws_UniformFiniteProbability`, `BinarySweep_GridBounds_BoardLaw`, `BinarySweep_GridBounds_DenseAssembly`, `BinarySweep_GridBounds_DiagonalDimension`, `BinarySweep_GridBounds_DiagonalRigidity`, `BinarySweep_GridBounds_EmptyGrid`, `BinarySweep_GridBounds_GridBoardAverage`, `BinarySweep_GridBounds_GridChildAverage`, `BinarySweep_GridBounds_GridDenseCost`, `BinarySweep_GridBounds_GridLaw`, `BinarySweep_GridBounds_GridProjectedMoment`, `BinarySweep_GridBounds_GridSplit`, `BinarySweep_GridBounds_GridSplitCost`, `BinarySweep_GridBounds_GridSplitFree`, `BinarySweep_GridBounds_GridSplitSweep`, `BinarySweep_GridBounds_GridSplitWeights`, `BinarySweep_GridBounds_GroupedMoments`, `BinarySweep_GridBounds_GroupedTypes`, `BinarySweep_GridBounds_GroupingGeometry`, `BinarySweep_MatrixBounds_BlockTrace`, `BinarySweep_MatrixBounds_CenteredMatrix`, `BinarySweep_MatrixBounds_HilbertBlockTrace`, `BinarySweep_MatrixBounds_MatrixProjection`, `BinarySweep_MatrixBounds_MatrixRegularize`, `BinarySweep_MatrixBounds_SchattenBounds`, `BinarySweep_MatrixBounds_SparsePinching`, `BinarySweep_MatrixBounds_SpectralMoment`, `BinarySweep_MatrixBounds_TraceConvex`, `BinarySweep_MatrixBounds_TraceInterpolation`, `BinarySweep_MatrixBounds_Whitening`, `BinarySweep_Mixing_BinaryLineDisk`, `BinarySweep_Mixing_BinaryMixingBounds`, `BinarySweep_Mixing_BinarySplitChoices`, `BinarySweep_Mixing_DimensionSeries`, `BinarySweep_Mixing_LongRowDimension`, `BinarySweep_Processes_AssignmentWeight`, `BinarySweep_Processes_Basic`, `BinarySweep_Processes_CoordinateLayerEdgeSwap`, `BinarySweep_Processes_GridSweepPath`, `BinarySweep_Processes_IndependentHistory`, `BinarySweep_Processes_LocalPathWeight`, `BinarySweep_Processes_SupportTimeBoundBounds`, `BinarySweep_Representations_FiniteUnitaryAverage`, `BinarySweep_Representations_IrrepTransport`, `BinarySweep_Representations_IsotypicDensity`, `BinarySweep_Representations_IsotypicMoment`, `BinarySweep_Representations_IsotypicOrthogonal`, `BinarySweep_Representations_IsotypicProjectionMoment`, `BinarySweep_Representations_IsotypicSpectral`, `BinarySweep_Representations_IsotypicTrace`, `BinarySweep_Representations_MatrixIsotypicWhitening`, `BinarySweep_Representations_MultiplicityBound`, `BinarySweep_Representations_UnitaryTransport`, `BinarySweep_SparseBounds_CenteredLineMoment`, `BinarySweep_SparseBounds_CenteredPlacement`, `BinarySweep_SparseBounds_FewSparse`, `BinarySweep_SparseBounds_ManySparse`, `BinarySweep_SparseBounds_SparseAmplitude`, `BinarySweep_SparseBounds_SparseKernel`, `BinarySweep_SparseBounds_SparseReduction`, `BinarySweep_TensorBounds_BlockTypes`, `BinarySweep_TensorBounds_EmpiricalTensor`, `BinarySweep_TensorBounds_EvenPostselection`, `BinarySweep_TensorBounds_PiTensorMatrices`, `BinarySweep_TensorBounds_SignedBlock`, `BinarySweep_TensorBounds_SignedBlocks`, `BinarySweep_TensorBounds_SignedCommutant`, `BinarySweep_TensorBounds_SignedConjugation`, `BinarySweep_TensorBounds_SignedPlacement`, `BinarySweep_TensorBounds_SignedWhitening`, `BinarySweep_TensorBounds_TensorPhases`, `BinarySweep_TensorBounds_TensorProductMatrices`, `BinarySweep_TensorBounds_TensorReduction`, `BinarySweep_TensorBounds_TypeMass`, `BinarySweep_Trajectories_EndpointEntryBound`, `BinarySweep_Trajectories_EndpointEvents`, `BinarySweep_Trajectories_EndpointFactors`, `BinarySweep_Trajectories_EndpointGood`, `BinarySweep_Trajectories_EndpointOccupancy`, `BinarySweep_Trajectories_EndpointPlacement`, `BinarySweep_Trajectories_EndpointValidity`, `BinarySweep_Trajectories_FallingMoment`, `BinarySweep_Trajectories_IsolatedCancellation`, `BinarySweep_Trajectories_PathExtension`, `BinarySweep_Trajectories_PathMomentMixed`, `BinarySweep_Trajectories_PathTelescope`, `BinarySweep_Trajectories_SharingProbability`, `BinarySweep_Trajectories_SparseOccupancy`, `BinarySweep_Trajectories_Trajectory`, `BinarySweep_Trajectories_TrajectoryComplement`, `BinarySweep_YoungTheory_CoindFibers`, `BinarySweep_YoungTheory_CoinductionTools`, `BinarySweep_YoungTheory_CutBranching`, `BinarySweep_YoungTheory_CutColumns`, `BinarySweep_YoungTheory_CutTensor`, `BinarySweep_YoungTheory_HookCut`, `BinarySweep_YoungTheory_HookHilbertOccurrence`, `BinarySweep_YoungTheory_HookInducedMoment`, `BinarySweep_YoungTheory_HookWord`, `BinarySweep_YoungTheory_KoszulBlocks`, `BinarySweep_YoungTheory_PhysicalHookInduced`, `BinarySweep_YoungTheory_YoungAnti`, `BinarySweep_YoungTheory_YoungDominance`, `BinarySweep_YoungTheory_YoungFactor`, `BinarySweep_YoungTheory_YoungFinite`, `BinarySweep_YoungTheory_YoungHilbert`, `BinarySweep_YoungTheory_YoungInducedMap`, `BinarySweep_YoungTheory_YoungPartition`, `BinarySweep_YoungTheory_YoungPlacement`, `BinarySweep_YoungTheory_YoungResolution`, `BinarySweep_YoungTheory_YoungSpecht`, `BinarySweep_YoungTheory_YoungTabloid`, `BinarySweep_YoungTheory_YoungTranspose`.
--
--   **Imports.** It imports the published bundle `Def_BinarySweep`.
--
--   **Imported by** (directly, in this split): the statements `OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually`, `OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp`, `OAI.BinaryCoordinateSweeps.constant_sweep_mixing`, `OAI.BinaryCoordinateSweeps.dense_induction_step_eventually`, `OAI.BinaryCoordinateSweeps.real_grid_bound`, `OAI.BinaryCoordinateSweeps.sparse_finite_radius` and `OAI.BinaryCoordinateSweeps.sparse_uniform_radius`; the proofs of `OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually`, `OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp`, `OAI.BinaryCoordinateSweeps.constant_sweep_mixing`, `OAI.BinaryCoordinateSweeps.dense_induction_step_eventually`, `OAI.BinaryCoordinateSweeps.real_grid_bound`, `OAI.BinaryCoordinateSweeps.sparse_finite_radius`, `OAI.BinaryCoordinateSweeps.sparse_uniform_radius` and `OAI.binary_sweep_contraction_and_mixing`.
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_BinarySweep

section
-- module Solutions.OAIB3_Bsw.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

def c0 : ℝ := (1 / 100 : ℝ) / 100
def e0 : ℝ := (1 / 100 : ℝ) / 100
def cExponent (s : ℕ) : ℝ := c0 + 1 / Real.sqrt (Real.log s)
def eExponent (s : ℕ) : ℝ := e0 - 1 / Real.sqrt (Real.log s)

def traceMoment {D : ℕ} (q : ℕ) (K : RepSpace D →L[ℂ] RepSpace D) : ℝ :=
  (LinearMap.trace ℂ (RepSpace D)
    (((ContinuousLinearMap.adjoint K) * K) ^ q).toLinearMap).re

def logMoment (T : ℝ) : EReal := (ENNReal.ofReal T).log

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_SupportTimeBoundBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

def boolSwitch (c : Bool) : Equiv.Perm Bool where
  toFun x := x ^^ c
  invFun x := x ^^ c
  left_inv x := by simp
  right_inv x := by simp

def sweepReachable (d : ℕ) : Submonoid (Equiv.Perm (Slot d)) where
  carrier := {g | ∃ l : List (SweepCoins d), (l.map (binarySweep d)).prod = g}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro g h ⟨l, rfl⟩ ⟨k, rfl⟩
    exact ⟨l ++ k, by simp⟩

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_CoordinateLayerEdgeSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteRandomWalk
variable {G : Type*} [Fintype G] [Group G]

def IsProbability (p : G → ℝ) : Prop := (∀ g, 0 ≤ p g) ∧ ∑ g, p g = 1

end FiniteRandomWalk

abbrev GridSlot {b : ℕ} (bits : Fin b → ℕ) := (j : Fin b) → Slot (bits j)
abbrev GridOutside {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :=
  (i : {i : Fin b // i ≠ j}) → Slot (bits i)
abbrev GridChoices {b : ℕ} (bits : Fin b → ℕ) :=
  (j : Fin b) → GridOutside bits j → Equiv.Perm (Slot (bits j))

def gridSize {b : ℕ} (bits : Fin b → ℕ) := ∏ j, 2 ^ bits j

lemma card_gridSlot {b : ℕ} (bits : Fin b → ℕ) :
    Fintype.card (GridSlot bits) = gridSize bits := by
  simp [GridSlot, Slot, gridSize, Fintype.card_pi]

def gridLayer {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    Equiv.Perm (GridSlot bits) :=
  let e := Equiv.piSplitAt j (fun i => Slot (bits i))
  e.trans ((Equiv.prodCongrLeft (g j)).trans e.symm)

def gridSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    Equiv.Perm (GridSlot bits) := (List.ofFn (gridLayer bits g)).reverse.prod

def lineLaw (d : ℕ) (z : ℝ) (g : Equiv.Perm (Slot d)) : ℝ :=
  (1 - z) * uniformLaw (Equiv.Perm (Slot d)) g + z * binaryLaw d g

def gridWeight {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) (g : GridChoices bits) : ℝ :=
  ∏ j, ∏ y, lineLaw (bits j) z (g j y)

structure PathFamily {b : ℕ} (bits : Fin b → ℕ) (h : ℕ) where
  position : Fin (b + 1) → Fin h → GridSlot bits
  disjoint : ∀ t, Function.Injective (position t)
  changes_only_stage : ∀ (j : Fin b) (k : Fin h) (i : Fin b), i ≠ j →
    position j.succ k i = position j.castSucc k i

def pathEvent {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : Prop :=
  ∀ (j : Fin b) (k : Fin h),
    gridLayer bits g j (H.position j.castSucc k) = H.position j.succ k

lemma chronological_trajectory {α : Type*} (b : ℕ) (f : Fin b → Equiv.Perm α)
    (x : Fin (b + 1) → α) (h : ∀ j, f j (x j.castSucc) = x j.succ) :
    (List.ofFn f).reverse.prod (x 0) = x (Fin.last b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp only [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton,
      Equiv.Perm.mul_apply]
    have h0 : f 0 (x 0) = x (Fin.succ 0) := by simpa using h 0
    rw [h0]
    have ht (j : Fin b) : f j.succ (x j.castSucc.succ) = x j.succ.succ := by
      simpa only [Fin.succ_castSucc] using h j.succ
    exact ih (fun j => f j.succ) (fun i => x i.succ) ht

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_MultiplicityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma intertwiner_retraction (f : IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ∃ r : IntertwiningMap σ ρ, ∀ v, r (f v) = v := by
  let fm := IntertwiningMap.equivLinearMapAsModule ρ σ f
  have hm : LinearMap.ker fm = ⊥ := LinearMap.ker_eq_bot.mpr hf
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨r,hr⟩ := MonoidAlgebra.exists_leftInverse_of_injective fm hm
  refine ⟨(IntertwiningMap.equivLinearMapAsModule σ ρ).symm r, fun v => ?_⟩
  exact DFunLike.congr_fun hr v

def isotypicSpan : Submodule ℂ W :=
  ⨆ f : IntertwiningMap ρ σ, LinearMap.range f.toLinearMap

def evaluation : V ⊗[ℂ] IntertwiningMap ρ σ →ₗ[ℂ] W :=
  TensorProduct.lift {
    toFun := fun v => {
      toFun := fun f => f v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    map_add' := by intro u v; ext f; exact map_add f u v
    map_smul' := by intro c v; ext f; exact map_smul f c v }

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma evaluation_range : LinearMap.range (evaluation ρ σ) = isotypicSpan ρ σ := by
  apply le_antisymm
  · rintro _ ⟨t,rfl⟩
    induction t using OAI.tensorInductionOn with
    | tmul v f =>
      exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) f) ⟨v,rfl⟩
    | add t u ht hu => simpa only [map_add] using Submodule.add_mem _ ht hu
  · apply iSup_le
    intro f w hw
    obtain ⟨v,rfl⟩ := hw
    exact ⟨TensorProduct.tmul ℂ v f, rfl⟩

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

def schurScalar : IntertwiningMap ρ ρ ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofBijective (Algebra.linearMap ℂ (IntertwiningMap ρ ρ))
    IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm

omit [Fintype G] in
lemma schurScalar_smul (f : IntertwiningMap ρ ρ) (v : V) :
    schurScalar ρ f • v = f v := by
  have he := (schurScalar ρ).symm_apply_apply f
  exact congrArg (fun t : IntertwiningMap ρ ρ => t v) he

omit [Fintype G] in
lemma schurScalar_one : schurScalar ρ (1 : IntertwiningMap ρ ρ) = 1 := by
  apply (schurScalar ρ).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (1 : IntertwiningMap ρ ρ) = algebraMap ℂ (IntertwiningMap ρ ρ) 1
  exact (map_one _).symm

def intertwinerPairing : IntertwiningMap ρ σ →ₗ[ℂ]
    IntertwiningMap σ ρ →ₗ[ℂ] ℂ :=
  (LinearMap.compr₂ ((IntertwiningMap.llcomp ρ σ ρ).flip) (schurScalar ρ).toLinearMap)

omit [FiniteDimensional ℂ W] in
lemma intertwinerPairing_injective : Function.Injective (intertwinerPairing ρ σ) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  by_contra hn
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hn
  obtain ⟨r,hr⟩ := intertwiner_retraction ρ σ f hfi
  have hc : r.comp f = 1 := by ext v; exact hr v
  have hz : intertwinerPairing ρ σ f = 0 := hf
  have he := DFunLike.congr_fun hz r
  change schurScalar ρ (r.comp f) = 0 at he
  rw [hc,schurScalar_one] at he
  exact one_ne_zero he

lemma exists_intertwiner_dual (l : Module.Dual ℂ (IntertwiningMap ρ σ)) :
    ∃ r : IntertwiningMap σ ρ, ∀ f : IntertwiningMap ρ σ, ∀ v : V,
      r (f v) = l f • v := by
  have hs := (LinearMap.flip_surjective_iff₁ (B := intertwinerPairing ρ σ)).mpr
    (intertwinerPairing_injective ρ σ)
  obtain ⟨r,hr⟩ := hs l
  refine ⟨r,fun f v => ?_⟩
  have he := DFunLike.congr_fun hr f
  change schurScalar ρ (r.comp f) = l f at he
  rw [← he]
  exact (schurScalar_smul ρ (r.comp f) v).symm

theorem evaluation_injective : Function.Injective (evaluation ρ σ) := by
  let b := Module.finBasis ℂ (IntertwiningMap ρ σ)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro t ht
  change t = 0
  have ht0 : evaluation ρ σ t = 0 := ht
  apply e.injective
  apply Finsupp.ext
  intro i
  obtain ⟨r,hr⟩ := exists_intertwiner_dual ρ σ (b.coord i)
  have he : ∀ x : V ⊗[ℂ] IntertwiningMap ρ σ,
      r (evaluation ρ σ x) = e x i := by
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul v f =>
      change r (f v) = _
      rw [hr]
      exact (TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b v f i).symm
    | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  simpa only [ht0,map_zero,Finsupp.zero_apply] using (he t).symm

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

def evaluationToIsotypic : V ⊗[ℂ] IntertwiningMap ρ σ →ₗ[ℂ] isotypicSpan ρ σ :=
  (evaluation ρ σ).codRestrict _ (fun x => by
    rw [← evaluation_range]; exact ⟨x,rfl⟩)

lemma evaluationToIsotypic_bijective : Function.Bijective (evaluationToIsotypic ρ σ) := by
  constructor
  · intro x y h
    apply evaluation_injective ρ σ
    exact congrArg Subtype.val h
  · intro y
    have hy : y.val ∈ LinearMap.range (evaluation ρ σ) := by
      rw [evaluation_range]; exact y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩

def evaluationEquiv : V ⊗[ℂ] IntertwiningMap ρ σ ≃ₗ[ℂ] isotypicSpan ρ σ :=
  LinearEquiv.ofBijective (evaluationToIsotypic ρ σ) (evaluationToIsotypic_bijective ρ σ)

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [ρ.IsIrreducible] in
lemma isotypic_invariant_of_compatible (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (hAB : ∀ f : IntertwiningMap ρ σ, ∀ v : V, B (f v) = f (A v)) :
    ∀ w ∈ isotypicSpan ρ σ, B w ∈ isotypicSpan ρ σ := by
  intro w hw
  apply Submodule.iSup_induction (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap)
    (motive := fun w => B w ∈ isotypicSpan ρ σ) hw
  · intro f w hw
    obtain ⟨v,rfl⟩ := hw
    rw [show f.toLinearMap v = f v from rfl,hAB]
    exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) f) ⟨A v,rfl⟩
  · simp
  · intro x y hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

def groupAverage (p : G → ℂ) : V →ₗ[ℂ] V := ∑ g, p g • ρ g

def evenMoment (q : ℕ) (A : V →ₗ[ℂ] V) : ℝ :=
  (LinearMap.trace ℂ V ((A.adjoint*A)^q)).re

omit [Fintype G] in
lemma unitary_rep_adjoint (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) :
    (ρ g).adjoint = ρ g⁻¹ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  let U : V →ₗᵢ[ℂ] V := { toLinearMap := ρ g, norm_map' := hρ g }
  have he := U.inner_map_map (ρ g⁻¹ x) y
  change inner ℂ (ρ g (ρ g⁻¹ x)) (ρ g y) = inner ℂ (ρ g⁻¹ x) y at he
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply] at he
  exact he.symm

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_FiniteUnitaryAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def complexAverage (ρ : Representation ℂ G V) (p : G → ℂ) : V →L[ℂ] V :=
  (Irrep.groupAverage ρ p).toContinuousLinearMap

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_IndependentOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def continuousRep (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma gridSweep_path {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) (hg : pathEvent H g) (k : Fin h) :
    gridSweep bits g (H.position 0 k) = H.position (Fin.last b) k :=
  chronological_trajectory b (gridLayer bits g) (fun t => H.position t k) (fun j => hg j k)

abbrev FreeSlot {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (t : Fin (b + 1)) := {x : GridSlot bits // x ∉ Set.range (H.position t)}

instance freeSlotFintype {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (t : Fin (b + 1)) : Fintype (FreeSlot H t) := Fintype.ofFinite _

lemma card_freeSlot {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (t : Fin (b + 1)) : Fintype.card (FreeSlot H t) = gridSize bits - h := by
  classical
  rw [show Fintype.card (FreeSlot H t) =
    Fintype.card (GridSlot bits) - Fintype.card (Set.range (H.position t)) from
      Fintype.card_subtype_compl (fun x => x ∈ Set.range (H.position t))]
  rw [card_gridSlot]
  have hr : Fintype.card (Set.range (H.position t)) = h := by
    let e : Fin h ↪ GridSlot bits := ⟨H.position t, H.disjoint t⟩
    simpa [e] using Fintype.card_range e
  rw [hr]

def freeIdentification {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    FreeSlot H 0 ≃ FreeSlot H (Fin.last b) :=
  Fintype.equivOfCardEq (by rw [card_freeSlot, card_freeSlot])

def remainingBijection {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) (hg : pathEvent H g) :
    FreeSlot H 0 ≃ FreeSlot H (Fin.last b) where
  toFun x := ⟨gridSweep bits g x, by
    rintro ⟨k, hk⟩
    exact x.property ⟨k, (gridSweep bits g).injective ((gridSweep_path H g hg k).trans hk)⟩⟩
  invFun y := ⟨(gridSweep bits g).symm y, by
    rintro ⟨k, hk⟩
    apply y.property
    refine ⟨k, ?_⟩
    rw [← gridSweep_path H g hg k, hk]
    exact (gridSweep bits g).apply_symm_apply y⟩
  left_inv x := by apply Subtype.ext; exact (gridSweep bits g).symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact (gridSweep bits g).apply_symm_apply y

def remainingPerm {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) (hg : pathEvent H g) : Equiv.Perm (FreeSlot H 0) :=
  (remainingBijection H g hg).trans (freeIdentification H).symm

def conditionalNormalizer {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) : ℝ := by
  classical
  exact ∑ g : GridChoices bits, if pathEvent H g then gridWeight bits z g else 0

def conditionalOperator {b h D : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) :
    RepSpace D →L[ℂ] RepSpace D := by
  classical
  exact LinearMap.toContinuousLinearMap
    ((conditionalNormalizer H z : ℂ)⁻¹ • ∑ g : GridChoices bits,
      if hg : pathEvent H g then (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg)
      else 0)

def lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : ℕ := by
  classical
  exact Fintype.card {k : Fin h // (fun i : {i : Fin b // i ≠ j} =>
    H.position j.castSucc k i) = y}

def pathCost {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) : ℝ :=
  ∑ j, ∑ y : GridOutside bits j,
    Real.log (((2 ^ bits j : ℕ) : ℝ) ^ lineHoles H j y /
      (Nat.descFactorial (2 ^ bits j) (lineHoles H j y) : ℝ))

def ConditionalMomentTarget : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∃ q : ℕ, 0 < q ∧ ∃ zStar : ℝ, 0 < zStar ∧
    ∀ b : ℕ, 1 ≤ b → ∀ bits : Fin b → ℕ, (∀ j, r ≤ bits j ∧ bits j ≤ 2 * r) →
    ∀ h : ℕ, ∀ H : PathFamily bits h, ∀ z : ℝ, 0 ≤ z → z ≤ zStar →
    ∀ D : ℕ, ∀ ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D),
      ρ.IsIrreducible → IsUnitaryRep ρ →
      logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
        ((-cExponent (gridSize bits) * Real.log D +
          eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal)

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryLineDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

def complexLineLaw (d : ℕ) (z : ℂ) (g : Equiv.Perm (Slot d)) : ℂ :=
  (1-z)*(uniformLaw (Equiv.Perm (Slot d)) g:ℂ)+z*(binaryLaw d g:ℂ)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_ComplexGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

def gridStageHom (j : Fin b) :
    (GridOutside bits j → Equiv.Perm (Slot (bits j))) →* Equiv.Perm (GridSlot bits) where
  toFun f := (Equiv.piSplitAt j (fun i => Slot (bits i))).symm.permCongr
    (Equiv.prodCongrLeft f)
  map_one' := by
    have h : Equiv.prodCongrLeft (1 : GridOutside bits j → Equiv.Perm (Slot (bits j)))=1 := by
      ext x <;> rfl
    change (Equiv.piSplitAt j (fun i => Slot (bits i))).symm.permCongrHom
      (Equiv.prodCongrLeft 1)=1
    rw [h,map_one]
  map_mul' f g := by
    ext x
    simp [Equiv.permCongr_apply,Equiv.prodCongrLeft_apply]

def complexGridWeight (z : ℂ) (g : GridChoices bits) : ℂ :=
  ∏j, ∏y, complexLineLaw (bits j) z (g j y)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) V)

def complexGridAverage (z : ℂ) : V →L[ℂ] V :=
  ∑g : GridChoices bits, complexGridWeight bits z g • continuousRep ρ (gridSweep bits g)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_CyclicHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Cyclic

variable {A : Type*} [Fintype A]

def chainWeight (n : ℕ) (p : Fin n → A → A → ℝ) (x : Fin (n+1) → A) : ℝ :=
  ∏ i, p i (x i.castSucc) (x i.succ)

def deletedWeight (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (r : Fin (n+1)) (x : Fin (n+1) → A) : ℝ :=
  ∏ i, if i = r then 1 else p i (x i) (x (finRotate (n+1) i))

end BinaryCoordinateSweeps.Cyclic

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_IndependentHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section Assignments
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [Fintype I]

def Assigns (A B : I ↪ X) (σ : Equiv.Perm X) : Prop := ∀ i, σ (A i) = B i

end Assignments

def fromInitial {G : Type*} [Group G] (p : G → ℝ) (initial : G) : G → ℝ :=
  fun g => p (g * initial⁻¹)

def ConstantSweepMixingTarget : Prop :=
  ∃ w : ℕ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ initial : Equiv.Perm (Slot d),
      totalVariation (fromInitial (sweepLaw d w) initial)
        (uniformLaw (Equiv.Perm (Slot d))) < ε

def fallingCost (m u : ℕ) : ℝ := Real.log ((m : ℝ) ^ u / (m.descFactorial u : ℝ))

attribute [local instance] Classical.propDecidable

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_AssignmentWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section AssignmentWeights
attribute [local instance] Classical.propDecidable
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

def assignmentWeight (p : Equiv.Perm X → ℝ) (A B : I ↪ X) : ℝ :=
  ∑ σ, if Assigns A B σ then p σ else 0

end AssignmentWeights

attribute [local instance] Classical.propDecidable

abbrev LinePaths {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) :=
  {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}

def lineInput {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : LinePaths H j y ↪ Slot (bits j) where
  toFun k := H.position j.castSucc k.val j
  inj' k l he := by
    apply Subtype.ext
    apply H.disjoint j.castSucc
    funext i
    by_cases hi : i = j
    · subst i; exact he
    · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm

def lineOutput {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : LinePaths H j y ↪ Slot (bits j) where
  toFun k := H.position j.succ k.val j
  inj' k l he := by
    apply Subtype.ext
    apply H.disjoint j.succ
    funext i
    by_cases hi : i = j
    · subst i; exact he
    · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
      exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm

def linePerturbationRadius (r : ℕ) : ℝ := 1 / (2 * ((2 ^ (2 * r)).factorial : ℝ))

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_LocalPathWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

def localPathWeight {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (j : Fin b) (y : GridOutside bits j) : ℝ :=
  assignmentWeight (lineLaw (bits j) z) (lineInput H j y) (lineOutput H j y)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_Placement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

abbrev ConditionalChoices {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :=
  {g : GridChoices bits // pathEvent H g}

instance conditionalChoicesFintype {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Fintype (ConditionalChoices H) := Fintype.ofFinite _

def conditionalChoiceWeight {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (g : ConditionalChoices H) : ℝ :=
  gridWeight bits z g.val / conditionalNormalizer H z

abbrev Placement {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (k : ℕ) (t : Fin (b+1)) := Fin k ↪ FreeSlot H t

def placementBijection {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (k : ℕ) (g : ConditionalChoices H) :
    Placement H k 0 ≃ Placement H k (Fin.last b) :=
  (Equiv.refl (Fin k)).embeddingCongr (remainingBijection H g.val g.property)

def placementProbability {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) {k : ℕ} (x : Placement H k 0) (y : Placement H k (Fin.last b)) : ℝ := by
  classical
  exact ∑ g : ConditionalChoices H,
    if placementBijection H k g x = y then conditionalChoiceWeight H z g else 0

section FiniteBijectionKernel
variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

def bijectionKernel (w : Ω → ℝ) (e : Ω → A ≃ B) (x : A) (y : B) : ℝ :=
  ∑ ω, if e ω x = y then w ω else 0

end FiniteBijectionKernel

def placementIdentification {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (k : ℕ) :
    Placement H k 0 ≃ Placement H k (Fin.last b) :=
  (Equiv.refl (Fin k)).embeddingCongr (freeIdentification H)

def placementKernel {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) {k : ℕ} (x y : Placement H k 0) : ℝ :=
  placementProbability H z x (placementIdentification H k y)

def placementEdge {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (reverse : Bool) {k : ℕ} (x y : Placement H k 0) : ℝ :=
  if reverse then placementKernel H z y x else placementKernel H z x y

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

structure PathExtension {b h h' : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (H' : PathFamily bits h') where
  labels : Fin h ↪ Fin h'
  position_eq : ∀ t i, H'.position t (labels i) = H.position t i

namespace PathExtension
variable {b h h' : ℕ} {bits : Fin b → ℕ}
  {H : PathFamily bits h} {H' : PathFamily bits h'}

def lineEmbedding (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j) :
    LinePaths H j y ↪ LinePaths H' j y where
  toFun i := ⟨E.labels i.val, by
    change (fun a : {a : Fin b // a ≠ j} => H'.position j.castSucc (E.labels i.val) a) = y
    rw [E.position_eq]
    exact i.property⟩
  inj' i k hik := Subtype.ext (E.labels.injective (congrArg Subtype.val hik))

lemma pathEvent_mono (E : PathExtension H H') {g : GridChoices bits}
    (hg : pathEvent H' g) : pathEvent H g := by
  intro j i
  simpa only [E.position_eq] using hg j (E.labels i)

end PathExtension

def conditionalEventWeight {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (P : GridChoices bits → Prop) : ℝ :=
  ∑ g : ConditionalChoices H, if P g.val then conditionalChoiceWeight H z g else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

abbrev Cell (μ : YoungDiagram) := {c // c ∈ μ.cells}
def row {μ : YoungDiagram} (x : Cell μ) : ℕ := x.val.1
def col {μ : YoungDiagram} (x : Cell μ) : ℕ := x.val.2

def columnCells (μ : YoungDiagram) (j : ℕ) : Finset (Cell μ) :=
  Finset.univ.filter (fun x => col x = j)

def fiberStabilizer {X Y : Type*} (f : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {π | ∀ x, f (π x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro a b ha hb x; exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ x)
    simpa using h.symm

abbrev rowStabilizer (μ : YoungDiagram) := fiberStabilizer (row (μ := μ))
abbrev colStabilizer (μ : YoungDiagram) := fiberStabilizer (col (μ := μ))

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
abbrev G := Equiv.Perm (Cell μ)

def labels (π : G μ) : Cell μ → ℕ := fun x => row (π⁻¹ x)

def Tabloid := Set.range (labels μ)

def tabloidOfPerm (π : G μ) : Tabloid μ := ⟨labels μ π, π, rfl⟩

lemma tabloidOfPerm_surjective : Function.Surjective (tabloidOfPerm μ) := by
  rintro ⟨f, π, rfl⟩
  exact ⟨π, rfl⟩

instance instFintypeElemForallCellNatTabloid : Fintype (Tabloid μ) := Fintype.ofSurjective _ (tabloidOfPerm_surjective μ)
instance instDecidableEqElemForallCellNatTabloid : DecidableEq (Tabloid μ) := Classical.decEq _

noncomputable def actTabloid (π : G μ) (t : Tabloid μ) : Tabloid μ := by
  refine ⟨fun x => t.val (π⁻¹ x), ?_⟩
  obtain ⟨g, hg⟩ := t.property
  refine ⟨π * g, ?_⟩
  ext x
  simp [labels, ← hg]

instance instMulActionGElemForallCellNatTabloid : MulAction (G μ) (Tabloid μ) where
  smul := actTabloid μ
  one_smul t := by
    change actTabloid μ 1 t = t
    apply Subtype.ext
    funext x
    simp [actTabloid]
  mul_smul π σ t := by
    change actTabloid μ (π * σ) t = actTabloid μ π (actTabloid μ σ t)
    apply Subtype.ext
    funext x
    simp [actTabloid]

lemma smul_tabloid_apply (π : G μ) (t : Tabloid μ) (x : Cell μ) :
    (π • t).val x = t.val (π⁻¹ x) := rfl

@[simp] lemma smul_tabloidOfPerm (π σ : G μ) :
    π • tabloidOfPerm μ σ = tabloidOfPerm μ (π * σ) := by
  apply Subtype.ext
  funext x
  simp [smul_tabloid_apply, tabloidOfPerm, labels]

lemma tabloidOfPerm_eq_iff (π σ : G μ) :
    tabloidOfPerm μ π = tabloidOfPerm μ σ ↔ π⁻¹ * σ ∈ rowStabilizer μ := by
  constructor
  · intro h x
    have he := congrArg (fun t : Tabloid μ => t.val (σ x)) h
    simpa [tabloidOfPerm, labels] using he
  · intro h
    apply Subtype.ext
    funext x
    have he := h (σ⁻¹ x)
    simpa [tabloidOfPerm, labels] using he

def tabloidRepresentation : Representation ℂ (G μ) (Tabloid μ → ℂ) where
  toFun π :=
    { toFun := fun v t => v (π⁻¹ • t)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v t; simp
  map_mul' π σ := by ext v t; simp [mul_smul]

lemma tabloidRepresentation_apply (π : G μ) (v : Tabloid μ → ℂ) (t : Tabloid μ) :
    tabloidRepresentation μ π v t = v (π⁻¹ • t) := rfl

def tabloidBasis (t : Tabloid μ) : Tabloid μ → ℂ := Pi.single t 1

lemma rep_basis (π : G μ) (t : Tabloid μ) :
    tabloidRepresentation μ π (tabloidBasis μ t) = tabloidBasis μ (π • t) := by
  ext u
  simp only [tabloidRepresentation_apply, tabloidBasis, Pi.single_apply]
  simp only [inv_smul_eq_iff]

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungAnti
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

def signC : G μ →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

lemma signC_eq (g : G μ) : signC μ g = ((Equiv.Perm.sign g : ℤ) : ℂ) := rfl

lemma signC_sq (g : G μ) : signC μ g * signC μ g = 1 := by
  rw [signC_eq, ← Int.cast_mul]
  norm_cast
  exact congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign g))

abbrev C := colStabilizer μ
instance instFintypeSubtypePermCellMemSubgroupC : Fintype (C μ) := Fintype.ofFinite _

def columnAnti : Module.End ℂ (Tabloid μ → ℂ) :=
  ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val

def polytabloid : Tabloid μ → ℂ :=
  columnAnti μ (tabloidBasis μ (tabloidOfPerm μ 1))

lemma sum_tabloidBasis (v : Tabloid μ → ℂ) :
    ∑ t : Tabloid μ, v t • tabloidBasis μ t = v := by
  ext t
  simp [tabloidBasis, Pi.single_apply, Finset.sum_apply]

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungSpecht
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

def polyModule : (tabloidRepresentation μ).asModule :=
  (tabloidRepresentation μ).asModuleEquiv.symm (polytabloid μ)

def antiModule : Module.End ℂ (tabloidRepresentation μ).asModule :=
  (tabloidRepresentation μ).asModuleEquiv.symm.toLinearMap.comp
    ((columnAnti μ).comp (tabloidRepresentation μ).asModuleEquiv.toLinearMap)

def Specht : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule :=
  Submodule.span _ {polyModule μ}

lemma polyModule_mem_Specht : polyModule μ ∈ Specht μ :=
  Submodule.subset_span (Set.mem_singleton _)

end BinaryCoordinateSweeps.Young

end

open scoped MonoidAlgebra BigOperators

namespace BinaryCoordinateSweeps.Young

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V] [IsScalarTower ℂ A V]

def restrictLinearEquiv : RestrictScalars ℂ A V ≃ₗ[ℂ] V where
  __ := RestrictScalars.addEquiv ℂ A V
  map_smul' a v := by
    change RestrictScalars.addEquiv ℂ A V (a • v) = a • RestrictScalars.addEquiv ℂ A V v
    rw [RestrictScalars.addEquiv_map_smul, algebraMap_smul]

variable (μ : YoungDiagram)
abbrev SpechtSpace := RestrictScalars ℂ ℂ[G μ] (Specht μ)

-- Use the same additive monoid for the restricted module and its additive group.
instance SpechtSpace.instAddCommGroup : AddCommGroup (SpechtSpace μ) :=
  Module.addCommMonoidToAddCommGroup ℂ

instance instModuleComplexSpechtSpace : @Module ℂ (SpechtSpace μ) _ (SpechtSpace.instAddCommGroup μ).toAddCommMonoid :=
  RestrictScalars.module ℂ ℂ[G μ] (Specht μ)

def spechtRep : Representation ℂ (G μ) (SpechtSpace μ) := Representation.ofModule (Specht μ)

instance instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht : FiniteDimensional ℂ (Specht μ) :=
  Module.Finite.of_injective ((Specht μ).subtype.restrictScalars ℂ) Subtype.val_injective

instance instFiniteDimensionalComplexSpechtSpace : FiniteDimensional ℂ (SpechtSpace μ) :=
  Module.Finite.equiv (restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm

def spechtInclude : SpechtSpace μ →ₗ[ℂ] (Tabloid μ → ℂ) :=
  (tabloidRepresentation μ).asModuleEquiv.toLinearMap.comp
    (((Specht μ).subtype.restrictScalars ℂ).comp
      (restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).toLinearMap)

lemma spechtInclude_injective : Function.Injective (spechtInclude μ) :=
  (tabloidRepresentation μ).asModuleEquiv.injective.comp
    (Subtype.val_injective.comp restrictLinearEquiv.injective)

lemma spechtInclude_rep (g : G μ) (v : SpechtSpace μ) :
    spechtInclude μ (spechtRep μ g v) = tabloidRepresentation μ g (spechtInclude μ v) := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((RestrictScalars.addEquiv ℂ ℂ[G μ] (Specht μ) (Representation.ofModule (Specht μ) g v)).val) = _
  simp only [Representation.ofModule, MonoidAlgebra.lift_symm_apply,
    RestrictScalars.lsmul_apply_apply, AddEquiv.apply_symm_apply, Submodule.coe_smul_of_tower,
    Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul]
  rfl

def spechtPoly : SpechtSpace μ :=
  (restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
    ⟨polyModule μ, polyModule_mem_Specht μ⟩

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

def diagonal (μ : YoungDiagram) (x : Cell μ) : ℕ := row x + col x
abbrev diagonalStabilizer (μ : YoungDiagram) := fiberStabilizer (diagonal μ)
instance diagonalStabilizer_fintype (μ : YoungDiagram) : Fintype (diagonalStabilizer μ) :=
  Fintype.ofFinite _

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberQuotientLabel (f : X → Y) :
    (Equiv.Perm X ⧸ fiberStabilizer f) → (X → Y) :=
  Quotient.lift (fun (g : Equiv.Perm X) => fun x => f (g⁻¹ x)) (by
    intro g h he
    have he' := (QuotientGroup.leftRel_apply.mp he : g⁻¹*h ∈ fiberStabilizer f)
    funext x
    have hh := he' (h⁻¹ x)
    simpa using hh)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

def assembleFiberPerm (f : X → Y) (p : ∀ y, Equiv.Perm {x // f x = y}) :
    fiberStabilizer f :=
  ⟨(Equiv.sigmaFiberEquiv f).permCongr (Equiv.sigmaCongrRight p), by
    intro x
    exact (p (f x) ⟨x,rfl⟩).property⟩

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev M (ι : Type*) := Matrix ι ι ℂ

def diagPower (d : ι → ℝ) (z : ℂ) : M ι :=
  Matrix.diagonal fun i => if d i = 0 then 0 else Complex.exp (z * (Real.log (d i) : ℂ))

def word {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ) (x : Fin m → ℂ) : M ι :=
  (List.ofFn (fun j => A j * diagPower (d j) (x j))).prod

def traceWord {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ) (x : Fin m → ℂ) : ℂ :=
  Matrix.trace (word A d x)

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagReal (s : ι → ℝ) : M ι := Matrix.diagonal (fun i => (s i : ℂ))

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SpectralMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixMoment (q : ℕ) (A : M ι) : ℝ := (Matrix.trace ((star A * A)^q)).re

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Admissible {m : ℕ} (d : Fin m → ι → ℝ) (x : Fin m → ℝ) : Prop :=
  ∀ A : Fin m → M ι, (∀ j, ‖A j‖ ≤ 1) →
    ‖traceWord A d (fun j => (x j : ℂ))‖ ≤ 1

def exponentSet {m : ℕ} (d : Fin m → ι → ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ Admissible d x}

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def schatten (q : ℕ) (A : M ι) : ℝ :=
  matrixMoment q A ^ (((2*q : ℕ) : ℝ)⁻¹)

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_MatrixProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

def projectionMatrix (S : Submodule ℂ (EuclideanSpace ℂ I)) : Matrix I I ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm S.starProjection

omit [DecidableEq I] in
lemma projectionMatrix_commutes (S : Submodule ℂ (EuclideanSpace ℂ I))
    (f : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ I) (hf : S.map f.toLinearMap = S)
    (v : EuclideanSpace ℂ I) :
    f (S.starProjection v) = S.starProjection (f v) := by
  have h := f.map_starProjection S v
  simpa only [hf] using h

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TypeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]

def wordCounts (w : I → A) : A →₀ ℕ := ∑ i, Finsupp.single (w i) 1

omit [Fintype A] [DecidableEq A] [DecidableEq I] in
lemma wordCounts_total (w : I → A) : (wordCounts w).sum (fun _ k => k) = Fintype.card I := by
  rw [wordCounts, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp

omit [DecidableEq A] [DecidableEq I] in
lemma wordCounts_sum (w : I → A) : ∑ a, wordCounts w a = Fintype.card I := by
  have h := wordCounts_total w
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) (fun _ k => k) (by simp)] at h
  exact h

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TensorPhases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def tensorPhase (n : ℕ) (θ : A → ZMod (n+1)) (w : Fin n → A) : ℂ :=
  ∏ i, ZMod.stdAddChar (θ (w i))

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def rankOne (v : I → ℂ) : Matrix I I ℂ := vecMulVec v (star v)

def typeVector (f : I → T) (t : T) : I → ℂ := fun i => if f i = t then 1 else 0

def typeOnes (f : I → T) (t : T) : Matrix I I ℂ := rankOne (typeVector f t)

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev WordType (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :=
  ↥(Finset.piAntidiag (Finset.univ : Finset A) n)

def wordType (n : ℕ) (w : Fin n → A) : WordType A n :=
  ⟨fun a => wordCounts w a, Finset.mem_piAntidiag.mpr ⟨by simpa using wordCounts_sum w, by simp⟩⟩

def symmetricProjector (n : ℕ) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  fun w v => if wordType n w = wordType n v then
    ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_EmpiricalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def tensorAmplitude (n : ℕ) (r : A → ℝ) (w : Fin n → A) : ℝ := ∏ i, Real.sqrt (r (w i))

def tensorProductVector (n : ℕ) (v : A → ℂ) : (Fin n → A) → ℂ := fun w => ∏ i, v (w i)

def phasedVector (n : ℕ) (r : A → ℝ) (θ : A → ZMod (n+1)) : A → ℂ :=
  fun a => (Real.sqrt (r a) : ℂ) * ZMod.stdAddChar (θ a)

def phaseAverage (n : ℕ) (r : A → ℝ) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  (((n+1 : ℕ) : ℂ)^Fintype.card A)⁻¹ •
    ∑ θ : A → ZMod (n+1), rankOne (tensorProductVector n (phasedVector n r θ))

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def empirical (n : ℕ) (c : WordType A n) : A → ℝ := fun a => c.val a / (n : ℝ)

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TensorReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

def reshape (e : K → A × B) (v : K → ℂ) : Matrix A B ℂ :=
  fun a b => ∑ k, if e k = (a,b) then v k else 0

def kraus (e : K → A × B) (b : B) : Matrix A K ℂ :=
  fun a k => if e k = (a,b) then 1 else 0

def densityChannel (e : K → A × B) (M : Matrix K K ℂ) : Matrix A A ℂ :=
  ∑ b, kraus e b * M * (kraus e b).conjTranspose

def wordPair (n : ℕ) (e : K → A × B) : (Fin n → K) → (Fin n → A) × (Fin n → B) :=
  fun w => (fun i => (e (w i)).1, fun i => (e (w i)).2)

def matrixTensorPower (n : ℕ) (M : Matrix A A ℂ) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  fun x y => ∏ i, M (x i) (y i)

def matrixTensorRect (n : ℕ) (U : Matrix A B ℂ) : Matrix (Fin n → A) (Fin n → B) ℂ :=
  fun x y => ∏ i, U (x i) (y i)

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

def reducedPhaseDensity (n : ℕ) (e : K → A × B) (c : WordType K n)
    (t : K → ZMod (n+1)) : Matrix A A ℂ :=
  reshape e (phasedVector n (empirical n c) t) *
    (reshape e (phasedVector n (empirical n c) t)).conjTranspose

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_UnitaryTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

section Algebra
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def conjugateRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W :=
  e.conjRingEquiv.toMonoidHom.comp ρ

def conjugateEquiv (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : ρ.Equiv (conjugateRep ρ e) :=
  .mk e (by intro g; ext v; change e (ρ g v) = e (ρ g (e.symm (e v))); rw [e.symm_apply_apply])

end Algebra

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungHilbert
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

variable (μ : YoungDiagram)

def spechtHilbertInclude : SpechtSpace μ →ₗ[ℂ] EuclideanSpace ℂ (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm.toLinearMap.comp (spechtInclude μ)

lemma spechtHilbertInclude_injective : Function.Injective (spechtHilbertInclude μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm.injective.comp (spechtInclude_injective μ)

abbrev SpechtHilbert := (spechtHilbertInclude μ).range

def spechtHilbertEquiv : SpechtSpace μ ≃ₗ[ℂ] SpechtHilbert μ :=
  LinearEquiv.ofInjective (spechtHilbertInclude μ) (spechtHilbertInclude_injective μ)

def hilbertSpecht : Representation ℂ (G μ) (SpechtHilbert μ) :=
  letI : AddCommGroup (SpechtSpace μ) := Module.addCommMonoidToAddCommGroup ℂ
  Irrep.conjugateRep (spechtRep μ) (spechtHilbertEquiv μ)

instance hilbertNormed : NormedAddCommGroup (SpechtHilbert μ) :=
  Submodule.normedAddCommGroup _
instance hilbertInner : InnerProductSpace ℂ (SpechtHilbert μ) :=
  Submodule.innerProductSpace _

end BinaryCoordinateSweeps.Young

end

section

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

def koszulSign (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) : ℤˣ :=
  ∏ x ∈ finPairsLT n, if β x.1 = true ∧ β x.2 = true then
    (if g x.1 ≤ g x.2 then -1 else 1) else 1

@[simp] lemma koszulSign_one (β : Fin n → Bool) : koszulSign β 1 = 1 := by
  apply Finset.prod_eq_one
  intro x hx
  simp only [one_apply]
  rw [ite_eq_right (mem_finPairsLT.mp hx).not_ge]
  simp

lemma koszulSign_inv (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    koszulSign (β ∘ g.symm) g⁻¹ = koszulSign β g := by
  unfold koszulSign
  apply prod_nbij (signBijAux g⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj
  rintro ⟨a,b⟩ hab
  have hab' : b < a := mem_finPairsLT.mp hab
  by_cases h : g.symm b < g.symm a
  · simp [signBijAux, h, hab'.not_ge]
  · simp [signBijAux, h, hab'.le, and_comm, le_of_not_gt h]

lemma koszulSign_mul (β : Fin n → Bool) (f g : Equiv.Perm (Fin n)) :
    koszulSign β (f*g) = koszulSign (β ∘ g.symm) f * koszulSign β g := by
  rw [← koszulSign_inv β g]
  unfold koszulSign
  rw [← Finset.prod_mul_distrib]
  apply prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj
  rintro ⟨a,b⟩ hab
  dsimp only [signBijAux]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [hg, mul_apply, hab.not_ge]
  obtain hf | hf := (f.injective.ne (g.injective.ne hab.ne)).lt_or_gt <;>
    simp_all [mul_apply, le_of_lt, not_le_of_gt, not_lt_of_ge, and_comm]

lemma koszulSign_sq (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    koszulSign β g * koszulSign β g = 1 := by
  exact Int.units_mul_self _

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_EvenPostselection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

variable {P : Type*} [DecidableEq P]

def MatchedPair (p : A → P) := {x : A × A // p x.1 = p x.2}
instance instFintypeMatchedPair (p : A → P) : Fintype (MatchedPair p) :=
  inferInstanceAs (Fintype {pair : A × A // p pair.1 = p pair.2})
instance instDecidableEqMatchedPair (p : A → P) : DecidableEq (MatchedPair p) :=
  inferInstanceAs (DecidableEq {pair : A × A // p pair.1 = p pair.2})

def matchedEmbedding (p : A → P) : MatchedPair p → A × A := Subtype.val

def pairVector (n : ℕ) (p : A → P) (Q : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (Fin n → MatchedPair p) → ℂ :=
  fun w => Q (fun i => (w i).val.1) (fun i => (w i).val.2)

def wordPerm (n : ℕ) (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → A) where
  toFun x := x ∘ g
  invFun x := x ∘ g.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} {n : ℕ}

def signC (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) : ℂ :=
  ((koszulSign β g : ℤ) : ℂ)

@[simp] lemma signC_one (β : Fin n → Bool) : signC β 1 = 1 := by simp [signC]
lemma signC_mul (β : Fin n → Bool) (f g : Equiv.Perm (Fin n)) :
    signC β (f*g) = signC (β ∘ g.symm) f * signC β g := by
  simp only [signC, koszulSign_mul, Units.val_mul, Int.cast_mul]
lemma signC_sq (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    signC β g * signC β g = 1 := by
  unfold signC
  rw [← Int.cast_mul, ← Units.val_mul, koszulSign_sq]
  norm_num
@[simp] lemma signC_star (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    star (signC β g) = signC β g := by simp [signC]

def act (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    ((Fin n → A) → ℂ) →ₗ[ℂ] ((Fin n → A) → ℂ) where
  toFun v x := signC (p ∘ x) g⁻¹ * v (x ∘ g)
  map_add' u v := by ext x; simp only [Pi.add_apply, mul_add]
  map_smul' c v := by ext x; simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm,
    RingHom.id_apply]

@[simp] lemma act_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : (Fin n → A) → ℂ) (x) :
    act p g v x = signC (p ∘ x) g⁻¹ * v (x ∘ g) := rfl

lemma act_one (p : A → Bool) : act (n := n) p 1 = 1 := by
  ext v x
  simp [act]

lemma act_mul (p : A → Bool) (g h : Equiv.Perm (Fin n)) :
    act p (g*h) = act p g * act p h := by
  apply LinearMap.ext
  intro v
  funext x
  change signC (p ∘ x) (g*h)⁻¹ * v (x ∘ ⇑(g*h)) =
    signC (p ∘ x) g⁻¹ * (signC (p ∘ (x ∘ g)) h⁻¹ * v ((x ∘ g) ∘ h))
  simp only [_root_.mul_inv_rev, signC_mul]
  have he : (p ∘ x) ∘ (Equiv.symm g⁻¹) = p ∘ (x ∘ g) := rfl
  rw [he]
  have hw : x ∘ ⇑(g*h) = (x ∘ g) ∘ h := rfl
  rw [hw]
  ring

def tensorRep (p : A → Bool) (n : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) ((Fin n → A) → ℂ) where
  toFun := act p
  map_one' := act_one p
  map_mul' := act_mul p

def Invariant (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ) : Prop :=
  ∀ (g : Equiv.Perm (Fin n)) x y,
    M (x ∘ g) (y ∘ g) = signC (p ∘ x) g⁻¹ * signC (p ∘ y) g⁻¹ * M x y

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedCommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

def invariantSubspace (p : A → Bool) (n : ℕ) :
    Submodule ℂ (Matrix (Fin n → A) (Fin n → A) ℂ) where
  carrier := {M | Invariant p M}
  zero_mem' := by intro g x y; simp
  add_mem' := by
    intro M N hM hN g x y
    simp only [Matrix.add_apply, hM g x y, hN g x y, mul_add]
  smul_mem' := by
    intro c M hM g x y
    simp only [Matrix.smul_apply, smul_eq_mul, hM g x y]
    ring

abbrev RealizedType (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :=
  Set.range (wordType (A := A × A) n)

def typeRepresentative (c : RealizedType A n) : Fin n → A × A := c.property.choose

def invariantCode (p : A → Bool) (n : ℕ) :
    invariantSubspace p n →ₗ[ℂ] (RealizedType A n → ℂ) where
  toFun M c := M.val (Prod.fst ∘ typeRepresentative c) (Prod.snd ∘ typeRepresentative c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype A] in
lemma act_single_comp (p : A → Bool) (g : Equiv.Perm (Fin n)) (y : Fin n → A) :
    act p g (Pi.single (y ∘ g) (1 : ℂ)) =
      signC (p ∘ y) g⁻¹ • Pi.single y (1 : ℂ) := by
  funext x
  change signC (p ∘ x) g⁻¹ * ((Pi.single (y ∘ g) (1 : ℂ) : (Fin n → A) → ℂ) (x ∘ g)) = _
  by_cases h : x=y
  · subst x
    simp
  · have hg : x ∘ g ≠ y ∘ g := by
      intro he
      apply h
      funext i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun he (g.symm i)
    simp [h, hg]

lemma intertwiner_matrix_invariant (p : A → Bool)
    (f : Representation.IntertwiningMap (tensorRep p n) (tensorRep p n)) :
    Invariant p (LinearMap.toMatrix' f.toLinearMap) := by
  intro g x y
  have h := congrFun (Representation.IntertwiningMap.isIntertwining _ _ f g (Pi.single (y ∘ g) (1 : ℂ))) x
  change f (act p g (Pi.single (y ∘ g) 1)) x = signC (p ∘ x) g⁻¹ * f (Pi.single (y ∘ g) 1) (x ∘ g) at h
  rw [act_single_comp, map_smul] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  simp only [LinearMap.toMatrix'_apply, Representation.IntertwiningMap.toLinearMap_apply]
  have hs := signC_sq (p ∘ x) g⁻¹
  calc
    _ = (signC (p ∘ x) g⁻¹ * signC (p ∘ x) g⁻¹) * f (Pi.single (y ∘ g) 1) (x ∘ g) := by rw [hs,one_mul]
    _ = _ := by rw [mul_assoc, ← h]; ring

def commutantToInvariant (p : A → Bool) (n : ℕ) :
    Representation.IntertwiningMap (tensorRep p n) (tensorRep p n) →ₗ[ℂ]
      invariantSubspace p n where
  toFun f := ⟨LinearMap.toMatrix' f.toLinearMap, intertwiner_matrix_invariant p f⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' c f := by apply Subtype.ext; simp

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} [Fintype A] {n : ℕ}

abbrev TensorSpace (A : Type*) (n : ℕ) := EuclideanSpace ℂ (Fin n → A)

def coeffEquiv (A : Type*) [Fintype A] (n : ℕ) :
    TensorSpace A n ≃ₗ[ℂ] ((Fin n → A) → ℂ) := WithLp.linearEquiv 2 ℂ _

def wordReorder (g : Equiv.Perm (Fin n)) : (Fin n → A) ≃ (Fin n → A) where
  toFun x := x ∘ g
  invFun x := x ∘ g.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

def actHilbert (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    TensorSpace A n →ₗ[ℂ] TensorSpace A n := (coeffEquiv A n).symm.conj (act p g)

lemma actHilbert_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) (x) :
    actHilbert p g v x = signC (p ∘ x) g⁻¹ * v (x ∘ g) := rfl

lemma actHilbert_inner (p : A → Bool) (g : Equiv.Perm (Fin n)) (v w : TensorSpace A n) :
    inner ℂ (actHilbert p g v) (actHilbert p g w) = inner ℂ v w := by
  simp only [PiLp.inner_apply, actHilbert_apply, RCLike.inner_apply, map_mul,
    starRingEnd_apply, signC_star]
  have he (x : Fin n → A) : signC (p ∘ x) g⁻¹ * w (x ∘ g) *
      (signC (p ∘ x) g⁻¹ * star (v (x ∘ g))) = w (x ∘ g) * star (v (x ∘ g)) := by
    calc
      _ = (signC (p ∘ x) g⁻¹ * signC (p ∘ x) g⁻¹) *
          (w (x ∘ g) * star (v (x ∘ g))) := by ring
      _ = _ := by rw [signC_sq, one_mul]
  simp_rw [he]
  exact Equiv.sum_comp (wordReorder g) (fun x => w x * star (v x))

def actionIsometry (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    TensorSpace A n →ₗᵢ[ℂ] TensorSpace A n := (actHilbert p g).isometryOfInner (actHilbert_inner p g)

def hilbertSubspace (S : Submodule ℂ ((Fin n → A) → ℂ)) : Submodule ℂ (TensorSpace A n) :=
  S.map (coeffEquiv A n).symm.toLinearMap

lemma hilbertSubspace_map (p : A → Bool) (S : Submodule ℂ ((Fin n → A) → ℂ))
    (hS : ∀ g, S.map (act p g) = S) (g : Equiv.Perm (Fin n)) :
    (hilbertSubspace S).map (actHilbert p g) = hilbertSubspace S := by
  apply le_antisymm
  · rintro _ ⟨u,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨act p g v, ?_, ?_⟩
    · rw [← hS g]
      exact ⟨v,hv,rfl⟩
    · simp only [actHilbert, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨v,hv,rfl⟩
    have hm : v ∈ S.map (act p g) := (hS g).symm ▸ hv
    obtain ⟨w,hw,rfl⟩ := hm
    refine ⟨(coeffEquiv A n).symm w, ⟨w,hw,rfl⟩, ?_⟩
    simp only [actHilbert, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SparsePinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

def blockVec (f : I → J) (a : J) (x : I → ℂ) : I → ℂ :=
  fun i => if f i = a then x i else 0

def pinch (f : I → J) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if f i = f j then A i j else 0

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [LinearOrder I]

def subsetCode (k : ℕ) (s : Finset I) : Fin k → Option I :=
  fun i => if h : i.val < s.card then some (s.orderEmbOfFin rfl ⟨i.val,h⟩) else none

def hamming (a b : I → Bool) : ℕ := (Finset.univ.filter (fun i => a i ≠ b i)).card

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix Representation

namespace BinaryCoordinateSweeps.Signed
open Density Irrep

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

omit [DecidableEq A] in
lemma coeff_actHilbert (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    coeffEquiv A n (actHilbert p g v) = act p g (coeffEquiv A n v) := rfl

omit [DecidableEq A] in
lemma coeff_symm_act (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : (Fin n → A) → ℂ) :
    (coeffEquiv A n).symm (act p g v) = actHilbert p g ((coeffEquiv A n).symm v) := rfl

def projectionIntertwiner (p : A → Bool) (S : Submodule ℂ ((Fin n → A) → ℂ))
    (hS : ∀ g, S.map (act p g) = S) :
    IntertwiningMap (tensorRep p n) (tensorRep p n) where
  toLinearMap := (coeffEquiv A n).conj (hilbertSubspace S).starProjection.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change coeffEquiv A n ((hilbertSubspace S).starProjection ((coeffEquiv A n).symm (act p g v))) =
      act p g (coeffEquiv A n ((hilbertSubspace S).starProjection ((coeffEquiv A n).symm v)))
    rw [coeff_symm_act, ← coeff_actHilbert]
    congr 1
    exact (projectionMatrix_commutes (hilbertSubspace S) (actionIsometry p g)
      (hilbertSubspace_map p S hS g) ((coeffEquiv A n).symm v)).symm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def isotypicProjection (p : A → Bool) (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    Matrix (Fin n → A) (Fin n → A) ℂ :=
  projectionMatrix (hilbertSubspace (isotypicSpan ρ (tensorRep p n)))

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [Fintype G] [FiniteDimensional ℂ W] in
lemma commuting_eigenspace_map (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) (μ : ℂ) (g : G) :
    (T.eigenspace μ).map (σ g) = T.eigenspace μ := by
  apply le_antisymm
  · rintro w ⟨v,hv,rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hT,Module.End.mem_eigenspace_iff.mp hv,map_smul]
  · intro w hw
    refine ⟨σ g⁻¹ w, ?_, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      rw [hT,Module.End.mem_eigenspace_iff.mp hw,map_smul]
    · rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

def eigenspaceProjectionIntertwiner (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) (μ : ℂ) : IntertwiningMap σ σ where
  toLinearMap := (T.eigenspace μ).starProjection.toLinearMap
  isIntertwining' g := by
    ext w
    change (T.eigenspace μ).starProjection (σ g w) = σ g ((T.eigenspace μ).starProjection w)
    let U : W →ₗᵢ[ℂ] W := {toLinearMap := σ g, norm_map' := hσ g}
    have he := U.map_starProjection (T.eigenspace μ) w
    change σ g ((T.eigenspace μ).starProjection w) =
      ((T.eigenspace μ).map (σ g)).starProjection (σ g w) at he
    simpa only [commuting_eigenspace_map σ T hT μ g] using he.symm

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

def commutingIntertwiner (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) : IntertwiningMap σ σ where
  toLinearMap := T
  isIntertwining' g := by ext w; exact hT g w

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma commuting_isotypic_invariant (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) :
    ∀ w ∈ isotypicSpan ρ σ, T w ∈ isotypicSpan ρ σ := by
  intro w hw
  apply Submodule.iSup_induction (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap)
    (motive := fun w => T w ∈ isotypicSpan ρ σ) hw
  · intro f w hw
    obtain ⟨v,rfl⟩ := hw
    let F := (commutingIntertwiner σ T hT).comp f
    exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) F) ⟨v,rfl⟩
  · simp
  · intro x y hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_TensorProductMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I A B C : Type*} [Fintype I] [DecidableEq I]
 [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def tensorMatrices (M : I → Matrix A B ℂ) : Matrix (I → A) (I → B) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_Whitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def parityProjection (p : A → Bool) : Matrix A A ℂ :=
  Matrix.diagonal (fun a => if p a then 1 else 0)

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_MatrixIsotypicWhitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical MonoidAlgebra

namespace BinaryCoordinateSweeps.Irrep
open Representation

universe uG uW uV uI
variable {G : Type uG} [Group G] [Fintype G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ G W)

def algebraSubmoduleInclusion (m : Submodule ℂ[G] σ.asModule) :
    IntertwiningMap (Representation.ofModule (k:=ℂ) (G:=G) m) σ where
  toFun v := σ.asModuleEquiv (m.subtype (RestrictScalars.addEquiv ℂ ℂ[G] m v))
  map_add' x y := by simp
  map_smul' c v := by
    simp only [RestrictScalars.addEquiv_map_smul,algebraMap_smul,RingHom.id_apply]
    change σ.asModuleEquiv (c • (m.subtype (RestrictScalars.addEquiv ℂ ℂ[G] m v))) = _
    exact map_smul σ.asModuleEquiv c _
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change σ.asModuleEquiv (m.subtype ((RestrictScalars.addEquiv ℂ ℂ[G] m)
      (Representation.ofModule m g v))) = σ g
      (σ.asModuleEquiv (m.subtype (RestrictScalars.addEquiv ℂ ℂ[G] m v)))
    rw [← Representation.asAlgebraHom_of,Representation.ofModule_asAlgebraHom_apply_apply]
    simp only [AddEquiv.apply_symm_apply,map_smul,Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedWhitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Irrep Density Representation

variable {A V : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def hilbertTensorRep (p : A → Bool) (n : ℕ) :
    Representation ℂ (Equiv.Perm (Fin n)) (TensorSpace A n) :=
  conjugateRep (tensorRep p n) (coeffEquiv A n).symm

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicOrthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W Z : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G Z)

def adjointIntertwiner (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (hσ : ∀ g w, ‖σ g w‖=‖w‖)
    (f : IntertwiningMap ρ σ) : IntertwiningMap σ ρ where
  toLinearMap := f.toLinearMap.adjoint
  isIntertwining' g := by
    have he := congrArg LinearMap.adjoint (f.isIntertwining' g⁻¹)
    simpa only [LinearMap.adjoint_comp,unitary_rep_adjoint ρ hρ,
      unitary_rep_adjoint σ hσ,inv_inv] using he.symm

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def subrepresentationCongr (e : H ≃* G) (ρ : Representation ℂ G V) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp e.toMonoidHom) where
  toFun U := ⟨U.toSubmodule, fun h _ hv => U.apply_mem_toSubmodule (e h) hv⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (e.symm g) hv
    change ρ (e (e.symm g)) v ∈ U.toSubmodule at h
    rwa [e.apply_symm_apply] at h⟩
  left_inv U := by rfl
  right_inv U := by rfl
  map_rel_iff' := Iff.rfl

variable [Fintype G] [FiniteDimensional ℂ V]

def classCharacter (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (fun g h hgh => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
    exact (ρ.char_conj g c).symm)

omit [Fintype G] [FiniteDimensional ℂ V] in
@[simp] lemma classCharacter_mk (ρ : Representation ℂ G V) (g : G) :
    classCharacter ρ (ConjClasses.mk g) = ρ.character g := rfl

def classPairRight (f : ConjClasses G → ℂ) : (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun h := (Nat.card G : ℂ)⁻¹ * ∑ g, h (ConjClasses.mk g) * f (ConjClasses.mk g⁻¹)
  map_add' h k := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
  map_smul' a h := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (∑ g : G, a * h (ConjClasses.mk g) * f (ConjClasses.mk g⁻¹)) =
      a * ∑ g : G, h (ConjClasses.mk g) * f (ConjClasses.mk g⁻¹) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
    ring

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungDominance
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

def rowPrefix (μ : YoungDiagram) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Cell μ => row x < k)).card

def Dominates (μ ν : YoungDiagram) : Prop := ∀ k, rowPrefix ν k ≤ rowPrefix μ k

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable {μ ν : YoungDiagram}

def crossAnti (e : Cell μ ≃ Cell ν) : Module.End ℂ (Tabloid ν → ℂ) :=
  ∑ c : C μ, signC μ c.val • tabloidRepresentation ν (e.permCongr c.val)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungPartition
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instDecidableEqElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.instMulActionGElemForallCellNatTabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma card_cellsOfRowLens (w : List ℕ) : (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
    · simpa using congrArg (a + ·) ih
    · rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hy
      have hx0 := (Finset.mem_product.mp hx).1
      simp only [Finset.mem_singleton] at hx0
      have hf := congrArg Prod.fst he
      change Nat.succ y.1 = x.1 at hf
      omega

def diagram {n : ℕ} (p : n.Partition) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma diagram_card {n : ℕ} (p : n.Partition) : (diagram p).card = n := by
  change (YoungDiagram.cellsOfRowLens (p.parts.sort (· ≥ ·))).card = n
  rw [card_cellsOfRowLens, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

def cellsEquivFin {n : ℕ} (p : n.Partition) : Cell (diagram p) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa using diagram_card p)

def conjPartition {X : Type*} [Fintype X] [DecidableEq X] :
    ConjClasses (Equiv.Perm X) → (Fintype.card X).Partition :=
  Quotient.lift Equiv.Perm.partition (fun _ _ h => Equiv.Perm.partition_eq_of_isConj.mp h)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFinite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

abbrev PartitionSpace {n : ℕ} (p : n.Partition) := SpechtSpace (diagram p)

def partitionRep {n : ℕ} (p : n.Partition) :
    Representation ℂ (Equiv.Perm (Fin n)) (PartitionSpace p) :=
  (spechtRep (diagram p)).comp ((cellsEquivFin p).symm.permCongrHom.toMonoidHom)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungResolution
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

abbrev PartitionHilbert {n : ℕ} (p : n.Partition) := SpechtHilbert (diagram p)

def partitionHilbertRep {n : ℕ} (p : n.Partition) :
    Representation ℂ (Equiv.Perm (Fin n)) (PartitionHilbert p) :=
  (hilbertSpecht (diagram p)).comp (cellsEquivFin p).symm.permCongrHom.toMonoidHom

def partitionHilbertEquiv {n : ℕ} (p : n.Partition) :
    (partitionRep p).Equiv (partitionHilbertRep p) :=
  .mk (spechtHilbertEquiv (diagram p)) (by
    intro g
    apply LinearMap.ext
    intro v
    change spechtHilbertEquiv (diagram p) (spechtRep (diagram p) _ v) =
      spechtHilbertEquiv (diagram p) (spechtRep (diagram p) _
        ((spechtHilbertEquiv (diagram p)).symm (spechtHilbertEquiv (diagram p) v)))
    rw [LinearEquiv.symm_apply_apply])

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed

def pairWeight {n : ℕ} (β : Fin n → Bool) (g : Equiv.Perm (Fin n))
    (a b : Fin n) : ℤˣ :=
  if b<a ∧ β a=true ∧ β b=true then (if g a ≤ g b then -1 else 1) else 1

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_ActiveTypes
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps
open Density Irrep Representation

namespace Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

def typeProjection (p : A → Bool) (α : n.Partition) :=
  isotypicProjection p (Young.partitionHilbertRep α)

abbrev ActiveType (p : A → Bool) (n : ℕ) := {α : n.Partition // typeProjection p α≠0}

end Signed
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_PiTensorMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
  [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]

def piTensorMatrices (M : ∀ i, Matrix (A i) (B i) ℂ) :
    Matrix (∀ i, A i) (∀ i, B i) ℂ := fun x y => ∏ i, M i (x i) (y i)

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical Kronecker
open Equiv Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n m : ℕ}

def splitWord : (Fin (n+m) → A) ≃ (Fin n → A) × (Fin m → A) :=
  (finSumFinEquiv.symm.arrowCongr (Equiv.refl A)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

omit [Fintype A] [DecidableEq A] in
@[simp] lemma splitWord_fst (x : Fin (n+m) → A) (i : Fin n) :
    (splitWord x).1 i = x (i.castAdd m) := rfl
omit [Fintype A] [DecidableEq A] in
@[simp] lemma splitWord_snd (x : Fin (n+m) → A) (i : Fin m) :
    (splitWord x).2 i = x (i.natAdd n) := rfl

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

abbrev actionMatrix (p : A → Bool) (g : Equiv.Perm (Fin n)) := LinearMap.toMatrix' (act p g)

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

def signedConj (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) :=
  actionMatrix p g*M*(actionMatrix p g).conjTranspose

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical Kronecker
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A B G : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def matrixSlice (M : Matrix (A×B) (A×B) ℂ) (b c : B) : Matrix A A ℂ :=
  fun a a' => M (a,b) (a',c)

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_PiCentrality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical Kronecker
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

def siteMatrix (i : I) (P : Matrix (A i) (A i) ℂ) : Matrix (∀i,A i) (∀i,A i) ℂ :=
  (P ⊗ₖ (1 : Matrix (∀j : {j // j≠i}, A j) (∀j : {j // j≠i}, A j) ℂ)).submatrix
    (Equiv.piSplitAt i A) (Equiv.piSplitAt i A)

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicProjectionMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MonoidAlgebra
open Matrix

namespace BinaryCoordinateSweeps
open Density Irrep Representation

namespace Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def signedAverage (p : A → Bool) (w : Equiv.Perm (Fin n) → ℂ) :
    Matrix (Fin n → A) (Fin n → A) ℂ := ∑g, w g • actionMatrix p g

end Signed
end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Fourier
open Representation

variable (G : Type*) [Group G] [Fintype G]

abbrev RegularSpace := EuclideanSpace ℂ G

def regularMap (g : G) : RegularSpace G →ₗ[ℂ] RegularSpace G where
  toFun v := WithLp.toLp 2 (fun x => v (g⁻¹*x))
  map_add' v w := by ext x; rfl
  map_smul' a v := by ext x; rfl

def regular : Representation ℂ G (RegularSpace G) where
  toFun := regularMap G
  map_one' := by ext v x; simp [regularMap]
  map_mul' g h := by ext v x; simp [regularMap,mul_assoc]

omit [Fintype G] in
@[simp] lemma regular_apply (g : G) (v : RegularSpace G) (x : G) :
    regular G g v x=v (g⁻¹*x) := rfl

end BinaryCoordinateSweeps.Fourier

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_KoszulBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I : Type*} [Fintype I] [LinearOrder I] {n : I → ℕ} {N : ℕ}

def blockPerm (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : ∀i, Equiv.Perm (Fin (n i))) :
    Equiv.Perm (Fin N) := (toLex.trans e.toEquiv).permCongr (Equiv.Perm.sigmaCongrRight g)

omit [Fintype I] in
@[simp] lemma blockPerm_apply (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (i : I) (a : Fin (n i)) :
    blockPerm e g (e (toLex ⟨i,a⟩)) = e (toLex ⟨i,g i a⟩) := by
  simp [blockPerm, Equiv.permCongr_apply]

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
open Matrix Density

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}

omit [Fintype I] in
@[simp] lemma blockPerm_inv (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) : (blockPerm e g)⁻¹=blockPerm e (fun i => (g i)⁻¹) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,a⟩,rfl⟩ := (toLex.trans e.toEquiv).surjective x
  apply (blockPerm e g).injective
  change blockPerm e g ((blockPerm e g).symm (e (toLex ⟨i,a⟩))) = _
  rw [Equiv.apply_symm_apply]
  simp

def blockWords (e : (Σₗ i, Fin (n i)) ≃o Fin N) :
    (Fin N → A) ≃ (∀i, Fin (n i) → A) :=
  ((toLex.trans e.toEquiv).symm.arrowCongr (Equiv.refl A)).trans (Equiv.piCurry (fun _ _ => A))

omit [Fintype I] [Fintype A] [DecidableEq A] in
@[simp] lemma blockWords_apply (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (x : Fin N → A) (i : I) (a : Fin (n i)) : blockWords e x i a=x (e (toLex ⟨i,a⟩)) := rfl

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MonoidAlgebra
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def vacuumDensity : Matrix A A ℂ := Matrix.diagonal (fun a => if a=Classical.choice (inferInstance : Nonempty A) then 1 else 0)

abbrev LocalDensityIndex (p : A → Bool) (n : ℕ) :=
  WordType (MatchedPair p) n × (MatchedPair p → ZMod (n+1))

def localDensity (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n) : Matrix A A ℂ :=
  if n=0 then vacuumDensity else reducedPhaseDensity n (matchedEmbedding p) u.1 u.2

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_BlockTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

def blockProjection (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    Matrix (Fin N → A) (Fin N → A) ℂ :=
  (piTensorMatrices (fun i => isotypicProjection p (ρ i))).submatrix (blockWords e) (blockWords e)

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps
open Density TraceHolder Irrep Representation

namespace Signed
variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

def blockAverage (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) : Matrix (Fin N → A) (Fin N → A) ℂ :=
  ∑g : ∀i, Equiv.Perm (Fin (n i)), (∏i, w i (g i)) • actionMatrix p (blockPerm e g)

end Signed
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

def groupOf (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N)) (t : Fin N) : I :=
  (ofLex (e.symm (g⁻¹ t))).1

def groupedProjection (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :=
  signedConj p g (blockProjection e p ρ)

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_MatrixRegularize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A I : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [Nonempty I]

def meanDensity (r : I → Matrix A A ℂ) : Matrix A A ℂ :=
  (Fintype.card I : ℂ)⁻¹ • ∑ i, r i

def regularizedMean (r : I → Matrix A A ℂ) (ε : ℝ) : Matrix A A ℂ :=
  (1-ε : ℂ) • meanDensity r + (ε/(Fintype.card A) : ℂ) • 1

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open scoped Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}

def groupedAverage (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :=
  signedConj p g (blockAverage e p w)

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CoinductionTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G H V W : Type*} [Group G] [Group H]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  (φ : H →* G) (ρ : Representation ℂ G V) (σ : Representation ℂ H W)

def toCoind (f : IntertwiningMap (ρ.comp φ) σ) : IntertwiningMap ρ (coind φ σ) where
  toLinearMap := {
    toFun := fun v => ⟨fun g => f (ρ g v), by
      intro h g
      change f (ρ (φ h * g) v) = σ h (f (ρ g v))
      rw [map_mul,Module.End.mul_apply]
      exact IntertwiningMap.isIntertwining _ _ f h (ρ g v)⟩
    map_add' := by intro a b; ext g; simp only [map_add]; rfl
    map_smul' := by intro c a; ext g; simp only [map_smul]; rfl }
  isIntertwining' a := by
    ext v g
    change f (ρ g (ρ a v)) = f (ρ (g*a) v)
    rw [map_mul,Module.End.mul_apply]

def fromCoind (f : IntertwiningMap ρ (coind φ σ)) : IntertwiningMap (ρ.comp φ) σ where
  toLinearMap := {
    toFun := fun v => (f v).val 1
    map_add' := by intros; simp only [map_add]; rfl
    map_smul' := by intros; simp only [map_smul]; rfl }
  isIntertwining' h := by
    ext v
    have he := congrArg (fun u : coindV φ σ => u.val 1)
      (IntertwiningMap.isIntertwining _ _ f (φ h) v)
    change (f (ρ (φ h) v)).val 1 = σ h ((f v).val 1)
    rw [he]
    change (f v).val (1*φ h) = _
    simpa only [one_mul,mul_one] using (f v).property h 1

def coindHomEquiv : IntertwiningMap (ρ.comp φ) σ ≃ₗ[ℂ] IntertwiningMap ρ (coind φ σ) where
  toFun := toCoind φ ρ σ
  invFun := fromCoind φ ρ σ
  left_inv f := by ext v; change f (ρ 1 v) = f v; simp
  right_inv f := by
    ext v g
    change (f (ρ g v)).val 1 = (f v).val g
    rw [IntertwiningMap.isIntertwining]
    change (f v).val (1*g) = _
    rw [one_mul]
  map_add' a b := by ext v g; rfl
  map_smul' c a := by ext v g; rfl

variable [Fintype G] [Fintype H] [Module.Finite ℂ V] [Module.Finite ℂ W]

def coindEvaluation {I : Type*} (r : I → G) : coindV φ σ →ₗ[ℂ] (I → W) where
  toFun := fun f i => f.val (r i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation Equiv Equiv.Perm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

def blockPerm : Equiv.Perm A →* Equiv.Perm X :=
  e.permCongrHom.toMonoidHom.comp ((sumCongrHom A B).comp (MonoidHom.inl _ _))

omit [Fintype A] [Fintype B] [Fintype X] in
lemma blockPerm_inr (a : Equiv.Perm A) (b : B) :
    blockPerm e a (e (Sum.inr b)) = e (Sum.inr b) := by
  change e (Equiv.sumCongr a (1:Equiv.Perm B) (e.symm (e (Sum.inr b)))) = _
  rw [e.symm_apply_apply]
  rfl

omit [Fintype X] in
lemma blockPerm_of_fixed (g : Equiv.Perm X) (hg : ∀ b, g (e (Sum.inr b)) = e (Sum.inr b)) :
    ∃ a : Equiv.Perm A, blockPerm e a = g := by
  let d := e.symm.permCongr g
  have hd (b : B) : d (Sum.inr b) = Sum.inr b := by
    change e.symm (g (e (Sum.inr b))) = _
    rw [hg,e.symm_apply_apply]
  have hh : d ∈ (sumCongrHom A B).range := by
    apply mem_sumCongrHom_range_of_perm_mapsTo_inl
    apply (perm_mapsTo_inl_iff_mapsTo_inr d).mpr
    rintro y ⟨b,rfl⟩
    exact ⟨b,(hd b).symm⟩
  obtain ⟨⟨a,b⟩,hab⟩ := hh
  have hb : b = 1 := by
    ext x
    have hx := Equiv.congr_fun hab (Sum.inr x)
    rw [hd] at hx
    exact Sum.inr_injective hx
  subst b
  refine ⟨a,?_⟩
  change e.permCongr ((sumCongrHom A B) (a,1)) = g
  have he := congrArg e.permCongr hab
  simpa only [d,← Equiv.permCongr_symm,Equiv.apply_symm_apply] using he

def basePlacement : B ↪ X := ⟨fun b => e (Sum.inr b), e.injective.comp Sum.inr_injective⟩

omit [Fintype A] [Fintype X] in
lemma placement_extension (x : B ↪ X) : ∃ g : Equiv.Perm X, ∀ b, g (basePlacement e b) = x b :=
  Equiv.Perm.exists_extending_pair (basePlacement e) x (basePlacement e).injective x.injective

def placementSection (x : B ↪ X) : Equiv.Perm X := (placement_extension e x).choose

omit [Fintype A] [Fintype X] in
lemma placementSection_apply (x : B ↪ X) (b : B) :
    placementSection e x (basePlacement e b) = x b := (placement_extension e x).choose_spec b

omit [Fintype X] in
lemma placementSection_covers (g : Equiv.Perm X) :
    ∃ a : Equiv.Perm A, ∃ x : B ↪ X, g = blockPerm e a * (placementSection e x)⁻¹ := by
  let x : B ↪ X := (basePlacement e).trans g.symm.toEmbedding
  have hx : ∀ b, (g*placementSection e x) (e (Sum.inr b)) = e (Sum.inr b) := by
    intro b
    change g (placementSection e x (basePlacement e b)) = _
    rw [placementSection_apply]
    exact g.apply_symm_apply _
  obtain ⟨a,ha⟩ := blockPerm_of_fixed e (g*placementSection e x) hx
  exact ⟨a,x,by rw [ha,mul_inv_cancel_right]⟩

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungInducedMap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

def tabloidVector (ρ : Representation ℂ (G μ) V) (v : V) (t : Tabloid μ) : V :=
  ρ ((tabloidOfPerm_surjective μ t).choose) v

lemma tabloidVector_eq (ρ : Representation ℂ (G μ) V) (v : V)
    (hv : ∀ r : rowStabilizer μ, ρ r.val v = v) (g : G μ) :
    tabloidVector μ ρ v (tabloidOfPerm μ g) = ρ g v := by
  let h := (tabloidOfPerm_surjective μ (tabloidOfPerm μ g)).choose
  have hh : tabloidOfPerm μ h = tabloidOfPerm μ g :=
    (tabloidOfPerm_surjective μ (tabloidOfPerm μ g)).choose_spec
  have hr : g⁻¹ * h ∈ rowStabilizer μ := (tabloidOfPerm_eq_iff μ _ _).mp hh.symm
  have he := hv ⟨g⁻¹*h,hr⟩
  have he' := congrArg (ρ g) he
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he'
  exact he'

lemma tabloidVector_smul (ρ : Representation ℂ (G μ) V) (v : V)
    (hv : ∀ r : rowStabilizer μ, ρ r.val v = v) (g : G μ) (t : Tabloid μ) :
    tabloidVector μ ρ v (g • t) = ρ g (tabloidVector μ ρ v t) := by
  obtain ⟨h,rfl⟩ := tabloidOfPerm_surjective μ t
  rw [smul_tabloidOfPerm, tabloidVector_eq μ ρ v hv, tabloidVector_eq μ ρ v hv,
    map_mul, Module.End.mul_apply]

def fromTabloid (ρ : Representation ℂ (G μ) V) (v : V) : (Tabloid μ → ℂ) →ₗ[ℂ] V where
  toFun w := ∑ t, w t • tabloidVector μ ρ v t
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

lemma fromTabloid_basis (ρ : Representation ℂ (G μ) V) (v : V) (t : Tabloid μ) :
    fromTabloid μ ρ v (tabloidBasis μ t) = tabloidVector μ ρ v t := by
  simp [fromTabloid, tabloidBasis, Pi.single_apply]

lemma fromTabloid_intertwines (ρ : Representation ℂ (G μ) V) (v : V)
    (hv : ∀ r : rowStabilizer μ, ρ r.val v = v) (g : G μ) (w : Tabloid μ → ℂ) :
    fromTabloid μ ρ v (tabloidRepresentation μ g w) = ρ g (fromTabloid μ ρ v w) := by
  conv_lhs => rw [← sum_tabloidBasis μ w]
  rw [map_sum, map_sum]
  conv_rhs => rw [← sum_tabloidBasis μ w]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [map_smul, rep_basis, fromTabloid_basis, tabloidVector_smul μ ρ v hv]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookWord
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Equiv Equiv.Perm

namespace BinaryCoordinateSweeps.Young

def InHook (μ : YoungDiagram) (p : ℕ) : Prop :=
  ∀ x : Cell μ, row x < p ∨ col x < p

variable {μ : YoungDiagram} {p : ℕ}

def hookLabel (h : InHook μ p) (x : Cell μ) : Bool × Fin p :=
  if hr : row x < p then (false, ⟨row x,hr⟩)
  else (true, ⟨col x,(h x).resolve_left hr⟩)

variable {n : ℕ}
def hookWord (h : InHook μ p) (e : Cell μ ≃ Fin n) : Fin n → Bool × Fin p :=
  hookLabel h ∘ e.symm

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Representation

namespace BinaryCoordinateSweeps.Young
variable {μ : YoungDiagram} {p n : ℕ}

instance rowStabilizer_fintype (μ : YoungDiagram) : Fintype (rowStabilizer μ) := Fintype.ofFinite _

def hookRep (e : Cell μ ≃ Fin n) (p : ℕ) :
    Representation ℂ (G μ) ((Fin n → Bool × Fin p) → ℂ) :=
  (Signed.tensorRep Prod.fst n).comp e.permCongrHom.toMonoidHom

def hookRowVector (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    (Fin n → Bool × Fin p) → ℂ :=
  ∑ r : rowStabilizer μ, hookRep e p r.val (Pi.single (hookWord h e) 1)

lemma hookRowVector_fixed (h : InHook μ p) (e : Cell μ ≃ Fin n) (r : rowStabilizer μ) :
    hookRep e p r.val (hookRowVector h e) = hookRowVector h e := by
  rw [hookRowVector,map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft r) (fun t : rowStabilizer μ =>
    hookRep e p t.val (Pi.single (hookWord h e) 1))

def hookMap (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    IntertwiningMap (spechtRep μ) (hookRep e p) where
  toLinearMap := (fromTabloid μ (hookRep e p) (hookRowVector h e)).comp (spechtInclude μ)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, spechtInclude_rep]
    exact fromTabloid_intertwines μ _ _ (hookRowVector_fixed h e) g (spechtInclude μ v)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookCut
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

variable (μ : YoungDiagram) (p : ℕ)

def hookPart : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1 < p ∨ x.2 < p)
  isLowerSet := by
    intro y x hxy hx
    rcases Finset.mem_filter.mp hx with ⟨hx,hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨μ.isLowerSet hxy hx, ?_⟩
    rcases hp with hp | hp
    · exact Or.inl (lt_of_le_of_lt hxy.1 hp)
    · exact Or.inr (lt_of_le_of_lt hxy.2 hp)

def shiftCell (x : ℕ × ℕ) : ℕ × ℕ := (x.1+p,x.2+p)

lemma shiftCell_injective : Function.Injective (shiftCell p) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> simp_all [shiftCell]

def southeast : YoungDiagram where
  cells := μ.cells.preimage (shiftCell p) (shiftCell_injective p).injOn
  isLowerSet := by
    intro y x hxy hx
    apply Finset.mem_preimage.mpr
    apply μ.isLowerSet _ (Finset.mem_preimage.mp hx)
    exact ⟨Nat.add_le_add_right hxy.1 _, Nat.add_le_add_right hxy.2 _⟩

@[simp] lemma mem_hookPart (x : ℕ × ℕ) :
    x ∈ hookPart μ p ↔ x ∈ μ ∧ (x.1 < p ∨ x.2 < p) := by
  change x ∈ μ.cells.filter (fun x => x.1 < p ∨ x.2 < p) ↔
    x ∈ μ.cells ∧ (x.1 < p ∨ x.2 < p)
  exact Finset.mem_filter

@[simp] lemma mem_southeast (x : ℕ × ℕ) :
    x ∈ southeast μ p ↔ (x.1+p,x.2+p) ∈ μ := by
  change x ∈ μ.cells.preimage (shiftCell p) (shiftCell_injective p).injOn ↔ shiftCell p x ∈ μ.cells
  exact Finset.mem_preimage

lemma hookPart_inHook : InHook (hookPart μ p) p := by
  intro x
  exact ((mem_hookPart μ p x.val).mp x.property).2

def hookIn : Cell (hookPart μ p) ↪ Cell μ where
  toFun x := ⟨x.val, ((mem_hookPart μ p x.val).mp x.property).1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : Cell μ => a.val) h)

def southeastIn : Cell (southeast μ p) ↪ Cell μ where
  toFun x := ⟨(x.val.1+p,x.val.2+p), (mem_southeast μ p x.val).mp x.property⟩
  inj' _ _ h := Subtype.ext ((shiftCell_injective p) (congrArg Subtype.val h))

@[simp] lemma row_hookIn (x : Cell (hookPart μ p)) : row (hookIn μ p x) = row x := rfl
@[simp] lemma col_hookIn (x : Cell (hookPart μ p)) : col (hookIn μ p x) = col x := rfl
@[simp] lemma row_southeastIn (x : Cell (southeast μ p)) : row (southeastIn μ p x) = row x+p := rfl
@[simp] lemma col_southeastIn (x : Cell (southeast μ p)) : col (southeastIn μ p x) = col x+p := rfl

def cutEquiv : Cell (hookPart μ p) ⊕ Cell (southeast μ p) ≃ Cell μ where
  toFun := Sum.elim (hookIn μ p) (southeastIn μ p)
  invFun x := if h : row x < p ∨ col x < p then
    Sum.inl ⟨x.val,(mem_hookPart μ p x.val).mpr ⟨x.property,h⟩⟩
    else Sum.inr ⟨(row x-p,col x-p), (mem_southeast μ p _).mpr (by
      have hr : p ≤ row x := by omega
      have hc : p ≤ col x := by omega
      change (row x-p+p,col x-p+p) ∈ μ
      rw [Nat.sub_add_cancel hr,Nat.sub_add_cancel hc]
      exact x.property)⟩
  left_inv := by
    intro x
    cases x with
    | inl x =>
      dsimp only [Sum.elim]
      split_ifs with h
      · rfl
      · exact (h (hookPart_inHook μ p x)).elim
    | inr x =>
      dsimp only [Sum.elim]
      split_ifs with h
      · have h' : row x+p<p ∨ col x+p<p := h
        omega
      · apply congrArg Sum.inr
        apply Subtype.ext
        change (row x+p-p,col x+p-p) = x.val
        simp [row,col]
  right_inv := by
    intro x
    dsimp
    split_ifs with h
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · change row x-p+p = row x
        omega
      · change col x-p+p = col x
        omega

@[simp] lemma cutEquiv_inl (x : Cell (hookPart μ p)) :
    cutEquiv μ p (Sum.inl x) = hookIn μ p x := rfl
@[simp] lemma cutEquiv_inr (x : Cell (southeast μ p)) :
    cutEquiv μ p (Sum.inr x) = southeastIn μ p x := rfl

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Equiv Equiv.Perm

variable (μ : YoungDiagram) (p : ℕ)

def cutPerm : (G (hookPart μ p) × G (southeast μ p)) →* G μ :=
  (cutEquiv μ p).permCongrHom.toMonoidHom.comp (sumCongrHom _ _)

lemma cutPerm_apply_hook (g : G (hookPart μ p) × G (southeast μ p))
    (x : Cell (hookPart μ p)) :
    cutPerm μ p g (hookIn μ p x) = hookIn μ p (g.1 x) := by
  change (cutEquiv μ p) ((Equiv.sumCongr g.1 g.2) ((cutEquiv μ p).symm (cutEquiv μ p (Sum.inl x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma cutPerm_apply_southeast (g : G (hookPart μ p) × G (southeast μ p))
    (x : Cell (southeast μ p)) :
    cutPerm μ p g (southeastIn μ p x) = southeastIn μ p (g.2 x) := by
  change (cutEquiv μ p) ((Equiv.sumCongr g.1 g.2) ((cutEquiv μ p).symm (cutEquiv μ p (Sum.inr x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma cutPerm_injective : Function.Injective (cutPerm μ p) :=
  (cutEquiv μ p).permCongr.injective.comp sumCongrHom_injective

def glueLabels (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) (x : Cell μ) : ℕ :=
  Sum.elim (fun a => t.1.val a) (fun a => t.2.val a+p) ((cutEquiv μ p).symm x)

@[simp] lemma glueLabels_hook (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p))
    (x : Cell (hookPart μ p)) : glueLabels μ p t (hookIn μ p x) = t.1.val x := by
  change Sum.elim _ _ ((cutEquiv μ p).symm ((cutEquiv μ p) (Sum.inl x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma glueLabels_southeast (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p))
    (x : Cell (southeast μ p)) : glueLabels μ p t (southeastIn μ p x) = t.2.val x+p := by
  change Sum.elim _ _ ((cutEquiv μ p).symm ((cutEquiv μ p) (Sum.inr x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma labels_cutPerm (g : G (hookPart μ p) × G (southeast μ p)) :
    labels μ (cutPerm μ p g) =
      glueLabels μ p (tabloidOfPerm (hookPart μ p) g.1,tabloidOfPerm (southeast μ p) g.2) := by
  funext x
  obtain ⟨y,rfl⟩ := (cutEquiv μ p).surjective x
  cases y with
  | inl y =>
    simp only [labels,← map_inv,cutEquiv_inl,cutPerm_apply_hook,row_hookIn,glueLabels_hook]
    rfl
  | inr y =>
    simp only [labels,← map_inv,cutEquiv_inr,cutPerm_apply_southeast,row_southeastIn,glueLabels_southeast]
    rfl

def glueTabloid (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) : Tabloid μ := by
  refine ⟨glueLabels μ p t, ?_⟩
  obtain ⟨g,hg⟩ := tabloidOfPerm_surjective (hookPart μ p) t.1
  obtain ⟨d,hd⟩ := tabloidOfPerm_surjective (southeast μ p) t.2
  refine ⟨cutPerm μ p (g,d),?_⟩
  rw [labels_cutPerm,hg,hd]

@[simp] lemma glueTabloid_val (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    (glueTabloid μ p t).val = glueLabels μ p t := rfl

lemma glueTabloid_perm (g : G (hookPart μ p) × G (southeast μ p)) :
    glueTabloid μ p (tabloidOfPerm (hookPart μ p) g.1,tabloidOfPerm (southeast μ p) g.2) =
      tabloidOfPerm μ (cutPerm μ p g) := by
  apply Subtype.ext
  exact (labels_cutPerm μ p g).symm

lemma glueTabloid_smul (g : G (hookPart μ p) × G (southeast μ p))
    (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    glueTabloid μ p (g.1 • t.1,g.2 • t.2) = cutPerm μ p g • glueTabloid μ p t := by
  obtain ⟨a,ha⟩ := tabloidOfPerm_surjective (hookPart μ p) t.1
  obtain ⟨b,hb⟩ := tabloidOfPerm_surjective (southeast μ p) t.2
  have ht : t = (tabloidOfPerm (hookPart μ p) a,tabloidOfPerm (southeast μ p) b) :=
    Prod.ext ha.symm hb.symm
  rw [ht]
  dsimp only
  rw [smul_tabloidOfPerm,smul_tabloidOfPerm,glueTabloid_perm μ p (g.1*a,g.2*b),
    glueTabloid_perm μ p (a,b),smul_tabloidOfPerm]
  congr 1
  exact map_mul (cutPerm μ p) g (a,b)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CutColumns
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

section
open Equiv Equiv.Perm

variable (μ : YoungDiagram) (p : ℕ)

lemma cutPerm_mem_column_iff (g : G (hookPart μ p) × G (southeast μ p)) :
    cutPerm μ p g ∈ C μ ↔ g.1 ∈ C (hookPart μ p) ∧ g.2 ∈ C (southeast μ p) := by
  constructor
  · intro h
    constructor
    · intro x
      simpa only [cutPerm_apply_hook,col_hookIn] using h (hookIn μ p x)
    · intro x
      simpa only [cutPerm_apply_southeast,col_southeastIn,Nat.add_right_cancel_iff] using
        h (southeastIn μ p x)
  · rintro ⟨h1,h2⟩ x
    obtain ⟨y,rfl⟩ := (cutEquiv μ p).surjective x
    cases y with
    | inl y => simpa only [cutEquiv_inl,cutPerm_apply_hook,col_hookIn] using h1 y
    | inr y => simpa only [cutEquiv_inr,cutPerm_apply_southeast,col_southeastIn] using
        congrArg (fun k : ℕ => k+p) (h2 y)

def cutColumns : C (hookPart μ p) × C (southeast μ p) ↪ C μ where
  toFun g := ⟨cutPerm μ p (g.1.val,g.2.val), (cutPerm_mem_column_iff μ p _).mpr ⟨g.1.property,g.2.property⟩⟩
  inj' a b h := by
    have hh := cutPerm_injective μ p (congrArg (fun c : C μ => c.val) h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))

end

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CutTensor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Young

variable (μ : YoungDiagram) (p : ℕ)

abbrev CutTensor := SpechtSpace (hookPart μ p) ⊗[ℂ] SpechtSpace (southeast μ p)
abbrev CutTabloids := Tabloid (hookPart μ p) × Tabloid (southeast μ p)

def cutTensorInclude : CutTensor μ p →ₗ[ℂ] (CutTabloids μ p → ℂ) :=
  TensorProduct.lift {
    toFun := fun v => {
      toFun := fun w t => spechtInclude (hookPart μ p) v t.1 * spechtInclude (southeast μ p) w t.2
      map_add' := by intro a b; ext t; simp only [map_add,Pi.add_apply,mul_add]
      map_smul' := by intro c a; ext t; simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
    map_add' := by intro a b; ext w t; simp only [map_add,Pi.add_apply,add_mul,LinearMap.add_apply,LinearMap.coe_mk,AddHom.coe_mk]
    map_smul' := by intro c a; ext w t; simp only [map_smul,Pi.smul_apply,smul_eq_mul,LinearMap.smul_apply,LinearMap.coe_mk,AddHom.coe_mk,RingHom.id_apply]; ring }

@[simp] lemma cutTensorInclude_tmul (v : SpechtSpace (hookPart μ p))
    (w : SpechtSpace (southeast μ p)) (t : CutTabloids μ p) :
    cutTensorInclude μ p (v ⊗ₜ[ℂ] w) t =
      spechtInclude (hookPart μ p) v t.1 * spechtInclude (southeast μ p) w t.2 := rfl

def cutRestriction : SpechtSpace μ →ₗ[ℂ] (CutTabloids μ p → ℂ) where
  toFun v t := spechtInclude μ v (glueTabloid μ p t)
  map_add' a b := by ext t; simp
  map_smul' c a := by ext t; simp

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W P : Type*} [Group G] [Fintype G]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid P] [Module ℂ P]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G P)

def averageLinear (l : P →ₗ[ℂ] V) : P →ₗ[ℂ] V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g⁻¹).comp (l.comp (τ g))

lemma averageLinear_apply (l : P →ₗ[ℂ] V) (v : P) :
    averageLinear ρ τ l v = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g⁻¹ (l (τ g v)) := by
  simp only [averageLinear,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply]

lemma averageLinear_intertwines (l : P →ₗ[ℂ] V) (a : G) (v : P) :
    averageLinear ρ τ l (τ a v) = ρ a (averageLinear ρ τ l v) := by
  simp only [averageLinear_apply,map_smul,map_sum,← Module.End.mul_apply,← map_mul]
  congr 1
  have hh := Equiv.sum_comp (Equiv.mulRight a) (fun g : G =>
    ρ (a*g⁻¹) (l (τ g v)))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.coe_mulRight,mul_inv_rev,mul_inv_cancel_left]

def averagedIntertwiner (l : P →ₗ[ℂ] V) : IntertwiningMap τ ρ where
  toLinearMap := averageLinear ρ τ l
  isIntertwining' a := LinearMap.ext (averageLinear_intertwines ρ τ l a)

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CutBranching
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinaryCoordinateSweeps.Young

section

open scoped BigOperators Classical TensorProduct

open Representation

variable (μ : YoungDiagram) (p : ℕ)

abbrev CutGroup := G (hookPart μ p) × G (southeast μ p)

def cutSpechtRep : Representation ℂ (CutGroup μ p) (CutTensor μ p) :=
  Representation.tprod ((spechtRep (hookPart μ p)).comp (MonoidHom.fst _ _))
    ((spechtRep (southeast μ p)).comp (MonoidHom.snd _ _))

lemma cutSpechtRep_tmul (g : CutGroup μ p) (v : SpechtSpace (hookPart μ p))
    (w : SpechtSpace (southeast μ p)) :
    cutSpechtRep μ p g (v ⊗ₜ[ℂ] w) =
      spechtRep (hookPart μ p) g.1 v ⊗ₜ[ℂ] spechtRep (southeast μ p) g.2 w := rfl

def cutTabloidRep : Representation ℂ (CutGroup μ p) (CutTabloids μ p → ℂ) where
  toFun g := {
    toFun := fun v t => v (g.1⁻¹ • t.1, g.2⁻¹ • t.2)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext v t; simp
  map_mul' g d := by ext v t; simp [mul_smul]

lemma cutRestriction_rep (g : CutGroup μ p) (v : SpechtSpace μ) :
    cutRestriction μ p (spechtRep μ (cutPerm μ p g) v) =
      cutTabloidRep μ p g (cutRestriction μ p v) := by
  ext t
  change spechtInclude μ (spechtRep μ (cutPerm μ p g) v) (glueTabloid μ p t) =
    spechtInclude μ v (glueTabloid μ p (g.1⁻¹ • t.1,g.2⁻¹ • t.2))
  rw [spechtInclude_rep,tabloidRepresentation_apply,← map_inv,← glueTabloid_smul]
  rfl

lemma cutTensorInclude_rep (g : CutGroup μ p) (v : CutTensor μ p) :
    cutTensorInclude μ p (cutSpechtRep μ p g v) =
      cutTabloidRep μ p g (cutTensorInclude μ p v) := by
  induction v using OAI.tensorInductionOn with
  | tmul v w =>
    ext t
    rw [cutSpechtRep_tmul,cutTensorInclude_tmul,spechtInclude_rep,spechtInclude_rep]
    rfl
  | add u v hu hv => simp only [map_add,hu,hv]

def cutRestrictionIntertwiner : IntertwiningMap
    ((spechtRep μ).comp (cutPerm μ p)) (cutTabloidRep μ p) where
  toLinearMap := cutRestriction μ p
  isIntertwining' g := LinearMap.ext (cutRestriction_rep μ p g)

def cutTensorIntertwiner : IntertwiningMap (cutSpechtRep μ p) (cutTabloidRep μ p) where
  toLinearMap := cutTensorInclude μ p
  isIntertwining' g := LinearMap.ext (cutTensorInclude_rep μ p g)

def hookPerm : G (hookPart μ p) →* G μ :=
  (cutPerm μ p).comp (MonoidHom.inl _ _)

def hookRestriction : Representation ℂ (G (hookPart μ p)) (SpechtSpace μ) :=
  (spechtRep μ).comp (hookPerm μ p)

def cutSlice (l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p)))
    (w : SpechtSpace (southeast μ p)) :
    IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p) where
  toLinearMap := {
    toFun := fun v => l (v ⊗ₜ[ℂ] w)
    map_add' := by intro a b; rw [TensorProduct.add_tmul,map_add]
    map_smul' := by intro c a; rw [← TensorProduct.smul_tmul',map_smul]; rfl }
  isIntertwining' g := by
    ext v
    have hh := IntertwiningMap.isIntertwining _ _ l (g,1) (v ⊗ₜ[ℂ] w)
    rw [cutSpechtRep_tmul,map_one,Module.End.one_apply] at hh
    exact hh

def cutSliceMap (l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p))) :
    SpechtSpace (southeast μ p) →ₗ[ℂ]
      IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p) where
  toFun := cutSlice μ p l
  map_add' a b := by ext v; exact (congrArg l (TensorProduct.tmul_add _ _ _)).trans (map_add l _ _)
  map_smul' c a := by ext v; exact (congrArg l (TensorProduct.tmul_smul c v a)).trans (map_smul l _ _)

end

open scoped BigOperators Classical

open Representation

variable (μ : YoungDiagram) (p : ℕ)

abbrev HookInducedSpace := coindV (hookPerm μ p) (spechtRep (hookPart μ p))

def hookInducedRep : Representation ℂ (G μ) (HookInducedSpace μ p) :=
  coind (hookPerm μ p) (spechtRep (hookPart μ p))

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (z : ℝ)

def conditionalGroupLaw (a : Equiv.Perm (FreeSlot H 0)) : ℝ :=
  ∑ g : ConditionalChoices H, if remainingPerm H g.val g.property=a then
    conditionalChoiceWeight H z g else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CoindFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep

section
open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [AddCommMonoid W] [Module ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

def cosetEquiv : H × I ≃ G := Equiv.ofBijective _ hc

lemma cosetEquiv_symm_mul (h : H) (g : G) :
    (cosetEquiv φ r hc).symm (φ h * g) =
      (h * ((cosetEquiv φ r hc).symm g).1, ((cosetEquiv φ r hc).symm g).2) := by
  apply (cosetEquiv φ r hc).injective
  rw [Equiv.apply_symm_apply]
  change φ h * g = φ (h * _) * r _
  rw [map_mul,mul_assoc]
  exact congrArg (fun a => φ h*a) ((cosetEquiv φ r hc).apply_symm_apply g).symm

lemma cosetEquiv_symm_rep (i : I) : (cosetEquiv φ r hc).symm (r i) = (1,i) := by
  apply (cosetEquiv φ r hc).injective
  simp only [Equiv.apply_symm_apply, cosetEquiv, Equiv.ofBijective_apply]
  simp

def coindFiberInverse (v : I → W) : coindV φ σ :=
  ⟨fun g => σ ((cosetEquiv φ r hc).symm g).1 (v ((cosetEquiv φ r hc).symm g).2), by
    intro h g
    dsimp only
    rw [cosetEquiv_symm_mul]
    simp only [map_mul,Module.End.mul_apply]⟩

def coindFiberEquiv : coindV φ σ ≃ₗ[ℂ] (I → W) where
  toFun := coindEvaluation φ σ r
  invFun := coindFiberInverse φ σ r hc
  left_inv f := by
    ext g
    change σ _ (f.val (r _)) = f.val g
    rw [← f.property]
    exact congrArg f.val ((cosetEquiv φ r hc).apply_symm_apply g)
  right_inv v := by
    funext i
    change σ _ (v _) = v i
    rw [cosetEquiv_symm_rep]
    simp
  map_add' := (coindEvaluation φ σ r).map_add
  map_smul' := (coindEvaluation φ σ r).map_smul

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

omit [Fintype X] in
lemma placement_cosets_bijective : Function.Bijective
    (fun u : Equiv.Perm A × (B ↪ X) => blockPerm e u.1 * (placementSection e u.2)⁻¹) := by
  constructor
  · rintro ⟨a,x⟩ ⟨b,y⟩ h
    have hxy : x = y := by
      ext k
      have he := Equiv.congr_fun (congrArg (fun g : Equiv.Perm X => g⁻¹) h)
        (basePlacement e k)
      simp only [mul_inv_rev,inv_inv,Equiv.Perm.mul_apply] at he
      have ha : (blockPerm e a)⁻¹ (basePlacement e k) = basePlacement e k := by
        rw [← map_inv]; exact blockPerm_inr e a⁻¹ k
      have hb : (blockPerm e b)⁻¹ (basePlacement e k) = basePlacement e k := by
        rw [← map_inv]; exact blockPerm_inr e b⁻¹ k
      simpa only [ha,hb,placementSection_apply] using he
    subst y
    have hab : blockPerm e a = blockPerm e b := mul_right_cancel h
    have hh : a = b := by
      ext k
      have hk := Equiv.congr_fun hab (e (Sum.inl k))
      change e (Equiv.sumCongr a 1 (e.symm (e (Sum.inl k)))) =
        e (Equiv.sumCongr b 1 (e.symm (e (Sum.inl k)))) at hk
      simpa only [e.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.inl.injEq] using e.injective hk
    simp only [hh]
  · intro g
    obtain ⟨a,x,h⟩ := placementSection_covers e g
    exact ⟨(a,x),h.symm⟩

end

open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [Fintype I] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

omit [Fintype I] in
lemma cosetIndex_mul (a b : G) (i : I) :
    ((cosetEquiv φ r hc).symm (r i*(a*b))).2 =
      ((cosetEquiv φ r hc).symm
        (r ((cosetEquiv φ r hc).symm (r i*a)).2 * b)).2 := by
  have he := (cosetEquiv φ r hc).apply_symm_apply (r i*a)
  change φ _ * r _ = r i*a at he
  conv_lhs => rw [← mul_assoc,← he,mul_assoc,cosetEquiv_symm_mul]

def cosetIndexAction (a : G) : I ≃ I where
  toFun i := ((cosetEquiv φ r hc).symm (r i*a)).2
  invFun i := ((cosetEquiv φ r hc).symm (r i*a⁻¹)).2
  left_inv i := by dsimp only; rw [← cosetIndex_mul,mul_inv_cancel,mul_one,cosetEquiv_symm_rep]
  right_inv i := by dsimp only; rw [← cosetIndex_mul,inv_mul_cancel,mul_one,cosetEquiv_symm_rep]

abbrev CoindHilbertSpace := PiLp 2 (fun _ : I => W)

def coindHilbertEquiv : coindV φ σ ≃ₗ[ℂ] CoindHilbertSpace (I := I) (W := W) :=
  (coindFiberEquiv φ σ r hc).trans (WithLp.linearEquiv 2 ℂ (I → W)).symm

def coindHilbertRep : Representation ℂ G (CoindHilbertSpace (I := I) (W := W)) where
  toFun g := (coindHilbertEquiv φ σ r hc).conj (coind φ σ g)
  map_one' := by rw [map_one]; exact (coindHilbertEquiv φ σ r hc).conjRingEquiv.map_one
  map_mul' a b := by rw [map_mul]; exact (coindHilbertEquiv φ σ r hc).conjRingEquiv.map_mul _ _

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W V' W' : Type*} [Group G]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid V'] [Module ℂ V'] [AddCommMonoid W'] [Module ℂ W']
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}

def homCongr (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    IntertwiningMap ρ σ ≃ₗ[ℂ] IntertwiningMap ρ' σ' where
  toFun a := f.toIntertwiningMap.comp (a.comp e.symm.toIntertwiningMap)
  invFun a := f.symm.toIntertwiningMap.comp (a.comp e.toIntertwiningMap)
  left_inv a := by
    ext v
    change f.symm (f (a (e.symm (e v)))) = a v
    rw [Representation.Equiv.symm_apply_apply,Representation.Equiv.symm_apply_apply]
  right_inv a := by
    ext v
    change f (f.symm (a (e (e.symm v)))) = a v
    rw [Representation.Equiv.apply_symm_apply,Representation.Equiv.apply_symm_apply]
  map_add' a b := by
    ext v
    change f (a (e.symm v) + b (e.symm v)) = _
    rw [map_add]
    rfl
  map_smul' c a := by
    ext v
    change f (c • a (e.symm v)) = _
    rw [map_smul]
    rfl

def repEquiv_comp {H : Type*} [Group H] (e : ρ.Equiv ρ') (φ : H →* G) :
    Representation.Equiv (ρ.comp φ) (ρ'.comp φ) :=
  .mk e.toLinearEquiv (fun h => e.isIntertwining' (φ h))

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookInducedMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [Fintype I] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

def fiberInclude (i : I) : W →ₗ[ℂ] CoindHilbertSpace (I := I) (W := W) :=
  (WithLp.linearEquiv 2 ℂ (I → W)).symm.toLinearMap.comp (LinearMap.single ℂ (fun _ : I => W) i)

def fiberProject (i : I) : CoindHilbertSpace (I := I) (W := W) →ₗ[ℂ] W :=
  (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℂ (I → W)).toLinearMap

def hilbertBlock (A : CoindHilbertSpace (I := I) (W := W) →ₗ[ℂ]
    CoindHilbertSpace (I := I) (W := W)) (i j : I) : W →ₗ[ℂ] W :=
  (fiberProject i).comp (A.comp (fiberInclude j))

omit [Fintype I] in
lemma fiberInclude_apply (i j : I) (w : W) : fiberInclude i w j = if j=i then w else 0 := by
  simp [fiberInclude,eq_comm]

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_PlacementBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation Equiv Equiv.Perm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

abbrev PlacementComplement (x : B ↪ X) := {u : X // u ∉ Set.range x}

def placementComplementEquiv (x : B ↪ X) : A ≃ PlacementComplement x where
  toFun a := ⟨placementSection e x (e (Sum.inl a)), by
    rintro ⟨b,hb⟩
    have he := (placementSection e x).injective ((placementSection_apply e x b).trans hb)
    exact Sum.inl_ne_inr (e.injective he).symm⟩
  invFun u := (e.symm ((placementSection e x)⁻¹ u.val)).getLeft (by
    cases h : e.symm ((placementSection e x)⁻¹ u.val) with
    | inl _ => rfl
    | inr b =>
      exfalso
      apply u.property
      refine ⟨b,?_⟩
      have hh := congrArg (fun t => placementSection e x (e t)) h
      simpa only [e.apply_symm_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,
        show placementSection e x (e (Sum.inr b)) = x b from placementSection_apply e x b] using hh.symm)
  left_inv a := by
    simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply,e.symm_apply_apply,Sum.getLeft_inl]
  right_inv u := by
    apply Subtype.ext
    have hl : (e.symm ((placementSection e x)⁻¹ u.val)).isLeft := by
      cases h : e.symm ((placementSection e x)⁻¹ u.val) with
      | inl _ => rfl
      | inr b =>
        exfalso
        apply u.property
        refine ⟨b,?_⟩
        have hh := congrArg (fun t => placementSection e x (e t)) h
        simpa only [e.apply_symm_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,
        show placementSection e x (e (Sum.inr b)) = x b from placementSection_apply e x b] using hh.symm
    change placementSection e x (e (Sum.inl ((e.symm ((placementSection e x)⁻¹ u.val)).getLeft _))) = u.val
    rw [show Sum.inl ((e.symm ((placementSection e x)⁻¹ u.val)).getLeft hl) =
      e.symm ((placementSection e x)⁻¹ u.val) from Sum.inl_getLeft _ hl]
    simp

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ComplementBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X]

def complementMap (f : X ≃ Y) (x : B ↪ X) (y : B ↪ Y)
    (hf : x.trans f.toEmbedding=y) : PlacementComplement x ≃ PlacementComplement y where
  toFun u := ⟨f u.val,by
    rintro ⟨b,hb⟩
    apply u.property
    refine ⟨b,f.injective ?_⟩
    exact (congrArg (fun y : B ↪ Y => y b) hf).trans hb⟩
  invFun u := ⟨f.symm u.val,by
    rintro ⟨b,hb⟩
    apply u.property
    refine ⟨b,?_⟩
    exact (congrArg (fun y : B ↪ Y => y b) hf).symm.trans
      ((congrArg f hb).trans (f.apply_symm_apply _))⟩
  left_inv u := Subtype.ext (f.symm_apply_apply _)
  right_inv u := Subtype.ext (f.apply_symm_apply _)

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h h' : ℕ} {bits : Fin b → ℕ}
variable {H : PathFamily bits h} {H' : PathFamily bits h'}

def PathExtension.restrictChoice (E : PathExtension H H')
    (g : ConditionalChoices H') : ConditionalChoices H :=
  ⟨g.val,E.pathEvent_mono g.property⟩

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_Trajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma trajectory_coordinates {b : ℕ} {bits : Fin b → ℕ}
    (x : Fin (b+1) → GridSlot bits)
    (hmov : ∀ (j : Fin b) (i : Fin b), i ≠ j → x j.succ i = x j.castSucc i)
    (t : Fin (b+1)) (i : Fin b) :
    x t i = if i.val < t.val then x (Fin.last b) i else x 0 i := by
  have hbefore : ∀ t : Fin (b+1), t.val ≤ i.val → x t i = x 0 i := by
    intro t
    induction t using Fin.induction with
    | zero => intro _; rfl
    | succ j ih =>
      intro ht
      have hij : i ≠ j := by intro h; subst j; simp at ht
      rw [hmov j i hij, ih]
      exact Nat.le_trans (Nat.le_succ j.val) ht
  have hafter : ∀ t : Fin (b+1), i.val < t.val → x t i = x (Fin.last b) i := by
    intro t
    induction t using Fin.reverseInduction with
    | last => intro _; rfl
    | cast j ih =>
      intro ht
      have hij : i ≠ j := by intro h; subst j; simp at ht
      rw [← hmov j i hij, ih]
      exact Nat.lt_succ_of_lt ht
  split_ifs with h
  · exact hafter t h
  · exact hbefore t (Nat.le_of_not_lt h)

lemma trajectory_unique {b : ℕ} {bits : Fin b → ℕ}
    (x y : Fin (b+1) → GridSlot bits)
    (hx : ∀ (j i : Fin b), i ≠ j → x j.succ i = x j.castSucc i)
    (hy : ∀ (j i : Fin b), i ≠ j → y j.succ i = y j.castSucc i)
    (h0 : x 0 = y 0) (hb : x (Fin.last b) = y (Fin.last b)) : x = y := by
  funext t i
  rw [trajectory_coordinates x hx, trajectory_coordinates y hy, h0, hb]

def gridPartialSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits)
    (t : Fin (b+1)) : Equiv.Perm (GridSlot bits) :=
  ((List.ofFn (gridLayer bits g)).take t.val).reverse.prod

@[simp] lemma gridPartialSweep_zero {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    gridPartialSweep bits g 0 = 1 := by simp [gridPartialSweep]

@[simp] lemma gridPartialSweep_last {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    gridPartialSweep bits g (Fin.last b) = gridSweep bits g := by
  unfold gridPartialSweep gridSweep
  rw [List.take_of_length_le (by simp)]

lemma gridPartialSweep_succ {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    gridPartialSweep bits g j.succ = gridLayer bits g j * gridPartialSweep bits g j.castSucc := by
  unfold gridPartialSweep
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp only [List.reverse_append, List.reverse_singleton, List.prod_append,
    List.prod_singleton, List.getElem_ofFn, Fin.eta]

lemma gridLayer_other {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits)
    (j i : Fin b) (hi : i ≠ j) (x : GridSlot bits) : gridLayer bits g j x i = x i := by
  simp [gridLayer, Equiv.piSplitAt, hi]

lemma gridPartialSweep_changes {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits)
    (x : GridSlot bits) (j i : Fin b) (hi : i ≠ j) :
    gridPartialSweep bits g j.succ x i = gridPartialSweep bits g j.castSucc x i := by
  rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, gridLayer_other bits g j i hi]

lemma gridPartialSweep_path {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (g : GridChoices bits) (hg : pathEvent H g)
    (t : Fin (b+1)) (i : Fin h) :
    gridPartialSweep bits g t (H.position 0 i) = H.position t i := by
  induction t using Fin.induction with
  | zero => simp
  | succ j ih => rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, ih, hg j i]

lemma pathEvent_of_endpoints {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (g : GridChoices bits)
    (he : ∀ i, gridSweep bits g (H.position 0 i) = H.position (Fin.last b) i) :
    pathEvent H g := by
  have hx (i : Fin h) : (fun t => gridPartialSweep bits g t (H.position 0 i)) =
      (fun t => H.position t i) := by
    apply trajectory_unique
    · exact gridPartialSweep_changes bits g (H.position 0 i)
    · exact fun j a ha => H.changes_only_stage j i a ha
    · simp
    · simpa using he i
  intro j i
  have ha := congrFun (hx i) j.castSucc
  have hb := congrFun (hx i) j.succ
  rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, ha] at hb
  exact hb

def augmentByChoice {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) : PathFamily bits (h+k) where
  position t a := gridPartialSweep bits g.val t (Fin.append (H.position 0) (fun i => (x i).val) a)
  disjoint t := (gridPartialSweep bits g.val t).injective.comp (Fin.append_injective_iff.mpr
    ⟨H.disjoint 0, Subtype.val_injective.comp x.injective, fun i j he => (x j).property ⟨i, he⟩⟩)
  changes_only_stage j _ i hi := gridPartialSweep_changes bits g.val _ j i hi

def augmentByChoice_extension {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    PathExtension H (augmentByChoice H x g) where
  labels := ⟨Fin.castAdd k, Fin.castAdd_injective h k⟩
  position_eq t i := by
    change gridPartialSweep bits g.val t (Fin.append _ _ (Fin.castAdd k i)) = _
    rw [Fin.append_left, gridPartialSweep_path H g.val g.property]

lemma placementEvent_iff_augmentation {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) {k : ℕ} (x : Placement H k 0) (g g' : ConditionalChoices H) :
    placementBijection H k g' x = placementBijection H k g x ↔
      pathEvent (augmentByChoice H x g) g'.val := by
  constructor
  · intro he
    apply pathEvent_of_endpoints
    intro a
    change gridSweep bits g'.val (gridPartialSweep bits g.val 0 (Fin.append _ _ a)) =
      gridPartialSweep bits g.val (Fin.last b) (Fin.append _ _ a)
    simp only [gridPartialSweep_zero, gridPartialSweep_last, Equiv.Perm.one_apply]
    induction a using Fin.addCases with
    | left i =>
      rw [Fin.append_left, gridSweep_path H g'.val g'.property, gridSweep_path H g.val g.property]
    | right i =>
      rw [Fin.append_right]
      exact congrArg (fun y : Placement H k (Fin.last b) => (y i).val) he
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change gridSweep bits g'.val (x i).val = gridSweep bits g.val (x i).val
    have hi := gridSweep_path (augmentByChoice H x g) g'.val he (Fin.natAdd h i)
    simpa only [augmentByChoice, Fin.append_right, gridPartialSweep_zero,
      gridPartialSweep_last, Equiv.Perm.one_apply] using hi

lemma placementProbability_pos_has_choice {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    ∃ g : ConditionalChoices H, placementBijection H k g x = y := by
  unfold placementProbability at hp
  by_contra he
  push Not at he
  have hs : (∑ g : ConditionalChoices H,
      if placementBijection H k g x = y then conditionalChoiceWeight H z g else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    simp only [he g, ite_false]
  rw [hs] at hp
  exact (lt_irrefl _ hp)

def realizePlacement {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) : ConditionalChoices H :=
  Classical.choose (placementProbability_pos_has_choice H z x y hp)

def placementTransitionCost {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) : ℝ :=
  if hp : 0 < placementProbability H z x y then
    pathCost (augmentByChoice H x (realizePlacement H z x y hp)) else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_TrajectoryComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g : ConditionalChoices H)

def augmentedPlacement (t : Fin (b+1)) : Placement H k t where
  toFun i := ⟨gridPartialSweep bits g.val t (x i).val, by
    rintro ⟨j,hj⟩
    have he := gridPartialSweep_path H g.val g.property t j
    have hx := (gridPartialSweep bits g.val t).injective (he.trans hj)
    exact (x i).property ⟨j,hx⟩⟩
  inj' i j hij := x.injective (Subtype.ext
    ((gridPartialSweep bits g.val t).injective (congrArg Subtype.val hij)))

lemma augmentedPosition_left (t : Fin (b+1)) (i : Fin h) :
    (augmentByChoice H x g).position t (Fin.castAdd k i) = H.position t i := by
  change gridPartialSweep bits g.val t (Fin.append _ _ (Fin.castAdd k i)) = _
  rw [Fin.append_left,gridPartialSweep_path H g.val g.property]

lemma augmentedPosition_right (t : Fin (b+1)) (i : Fin k) :
    (augmentByChoice H x g).position t (Fin.natAdd h i) = (augmentedPlacement H x g t i).val := by
  change gridPartialSweep bits g.val t (Fin.append _ _ (Fin.natAdd h i)) = _
  rw [Fin.append_right]; rfl

lemma augmentedPlacement_zero : augmentedPlacement H x g 0 = x := by
  apply Function.Embedding.ext
  intro index
  apply Subtype.ext
  change gridPartialSweep bits g.val 0 (x index).val = (x index).val
  rw [gridPartialSweep_zero, Equiv.Perm.one_apply]

def augmentationFreeEquiv (t : Fin (b+1)) :
    FreeSlot (augmentByChoice H x g) t ≃ PlacementComplement (augmentedPlacement H x g t) where
  toFun w := ⟨⟨w.val, by
    rintro ⟨i,hi⟩
    exact w.property ⟨Fin.castAdd k i,(augmentedPosition_left H x g t i).trans hi⟩⟩,by
      rintro ⟨i,hi⟩
      exact w.property ⟨Fin.natAdd h i,(augmentedPosition_right H x g t i).trans
        (congrArg Subtype.val hi)⟩⟩
  invFun w := ⟨w.val.val,by
    rintro ⟨i,hi⟩
    induction i using Fin.addCases with
    | left i =>
      rw [augmentedPosition_left] at hi
      exact w.val.property ⟨i,hi⟩
    | right i =>
      rw [augmentedPosition_right] at hi
      exact w.property ⟨i,Subtype.ext hi⟩⟩
  left_inv w := rfl
  right_inv w := rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]

def movePlacement (g : Equiv.Perm X) (x : J ↪ X) : J ↪ X := x.trans g.toEmbedding

omit [Fintype X] [DecidableEq X] [Fintype J] in
@[simp] lemma movePlacement_one (x : J ↪ X) : movePlacement 1 x = x := by ext; rfl

def placementRep : Representation ℂ (Equiv.Perm X) ((J ↪ X) → ℂ) where
  toFun g := {
    toFun := fun v x => v (movePlacement g⁻¹ x)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext; simp
  map_mul' g h := by ext v x; rfl

variable (μ : YoungDiagram)

abbrev Tail := {x : Cell μ // row x ≠ 0}

lemma placement_extends (x : Tail μ ↪ Cell μ) :
    ∃ g : G μ, ∀ a : Tail μ, g a.val = x a :=
  Equiv.Perm.exists_extending_pair Subtype.val x Subtype.val_injective x.injective

def placementTabloid (x : Tail μ ↪ Cell μ) : Tabloid μ :=
  tabloidOfPerm μ (placement_extends μ x).choose

def spechtPlacement : SpechtSpace μ →ₗ[ℂ] ((Tail μ ↪ Cell μ) → ℂ) where
  toFun v x := spechtInclude μ v (placementTabloid μ x)
  map_add' v w := by ext x; simp
  map_smul' z v := by ext x; simp

section ColumnSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def columnSum (ρ : Representation ℂ (G μ) V) : Module.End ℂ V :=
  ∑ c : C μ, signC μ c.val • ρ c.val

end ColumnSum

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_AugmentedComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g₀ : ConditionalChoices H)

def augmentedOutputIndex : Placement H k 0 :=
  x.trans (remainingPerm H g₀.val g₀.property).toEmbedding

lemma augmentedOutputIndex_physical :
    (augmentedPlacement H x g₀ (Fin.last b)).trans (freeIdentification H).symm.toEmbedding =
      augmentedOutputIndex H x g₀ := by
  apply Function.Embedding.ext
  intro i
  apply (freeIdentification H).injective
  simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
  change augmentedPlacement H x g₀ (Fin.last b) i=
    (freeIdentification H) ((freeIdentification H).symm (remainingBijection H g₀.val g₀.property (x i)))
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun a : Equiv.Perm (GridSlot bits) => a (x i).val) (gridPartialSweep_last bits g₀.val)

def augmentationInputComplement : FreeSlot (augmentByChoice H x g₀) 0 ≃ PlacementComplement x :=
  (augmentationFreeEquiv H x g₀ 0).trans
    (complementMap (Equiv.refl _) _ x (by
      simpa only [Equiv.refl_toEmbedding,Function.Embedding.trans_refl] using augmentedPlacement_zero H x g₀))

def augmentationOutputComplement : FreeSlot (augmentByChoice H x g₀) (Fin.last b) ≃
    PlacementComplement (augmentedOutputIndex H x g₀) :=
  (augmentationFreeEquiv H x g₀ (Fin.last b)).trans
    (complementMap (freeIdentification H).symm _ _ (augmentedOutputIndex_physical H x g₀))

lemma augmentedOutputIndex_event (g : ConditionalChoices H) :
    x.trans (remainingPerm H g.val g.property).toEmbedding=augmentedOutputIndex H x g₀ ↔
      pathEvent (augmentByChoice H x g₀) g.val := by
  rw [← placementEvent_iff_augmentation H x g₀ g]
  constructor
  · intro he
    apply Function.Embedding.ext
    intro i
    apply (freeIdentification H).symm.injective
    exact congrArg (fun y : Placement H k 0 => y i) he
  · intro he
    apply Function.Embedding.ext
    intro i
    exact congrArg (fun y : Placement H k (Fin.last b) => (freeIdentification H).symm (y i)) he

lemma augmented_event (g : ConditionalChoices (augmentByChoice H x g₀)) :
    x.trans (remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property)).toEmbedding =
      augmentedOutputIndex H x g₀ :=
  (augmentedOutputIndex_event H x g₀ ((augmentByChoice_extension H x g₀).restrictChoice g)).mpr g.property

variable {A : Type*} [Fintype A] (e : A ⊕ Fin k ≃ FreeSlot H 0)

def augmentedInputBasis : A ≃ FreeSlot (augmentByChoice H x g₀) 0 :=
  (placementComplementEquiv e x).trans (augmentationInputComplement H x g₀).symm

def augmentedOutputBasis : A ≃ FreeSlot (augmentByChoice H x g₀) (Fin.last b) :=
  (placementComplementEquiv e (augmentedOutputIndex H x g₀)).trans
    (augmentationOutputComplement H x g₀).symm

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

 def subPlacement (A : Finset I) (x : I ↪ X) : A ↪ X :=
  (Function.Embedding.subtype (fun i => i∈A)).trans x

def placementMoveEquiv (g : Equiv.Perm X) : (I ↪ X) ≃ (I ↪ X) :=
  (Equiv.refl I).embeddingCongr g

def placementMarginal (A : Finset I) : ((I ↪ X) → ℂ) →ₗ[ℂ] ((A ↪ X) → ℂ) where
  toFun v u := ∑x : I ↪ X, if subPlacement A x=u then v x else 0
  map_add' v w := by
    funext u
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  map_smul' c v := by
    funext u
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_CenteredPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

 def partialPlacement (A : Finset I) (g : Equiv.Perm X) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) where
  toFun v y := placementMarginal A v (movePlacement g⁻¹ (subPlacement A y))
  map_add' v w := by ext y; simp only [map_add,Pi.add_apply]
  map_smul' c v := by ext y; simp only [map_smul,RingHom.id_apply,Pi.smul_apply]

 def placementAverage (p : Equiv.Perm X → ℂ) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) := ∑g, p g • placementRep g

 def partialPlacementAverage (A : Finset I) (p : Equiv.Perm X → ℂ) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) := ∑g, p g • partialPlacement A g

 def centeredPlacement (s : ℂ) (p : Equiv.Perm X → ℂ) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) :=
  ∑A ∈ (Finset.univ : Finset I).powerset,
    ((-1:ℂ)^(Fintype.card I-A.card)*s^A.card/s^Fintype.card I) • partialPlacementAverage A p

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

 def placementCoeffs : EuclideanSpace ℂ (I ↪ X) ≃ₗ[ℂ] ((I ↪ X) → ℂ) :=
  WithLp.linearEquiv 2 ℂ _
 def partialHilbert (A : Finset I) (g : Equiv.Perm X) :
    EuclideanSpace ℂ (I ↪ X) →ₗ[ℂ] EuclideanSpace ℂ (I ↪ X) :=
  placementCoeffs.symm.conj (partialPlacement A g)
 def partialKernel (A : Finset I) (g : Equiv.Perm X) : Matrix (I ↪ X) (I ↪ X) ℂ :=
  fun y x => if subPlacement A (movePlacement g x)=subPlacement A y then 1 else 0

 def centeredHilbert (s : ℝ) (p : Equiv.Perm X → ℂ) :
    EuclideanSpace ℂ (I ↪ X) →ₗ[ℂ] EuclideanSpace ℂ (I ↪ X) :=
  placementCoeffs.symm.conj (centeredPlacement (s:ℂ) p)

 def spechtPlacementHilbert (μ : YoungDiagram) :
    SpechtHilbert μ →ₗ[ℂ] EuclideanSpace ℂ (Tail μ ↪ Cell μ) :=
  placementCoeffs.symm.toLinearMap.comp ((spechtPlacement μ).comp (spechtHilbertEquiv μ).symm.toLinearMap)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_CenteredMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

def centeredMatrix (s : ℝ) (p : Equiv.Perm X → ℂ) : Matrix (I ↪ X) (I ↪ X) ℂ :=
  ∑A ∈ (Finset.univ : Finset I).powerset,
    ((-1:ℂ)^(Fintype.card I-A.card)*(s:ℂ)^A.card/(s:ℂ)^Fintype.card I) •
      ∑g, p g • partialKernel A g

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_PlacementAlternation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I : Type*} [DecidableEq I]

def alternatingSubsetSum (U : Finset I) (s : ℝ) (p : Finset I → ℝ) : ℝ :=
  ∑A ∈ U.powerset, (-1:ℝ)^(U.card-A.card)*s^A.card*p A

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_FiniteProductProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

def productWeight (p : Ω → ℝ) (x : I → Ω) : ℝ := ∏ i, p (x i)

def productProbability (p : Ω → ℝ) (E : (I → Ω) → Prop) : ℝ :=
  ∑ x, productWeight p x * (if E x then 1 else 0)

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SharingProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H Ω : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype Ω]

 def sharingGraph (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first) (x : I → Ω) : SimpleGraph I where
  Adj i j := i ≠ j ∧ R (x i) (x j)
  symm := ⟨fun _ _ h => ⟨h.1.symm,hs h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def incidentSet (R : Ω → Ω → Prop) (roots : H → Ω) (x : I → Ω) : Finset I :=
  Finset.univ.filter (fun i => (∃ j, i ≠ j ∧ R (x i) (x j)) ∨ ∃ h, R (x i) (roots h))

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_UniformFiniteProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {Ω V W : Type*} [Fintype Ω] [Fintype V] [Fintype W]

 def uniformWeight (_u : Ω) : ℝ := 1 / Fintype.card Ω

def finiteProbability (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ u, p u * (if E u then 1 else 0)

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
namespace Sparse
variable {b : ℕ} {bits : Fin b → ℕ}

def independentPosition (z : GridSlot bits × GridSlot bits) (t : Fin (b+1)) : GridSlot bits :=
  fun i => if i.val<t.val then z.2 i else z.1 i

def endpointSwap (t : Fin (b+1)) :
    (GridSlot bits × GridSlot bits) ≃ GridSlot bits × GridSlot bits where
  toFun z := (independentPosition z t,independentPosition (z.2,z.1) t)
  invFun z := (independentPosition z t,independentPosition (z.2,z.1) t)
  left_inv z := by
    apply Prod.ext <;> funext i <;> dsimp [independentPosition] <;> split <;> rfl
  right_inv z := by
    apply Prod.ext <;> funext i <;> dsimp [independentPosition] <;> split <;> rfl

def shareVertex (z w : GridSlot bits × GridSlot bits) : Prop :=
  ∃t : Fin (b+1), independentPosition z t=independentPosition w t

def endpointLineEquiv (j : Fin b) :
    (GridSlot bits × GridSlot bits) ≃
      GridOutside bits j × (Slot (bits j) × GridSlot bits) :=
  (endpointSwap j.castSucc).trans
    (((Equiv.piSplitAt j (fun i : Fin b => Slot (bits i))).trans (Equiv.prodComm _ _)).prodCongr
      (Equiv.refl _)) |>.trans (Equiv.prodAssoc _ _ _)

end Sparse
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_OneCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

def binaryPosition {d : ℕ} (x y : Slot d) (t : Fin (d+1)) : Slot d :=
  fun i => if i.val<t.val then y i else x i

def binaryPartialSweep (d : ℕ) (c : SweepCoins d) (t : Fin (d+1)) : Equiv.Perm (Slot d) :=
  ((List.ofFn (fun j => coordinateLayer d j (c j))).take t.val).reverse.prod

@[simp] lemma binaryPartialSweep_zero (d : ℕ) (c : SweepCoins d) : binaryPartialSweep d c 0=1 := by
  simp [binaryPartialSweep]

@[simp] lemma binaryPartialSweep_last (d : ℕ) (c : SweepCoins d) :
    binaryPartialSweep d c (Fin.last d)=binarySweep d c := by
  unfold binaryPartialSweep binarySweep
  rw [List.take_of_length_le (by simp)]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ}

lemma gridLayer_at (g : GridChoices bits) (j : Fin b) (x : GridSlot bits) :
    gridLayer bits g j x j = g j (fun i => x i) (x j) := by
  simp [gridLayer,Equiv.piSplitAt_symm_apply]

@[simp] lemma independentPosition_zero (e : GridSlot bits × GridSlot bits) :
    independentPosition e 0=e.1 := by ext i; simp [independentPosition]

@[simp] lemma independentPosition_last (e : GridSlot bits × GridSlot bits) :
    independentPosition e (Fin.last b)=e.2 := by ext i; simp [independentPosition]

def endpointLine (e : GridSlot bits × GridSlot bits) (j : Fin b) : GridOutside bits j :=
  fun i => independentPosition e j.castSucc i

variable {I : Type*} [Fintype I] [DecidableEq I]

def localEndpointEvent (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) : Prop :=
  ∀i ∈ A, endpointLine (e i) j=y → σ ((e i).1 j)=(e i).2 j

def endpointMass (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) : ℝ :=
  ∑g : GridChoices bits, if pathEvent H g ∧ ∀i ∈ A, gridSweep bits g (e i).1=(e i).2 then
    gridWeight bits z g else 0

def localEndpointMass (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (j : Fin b) (y : GridOutside bits j) : ℝ :=
  ∑σ, if Assigns (lineInput H j y) (lineOutput H j y) σ ∧ localEndpointEvent A e j y σ then
    lineLaw (bits j) z σ else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_IsolatedCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ}
variable {I : Type*} [DecidableEq I]

variable [Fintype I]

def endpointProbability (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) : ℝ := endpointMass H z A e / conditionalNormalizer H z

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def centeredEndpointKernel (H : PathFamily bits h) (z : ℝ)
    (e : I → GridSlot bits × GridSlot bits) : ℝ :=
  (gridSize bits:ℝ)⁻¹ ^ Fintype.card I *
    alternatingSubsetSum Finset.univ (gridSize bits) (fun A => endpointProbability H z A e)

def pathEndpoints (H : PathFamily bits h) (k : Fin h) : GridSlot bits × GridSlot bits :=
  (H.position 0 k,H.position (Fin.last b) k)

def shareLine (e f : GridSlot bits × GridSlot bits) : Prop :=
  ∃j, endpointLine e j=endpointLine f j

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def restrictPlacement {t : Fin (b+1)} (x : Placement H k t) (A : Finset (Fin k)) :
    Placement H (Fintype.card A) t where
  toFun i := x ((Fintype.equivFin A).symm i).val
  inj' _ _ he := (Fintype.equivFin A).symm.injective
    (Subtype.ext (x.injective he))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_AugmentedBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g₀ : ConditionalChoices H)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

def augmentedFrame : Equiv.Perm A :=
  ((augmentedInputBasis H x g₀ e).trans (freeIdentification (augmentByChoice H x g₀))).trans
    (augmentedOutputBasis H x g₀ e).symm

def augmentedRepresentation : Representation ℂ (Equiv.Perm (FreeSlot (augmentByChoice H x g₀) 0)) W :=
  σ.comp (augmentedInputBasis H x g₀ e).symm.permCongrHom.toMonoidHom

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_BlockTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder

section Expansion
variable {P R : Type*} [Fintype P] [DecidableEq P] [Semiring R]

def pathProduct {n : ℕ} (A : Fin n → Matrix P P R) (x : Fin n → P) (b : P) : R :=
  (List.ofFn fun j => A j (x j) (Fin.snoc (α := fun _ => P) x b j.succ)).prod

end Expansion

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_HilbertBlockTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
local notation "HW" => CoindHilbertSpace (I:=I) (W:=W)

omit [DecidableEq I] [FiniteDimensional ℂ W] in
lemma fiber_sum (v : HW) : ∑i, fiberInclude i (v i)=v := by
  classical
  apply (WithLp.linearEquiv 2 ℂ (I → W)).injective
  simp only [map_sum]
  ext i
  simp only [fiberInclude,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.single_apply,Finset.sum_apply,Pi.single_apply]
  simp only [WithLp.coe_linearEquiv]
  let : DecidableEq I := fun i j => Classical.propDecidable (i=j)
  exact (Finset.sum_ite_eq Finset.univ i (fun x => v x)).trans (ite_eq_left (Finset.mem_univ i))

omit [DecidableEq I] [FiniteDimensional ℂ W] in
lemma hilbertBlock_mul (A B : HW →ₗ[ℂ] HW) (i j : I) :
    hilbertBlock (A*B) i j = ∑a, hilbertBlock A i a * hilbertBlock B a j := by
  ext v
  change A (B (fiberInclude j v)) i = _
  conv_lhs => rw [← fiber_sum (B (fiberInclude j v))]
  simp only [map_sum,LinearMap.sum_apply,Module.End.mul_apply]
  change (WithLp.linearEquiv 2 ℂ (I → W)) (∑ x, A (fiberInclude x (B (fiberInclude j v) x))) i = _
  rw [map_sum,Finset.sum_apply]
  rfl

omit [Fintype I] [FiniteDimensional ℂ W] in
lemma hilbertBlock_one (i j : I) : hilbertBlock (1 : HW →ₗ[ℂ] HW) i j = if i=j then 1 else 0 := by
  ext v
  change fiberInclude j v i = _
  rw [fiberInclude_apply]
  split_ifs <;> rfl

def hilbertBlocksHom : (HW →ₗ[ℂ] HW) →* Matrix I I (W →ₗ[ℂ] W) where
  toFun A := hilbertBlock A
  map_one' := by funext i j; exact hilbertBlock_one i j
  map_mul' A B := by funext i j; exact hilbertBlock_mul A B i j

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_PlacementCycleMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

abbrev inducedPlacementAverage (z : ℝ) :=
  groupAverage (coindHilbertRep (blockPerm e) σ
    (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
    (fun a => (conditionalGroupLaw H z a:ℂ))

def placementFiberMoment (z : ℝ) (q : ℕ) (x y : Placement H k 0) : ℝ :=
  if hp : 0<placementKernel H z x y then
    let g := realizePlacement H z x (placementIdentification H k y) hp
    evenMoment q (groupAverage (augmentedRepresentation H x g e σ)
      (fun a => (conditionalGroupLaw (augmentByChoice H x g) z a:ℂ)))
  else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_WeightedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

def placementEdgeCost {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (reverse : Bool) {k : ℕ} (x y : Placement H k 0) : ℝ :=
  if reverse then placementTransitionCost H z y (placementIdentification H k x)
  else placementTransitionCost H z x (placementIdentification H k y)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_IndependentPush
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {I : Type*} [Fintype I] {Ω G : I → Type*}
  [∀i,Fintype (Ω i)] [∀i,Fintype (G i)]

def finitePush {X Y : Type*} [Fintype X] (w : X → ℂ) (f : X → Y) (y : Y) : ℂ :=
  ∑x, if f x=y then w x else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SampleMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation TraceHolder Density

namespace Signed
variable {A X : Type*} [Fintype A] [DecidableEq A] [Fintype X] {N : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def sampleMatrix (p : A → Bool) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :=
  ∑x, w x • actionMatrix p (f x)

end Signed
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

abbrev leftBits : Fin m → ℕ := fun i => bits (i.castAdd n)
abbrev rightBits : Fin n → ℕ := fun i => bits (i.natAdd m)
def leftSlot (x : GridSlot bits) : GridSlot (leftBits bits) := fun i => x (i.castAdd n)
def rightSlot (x : GridSlot bits) : GridSlot (rightBits bits) := fun i => x (i.natAdd m)
def joinSlot (x : GridSlot (leftBits bits)) (y : GridSlot (rightBits bits)) : GridSlot bits :=
  Fin.addCases x y

def slotEquiv : GridSlot bits ≃ GridSlot (leftBits bits) × GridSlot (rightBits bits) where
  toFun x := (leftSlot bits x,rightSlot bits x)
  invFun xy := joinSlot bits xy.1 xy.2
  left_inv x := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [joinSlot,leftSlot]
    | right i => simp [joinSlot,rightSlot]
  right_inv xy := by
    apply Prod.ext <;> funext i
    · simp [leftSlot,joinSlot]
    · simp [rightSlot,joinSlot]

def leftTime (t : Fin (m+1)) : Fin (m+n+1) := ⟨t.val,by omega⟩
def rightTime (t : Fin (n+1)) : Fin (m+n+1) := ⟨m+t.val,by omega⟩

variable (H : PathFamily bits h)

lemma rightSlot_leftTime (t : Fin (m+1)) (k : Fin h) :
    rightSlot bits (H.position (leftTime t) k)=rightSlot bits (H.position 0 k) := by
  funext i
  unfold rightSlot
  have he := trajectory_coordinates (fun t => H.position t k)
    (fun j i hi => H.changes_only_stage j k i hi) (leftTime t) (i.natAdd m)
  rw [ite_eq_right (show ¬(i.natAdd m).val < (leftTime t).val from by
    change ¬m+i.val<t.val; omega)] at he
  exact he

lemma leftSlot_rightTime (t : Fin (n+1)) (k : Fin h) :
    leftSlot bits (H.position (rightTime t) k)=leftSlot bits (H.position (rightTime (m:=m) 0) k) := by
  funext i
  unfold leftSlot
  have he (u : Fin (n+1)) : H.position (rightTime u) k (i.castAdd n) =
      H.position (Fin.last (m+n)) k (i.castAdd n) := by
    have he := trajectory_coordinates (fun t => H.position t k)
      (fun j i hi => H.changes_only_stage j k i hi) (rightTime u) (i.castAdd n)
    rw [ite_eq_left (show (i.castAdd n).val < (rightTime u).val from by
      change i.val < m + u.val; omega)] at he
    exact he
  exact (he t).trans (he 0).symm

abbrev RowLabels (y : GridSlot (rightBits bits)) :=
  {k : Fin h // rightSlot bits (H.position 0 k)=y}
abbrev ColumnLabels (x : GridSlot (leftBits bits)) :=
  {k : Fin h // leftSlot bits (H.position (rightTime (m:=m) 0) k)=x}

noncomputable instance rowLabelsFintype (y : GridSlot (rightBits bits)) :
    Fintype (RowLabels bits H y) := Fintype.ofFinite _
noncomputable instance columnLabelsFintype (x : GridSlot (leftBits bits)) :
    Fintype (ColumnLabels bits H x) := Fintype.ofFinite _

def rowFamily (y : GridSlot (rightBits bits)) :
    PathFamily (leftBits bits) (Fintype.card (RowLabels bits H y)) where
  position t k := leftSlot bits (H.position (leftTime t) ((Fintype.equivFin (RowLabels bits H y)).symm k).val)
  disjoint t a b he := by
    apply (Fintype.equivFin (RowLabels bits H y)).symm.injective
    apply Subtype.ext
    apply H.disjoint (leftTime t)
    apply (slotEquiv bits).injective
    apply Prod.ext
    · exact he
    · change rightSlot bits (H.position (leftTime t) _) = rightSlot bits (H.position (leftTime t) _)
      simp only [rightSlot_leftTime]
      exact ((Fintype.equivFin (RowLabels bits H y)).symm a).property.trans
        ((Fintype.equivFin (RowLabels bits H y)).symm b).property.symm
  changes_only_stage j k i hi := by
    change H.position (leftTime j.succ) _ (i.castAdd n) = H.position (leftTime j.castSucc) _ (i.castAdd n)
    exact H.changes_only_stage (j.castAdd n) _ (i.castAdd n)
      (fun he => hi (Fin.ext (congrArg (fun q : Fin (m+n) => q.val) he)))

def columnFamily (x : GridSlot (leftBits bits)) :
    PathFamily (rightBits bits) (Fintype.card (ColumnLabels bits H x)) where
  position t k := rightSlot bits (H.position (rightTime t) ((Fintype.equivFin (ColumnLabels bits H x)).symm k).val)
  disjoint t a b he := by
    apply (Fintype.equivFin (ColumnLabels bits H x)).symm.injective
    apply Subtype.ext
    apply H.disjoint (rightTime t)
    apply (slotEquiv bits).injective
    apply Prod.ext
    · change leftSlot bits (H.position (rightTime t) _) = leftSlot bits (H.position (rightTime t) _)
      simp only [leftSlot_rightTime]
      exact ((Fintype.equivFin (ColumnLabels bits H x)).symm a).property.trans
        ((Fintype.equivFin (ColumnLabels bits H x)).symm b).property.symm
    · exact he
  changes_only_stage j k i hi := by
    change H.position (rightTime j.succ) _ (i.natAdd m) = H.position (rightTime j.castSucc) _ (i.natAdd m)
    exact H.changes_only_stage (j.natAdd m) _ (i.natAdd m)
      (fun he => hi (Fin.ext (by have hh := congrArg (fun q : Fin (m+n) => q.val) he; simpa using hh)))

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n : ℕ} (bits : Fin (m+n) → ℕ)

def fillSlot {b : ℕ} (a : Fin b → ℕ) (j : Fin b) (u : GridOutside a j) : GridSlot a :=
  (Equiv.piSplitAt j (fun i => Slot (a i))).symm (fun _ => false,u)

lemma fillSlot_other {b : ℕ} (a : Fin b → ℕ) (j : Fin b) (u : GridOutside a j)
    (i : Fin b) (hi : i≠j) : fillSlot a j u i=u ⟨i,hi⟩ := by
  simp [fillSlot,Equiv.piSplitAt,hi]

def leftOutsideEquiv (j : Fin m) :
    GridOutside bits (j.castAdd n) ≃ GridSlot (rightBits bits) × GridOutside (leftBits bits) j where
  toFun u := (fun i => u ⟨i.natAdd m,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.castAdd n,fun h => i.property (Fin.ext (congrArg (fun q:Fin (m+n) => q.val) h))⟩)
  invFun yu i := joinSlot bits (fillSlot (leftBits bits) j yu.2) yu.1 i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.castAdd n) h)
      simp only [joinSlot,Fin.addCases_left,fillSlot_other _ _ _ _ hij]
    | right i => intro hi; simp only [joinSlot,Fin.addCases_right]
  right_inv yu := by
    apply Prod.ext
    · funext i
      simp only [joinSlot,Fin.addCases_right]
    · funext i
      simp only [joinSlot,Fin.addCases_left,fillSlot_other _ _ _ _ i.property]

def rightOutsideEquiv (j : Fin n) :
    GridOutside bits (j.natAdd m) ≃ GridSlot (leftBits bits) × GridOutside (rightBits bits) j where
  toFun u := (fun i => u ⟨i.castAdd n,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.natAdd m,fun h => i.property (Fin.ext (by have hh := congrArg (fun q:Fin (m+n) => q.val) h; simpa using hh))⟩)
  invFun xu i := joinSlot bits xu.1 (fillSlot (rightBits bits) j xu.2) i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i => intro hi; simp only [joinSlot,Fin.addCases_left]
    | right i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.natAdd m) h)
      simp only [joinSlot,Fin.addCases_right,fillSlot_other _ _ _ _ hij]
  right_inv xu := by
    apply Prod.ext
    · funext i
      simp only [joinSlot,Fin.addCases_left]
    · funext i
      simp only [joinSlot,Fin.addCases_right,fillSlot_other _ _ _ _ i.property]

def rowChoices (g : GridChoices bits) (y : GridSlot (rightBits bits)) : GridChoices (leftBits bits) :=
  fun j u => g (j.castAdd n) ((leftOutsideEquiv bits j).symm (y,u))
def columnChoices (g : GridChoices bits) (x : GridSlot (leftBits bits)) : GridChoices (rightBits bits) :=
  fun j u => g (j.natAdd m) ((rightOutsideEquiv bits j).symm (x,u))

def joinChoices (L : GridSlot (rightBits bits) → GridChoices (leftBits bits))
    (R : GridSlot (leftBits bits) → GridChoices (rightBits bits)) : GridChoices bits :=
  Fin.addCases (fun j u => L ((leftOutsideEquiv bits j) u).1 j ((leftOutsideEquiv bits j) u).2)
    (fun j u => R ((rightOutsideEquiv bits j) u).1 j ((rightOutsideEquiv bits j) u).2)

def choicesEquiv : GridChoices bits ≃
    (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
    (GridSlot (leftBits bits) → GridChoices (rightBits bits)) where
  toFun g := (rowChoices bits g,columnChoices bits g)
  invFun LR := joinChoices bits LR.1 LR.2
  left_inv g := by
    funext j u
    induction j using Fin.addCases with
    | left j => simp [joinChoices,rowChoices]
    | right j => simp [joinChoices,columnChoices]
  right_inv LR := by
    apply Prod.ext
    · funext y j u
      simp [rowChoices,joinChoices]
    · funext x j u
      simp [columnChoices,joinChoices]

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

section
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

lemma outside_left (j : Fin m) (x : GridSlot bits) :
    (leftOutsideEquiv bits j) (fun i => x i.val) =
      (rightSlot bits x,fun i : {i : Fin m // i≠j} => leftSlot bits x i.val) := rfl
lemma outside_right (j : Fin n) (x : GridSlot bits) :
    (rightOutsideEquiv bits j) (fun i => x i.val) =
      (leftSlot bits x,fun i : {i : Fin n // i≠j} => rightSlot bits x i.val) := rfl

lemma rowChoices_at (g : GridChoices bits) (x : GridSlot bits) (j : Fin m) :
    rowChoices bits g (rightSlot bits x) j (fun i => leftSlot bits x i.val) =
      g (j.castAdd n) (fun i => x i.val) := by
  unfold rowChoices
  rw [← outside_left,Equiv.symm_apply_apply]

lemma columnChoices_at (g : GridChoices bits) (x : GridSlot bits) (j : Fin n) :
    columnChoices bits g (leftSlot bits x) j (fun i => rightSlot bits x i.val) =
      g (j.natAdd m) (fun i => x i.val) := by
  unfold columnChoices
  rw [← outside_right,Equiv.symm_apply_apply]

lemma gridLayer_path_iff {b h : ℕ} {a : Fin b → ℕ} (H : PathFamily a h)
    (g : GridChoices a) (j : Fin b) (k : Fin h) :
    gridLayer a g j (H.position j.castSucc k)=H.position j.succ k ↔
      g j (fun i => H.position j.castSucc k i.val) (H.position j.castSucc k j)=H.position j.succ k j := by
  constructor
  · intro he
    have hh := congrFun he j
    rwa [gridLayer_at] at hh
  · intro he
    funext i
    by_cases hi : i=j
    · subst i; exact (gridLayer_at g j _).trans he
    · rw [gridLayer_other a g j i hi,H.changes_only_stage j k i hi]

end

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma row_stage_iff (g : GridChoices bits) (y : GridSlot (rightBits bits))
    (j : Fin m) (a : RowLabels bits H y) :
    gridLayer (leftBits bits) (rowChoices bits g y) j
      ((rowFamily bits H y).position j.castSucc (Fintype.equivFin (RowLabels bits H y) a)) =
      (rowFamily bits H y).position j.succ (Fintype.equivFin (RowLabels bits H y) a) ↔
    gridLayer bits g (j.castAdd n) (H.position (leftTime j.castSucc) a.val) =
      H.position (leftTime j.succ) a.val := by
  change _ ↔ gridLayer bits g (j.castAdd n)
    (H.position (j.castAdd n).castSucc a.val)=H.position (j.castAdd n).succ a.val
  rw [gridLayer_path_iff (rowFamily bits H y),
    gridLayer_path_iff H g (j.castAdd n) a.val]
  simp only [rowFamily,Equiv.symm_apply_apply]
  have hr : rightSlot bits (H.position (leftTime j.castSucc) a.val)=y :=
    (rightSlot_leftTime bits H j.castSucc a.val).trans a.property
  have hc : rowChoices bits g y j
      (fun i => leftSlot bits (H.position (leftTime j.castSucc) a.val) i.val) =
      g (j.castAdd n) (fun i => H.position (leftTime j.castSucc) a.val i.val) := by
    simpa only [hr] using rowChoices_at bits g (H.position (leftTime j.castSucc) a.val) j
  rw [hc]
  rfl

lemma column_stage_iff (g : GridChoices bits) (x : GridSlot (leftBits bits))
    (j : Fin n) (a : ColumnLabels bits H x) :
    gridLayer (rightBits bits) (columnChoices bits g x) j
      ((columnFamily bits H x).position j.castSucc (Fintype.equivFin (ColumnLabels bits H x) a)) =
      (columnFamily bits H x).position j.succ (Fintype.equivFin (ColumnLabels bits H x) a) ↔
    gridLayer bits g (j.natAdd m) (H.position (rightTime j.castSucc) a.val) =
      H.position (rightTime j.succ) a.val := by
  change _ ↔ gridLayer bits g (j.natAdd m)
    (H.position (j.natAdd m).castSucc a.val)=H.position (j.natAdd m).succ a.val
  rw [gridLayer_path_iff (columnFamily bits H x),
    gridLayer_path_iff H g (j.natAdd m) a.val]
  simp only [columnFamily,Equiv.symm_apply_apply]
  have hr : leftSlot bits (H.position (rightTime j.castSucc) a.val)=x :=
    (leftSlot_rightTime bits H j.castSucc a.val).trans a.property
  have hc : columnChoices bits g x j
      (fun i => rightSlot bits (H.position (rightTime j.castSucc) a.val) i.val) =
      g (j.natAdd m) (fun i => H.position (rightTime j.castSucc) a.val i.val) := by
    simpa only [hr] using columnChoices_at bits g (H.position (rightTime j.castSucc) a.val) j
  rw [hc]
  rfl

theorem pathEvent_split (g : GridChoices bits) :
    pathEvent H g ↔
      (∀y, pathEvent (rowFamily bits H y) (rowChoices bits g y)) ∧
      (∀x, pathEvent (columnFamily bits H x) (columnChoices bits g x)) := by
  constructor
  · intro hg
    constructor
    · intro y j k
      obtain ⟨a,rfl⟩ := (Fintype.equivFin (RowLabels bits H y)).surjective k
      exact (row_stage_iff bits H g y j a).mpr (hg _ _)
    · intro x j k
      obtain ⟨a,rfl⟩ := (Fintype.equivFin (ColumnLabels bits H x)).surjective k
      exact (column_stage_iff bits H g x j a).mpr (hg _ _)
  · rintro ⟨hL,hR⟩ j k
    induction j using Fin.addCases with
    | left j =>
      let y := rightSlot bits (H.position 0 k)
      let a : RowLabels bits H y := ⟨k,rfl⟩
      exact (row_stage_iff bits H g y j a).mp (hL y j _)
    | right j =>
      let x := leftSlot bits (H.position (rightTime (m:=m) 0) k)
      let a : ColumnLabels bits H x := ⟨k,rfl⟩
      exact (column_stage_iff bits H g x j a).mp (hR x j _)

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
attribute [local instance] Classical.propDecidable
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma rowChoices_symm (LR : (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
    (GridSlot (leftBits bits) → GridChoices (rightBits bits))) :
    rowChoices bits ((choicesEquiv bits).symm LR)=LR.1 :=
  congrArg Prod.fst ((choicesEquiv bits).apply_symm_apply LR)
lemma columnChoices_symm (LR : (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
    (GridSlot (leftBits bits) → GridChoices (rightBits bits))) :
    columnChoices bits ((choicesEquiv bits).symm LR)=LR.2 :=
  congrArg Prod.snd ((choicesEquiv bits).apply_symm_apply LR)

def conditionalChoicesEquiv : ConditionalChoices H ≃
    (∀y, ConditionalChoices (rowFamily bits H y)) ×
    (∀x, ConditionalChoices (columnFamily bits H x)) where
  toFun g := (fun y => ⟨rowChoices bits g.val y,(pathEvent_split bits H g.val).mp g.property |>.1 y⟩,
    fun x => ⟨columnChoices bits g.val x,(pathEvent_split bits H g.val).mp g.property |>.2 x⟩)
  invFun LR := ⟨(choicesEquiv bits).symm (fun y => (LR.1 y).val,fun x => (LR.2 x).val), by
    rw [pathEvent_split,rowChoices_symm,columnChoices_symm]
    exact ⟨fun y => (LR.1 y).property,fun x => (LR.2 x).property⟩⟩
  left_inv g := by
    classical
    apply Subtype.ext
    exact (choicesEquiv bits).symm_apply_apply g.val
  right_inv LR := by
    classical
    apply Prod.ext <;> funext a <;> apply Subtype.ext
    · exact congrFun (rowChoices_symm bits _) a
    · exact congrFun (columnChoices_symm bits _) a

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

variable {X Y : Type*}
def rowPerm (f : Y → Equiv.Perm X) : Equiv.Perm (X×Y) where
  toFun xy := (f xy.2 xy.1,xy.2)
  invFun xy := ((f xy.2).symm xy.1,xy.2)
  left_inv xy := by simp
  right_inv xy := by simp

def columnPerm (f : X → Equiv.Perm Y) : Equiv.Perm (X×Y) where
  toFun xy := (xy.1,f xy.1 xy.2)
  invFun xy := (xy.1,(f xy.1).symm xy.2)
  left_inv xy := by simp
  right_inv xy := by simp

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

@[simp] lemma left_join (x : GridSlot (leftBits bits)) (y : GridSlot (rightBits bits)) :
    leftSlot bits (joinSlot bits x y)=x := by funext i; simp [leftSlot,joinSlot]
@[simp] lemma right_join (x : GridSlot (leftBits bits)) (y : GridSlot (rightBits bits)) :
    rightSlot bits (joinSlot bits x y)=y := by funext i; simp [rightSlot,joinSlot]
@[simp] lemma join_left_right (x : GridSlot bits) :
    joinSlot bits (leftSlot bits x) (rightSlot bits x)=x := (slotEquiv bits).symm_apply_apply x

def rowFreeEquiv (t : Fin (m+1)) : FreeSlot H (leftTime t) ≃
    Σy : GridSlot (rightBits bits), FreeSlot (rowFamily bits H y) t where
  toFun x := ⟨rightSlot bits x.val,⟨leftSlot bits x.val,by
    rintro ⟨a,ha⟩
    let k := (Fintype.equivFin (RowLabels bits H (rightSlot bits x.val))).symm a
    apply x.property
    refine ⟨k.val,?_⟩
    apply (slotEquiv bits).injective
    apply Prod.ext
    · exact ha
    · exact (rightSlot_leftTime bits H t k.val).trans k.property⟩⟩
  invFun yx := ⟨joinSlot bits yx.2.val yx.1,by
    rintro ⟨k,hk⟩
    have he := congrArg (slotEquiv bits) hk
    have hr : rightSlot bits (H.position 0 k)=yx.1 := by
      rw [←rightSlot_leftTime bits H t k]
      exact (congrArg Prod.snd he).trans (congrArg Prod.snd ((slotEquiv bits).apply_symm_apply (yx.2.val,yx.1)))
    apply yx.2.property
    refine ⟨Fintype.equivFin (RowLabels bits H yx.1) ⟨k,hr⟩,?_⟩
    simp only [rowFamily,Equiv.symm_apply_apply]
    exact (congrArg Prod.fst he).trans (congrArg Prod.fst ((slotEquiv bits).apply_symm_apply (yx.2.val,yx.1)))⟩
  left_inv x := by
    apply Subtype.ext
    exact (slotEquiv bits).symm_apply_apply x.val
  right_inv yx := by
    rcases yx with ⟨y,x⟩
    have he := (slotEquiv bits).apply_symm_apply (x.val,y)
    apply Sigma.ext (congrArg Prod.snd he)
    have hr : rightSlot bits (joinSlot bits x.val y)=y := congrArg Prod.snd he
    apply (Subtype.heq_iff_coe_eq (by
      intro a
      change a∉Set.range ((rowFamily bits H (rightSlot bits (joinSlot bits x.val y))).position t) ↔ _
      rw [hr])).mpr
    exact congrArg Prod.fst he

def columnFreeEquiv (t : Fin (n+1)) : FreeSlot H (rightTime t) ≃
    Σx : GridSlot (leftBits bits), FreeSlot (columnFamily bits H x) t where
  toFun y := ⟨leftSlot bits y.val,⟨rightSlot bits y.val,by
    rintro ⟨a,ha⟩
    let k := (Fintype.equivFin (ColumnLabels bits H (leftSlot bits y.val))).symm a
    apply y.property
    refine ⟨k.val,?_⟩
    apply (slotEquiv bits).injective
    apply Prod.ext
    · exact (leftSlot_rightTime bits H t k.val).trans k.property
    · exact ha⟩⟩
  invFun xy := ⟨joinSlot bits xy.1 xy.2.val,by
    rintro ⟨k,hk⟩
    have he := congrArg (slotEquiv bits) hk
    have hl : leftSlot bits (H.position (rightTime (m:=m) 0) k)=xy.1 := by
      rw [←leftSlot_rightTime bits H t k]
      exact (congrArg Prod.fst he).trans (congrArg Prod.fst ((slotEquiv bits).apply_symm_apply (xy.1,xy.2.val)))
    apply xy.2.property
    refine ⟨Fintype.equivFin (ColumnLabels bits H xy.1) ⟨k,hl⟩,?_⟩
    simp only [columnFamily,Equiv.symm_apply_apply]
    exact (congrArg Prod.snd he).trans (congrArg Prod.snd ((slotEquiv bits).apply_symm_apply (xy.1,xy.2.val)))⟩
  left_inv y := by
    apply Subtype.ext
    exact (slotEquiv bits).symm_apply_apply y.val
  right_inv xy := by
    rcases xy with ⟨x,y⟩
    have he := (slotEquiv bits).apply_symm_apply (x,y.val)
    apply Sigma.ext (congrArg Prod.fst he)
    have hl : leftSlot bits (joinSlot bits x y.val)=x := congrArg Prod.fst he
    apply (Subtype.heq_iff_coe_eq (by
      intro a
      change a∉Set.range ((columnFamily bits H (leftSlot bits (joinSlot bits x y.val))).position t) ↔ _
      rw [hl])).mpr
    exact congrArg Prod.snd he

abbrev RowSamples := ∀y, ConditionalChoices (rowFamily bits H y)
abbrev ColumnSamples := ∀x, ConditionalChoices (columnFamily bits H x)

def rowRemaining (g : RowSamples bits H) : FreeSlot H 0 ≃ FreeSlot H (rightTime (m:=m) 0) :=
  (rowFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun y =>
    remainingBijection (rowFamily bits H y) (g y).val (g y).property)).trans
    (rowFreeEquiv bits H (Fin.last m)).symm)

def columnRemaining (g : ColumnSamples bits H) :
    FreeSlot H (rightTime (m:=m) 0) ≃ FreeSlot H (Fin.last (m+n)) :=
  (columnFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun x =>
    remainingBijection (columnFamily bits H x) (g x).val (g x).property)).trans
    (columnFreeEquiv bits H (Fin.last n)).symm)

@[simp] lemma rowRemaining_val (g : RowSamples bits H) (a : FreeSlot H 0) :
    (rowRemaining bits H g a).val = joinSlot bits
      (gridSweep (leftBits bits) (g (rightSlot bits a.val)).val (leftSlot bits a.val))
      (rightSlot bits a.val) := rfl

@[simp] lemma columnRemaining_val (g : ColumnSamples bits H)
    (a : FreeSlot H (rightTime (m:=m) 0)) :
    (columnRemaining bits H g a).val = joinSlot bits (leftSlot bits a.val)
      (gridSweep (rightBits bits) (g (leftSlot bits a.val)).val (rightSlot bits a.val)) := rfl

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

def rowReference : FreeSlot H 0 ≃ FreeSlot H (rightTime (m:=m) 0) :=
  (rowFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun y =>
    freeIdentification (rowFamily bits H y))).trans
    (rowFreeEquiv bits H (Fin.last m)).symm)

def columnReference : FreeSlot H (rightTime (m:=m) 0) ≃ FreeSlot H (Fin.last (m+n)) :=
  (columnFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun x =>
    freeIdentification (columnFamily bits H x))).trans
    (columnFreeEquiv bits H (Fin.last n)).symm)

def rowRelative (g : RowSamples bits H) : Equiv.Perm (FreeSlot H 0) :=
  (rowRemaining bits H g).trans (rowReference bits H).symm

def columnRelative (g : ColumnSamples bits H) : Equiv.Perm (FreeSlot H (rightTime (m:=m) 0)) :=
  (columnRemaining bits H g).trans (columnReference bits H).symm

def framePermutation : Equiv.Perm (FreeSlot H 0) :=
  ((rowReference bits H).trans (columnReference bits H)).trans (freeIdentification H).symm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)

def rowAverage (z : ℝ) : V →ₗ[ℂ] V :=
  ∑g : RowSamples bits H,
    ((∏y, conditionalChoiceWeight (rowFamily bits H y) z (g y)):ℂ) • ρ (rowRelative bits H g)

def columnAverage (z : ℝ) : V →ₗ[ℂ] V :=
  ∑g : ColumnSamples bits H,
    ((∏x, conditionalChoiceWeight (columnFamily bits H x) z (g x)):ℂ) •
      ρ ((rowReference bits H).symm.permCongr (columnRelative bits H g))

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I : Type*} [Fintype I] [LinearOrder I]
  {X : I → Type*} [∀i,Fintype (X i)] {N : ℕ}

omit [LinearOrder I] in
theorem groupingCard (e : (Σi, X i) ≃ Fin N) :
    Fintype.card (Σₗ i, Fin (Fintype.card (X i)))=N := by
  change Fintype.card (Σi, Fin (Fintype.card (X i)))=N
  have he := Fintype.card_congr e
  simpa only [Fintype.card_sigma,Fintype.card_fin] using he

def groupingOrder (e : (Σi, X i) ≃ Fin N) :
    (Σₗ i, Fin (Fintype.card (X i))) ≃o Fin N :=
  (Fintype.orderIsoFinOfCardEq _ (groupingCard e)).symm

def groupingPerm (e : (Σi, X i) ≃ Fin N) : Equiv.Perm (Fin N) :=
  ((groupingOrder e).symm.toEquiv.trans ofLex).trans
    ((Equiv.sigmaCongrRight (fun i => (Fintype.equivFin (X i)).symm)).trans e)

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridChildAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

namespace GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

def rowInputEquiv : FreeSlot H 0 ≃
    Σy : GridSlot (rightBits bits), FreeSlot (rowFamily bits H y) 0 := rowFreeEquiv bits H 0

end GridSplit
end BinaryCoordinateSweeps

namespace BinaryCoordinateSweeps.GridSplit
open Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

local instance rowOrder : LinearOrder (GridSlot (rightBits bits)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
local instance columnOrder : LinearOrder (GridSlot (leftBits bits)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

abbrev Junction := FreeSlot H (rightTime (m:=m) 0)
abbrev junctionSize := Fintype.card (Junction bits H)

def junctionEnum : Junction bits H ≃ Fin (junctionSize bits H) := Fintype.equivFin _

def physicalBoard : Fin (junctionSize bits H) ↪
    GridSlot (rightBits bits) × GridSlot (leftBits bits) where
  toFun t := (rightSlot bits ((junctionEnum bits H).symm t).val,
    leftSlot bits ((junctionEnum bits H).symm t).val)
  inj' := by
    intro t u he
    apply (junctionEnum bits H).symm.injective
    apply Subtype.ext
    apply (slotEquiv bits).injective
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

def rowGrouping : (Σy : GridSlot (rightBits bits), FreeSlot (rowFamily bits H y) 0) ≃
    Fin (junctionSize bits H) :=
  (rowInputEquiv bits H).symm.trans ((rowReference bits H).trans (junctionEnum bits H))

def columnGrouping : (Σx : GridSlot (leftBits bits), FreeSlot (columnFamily bits H x) 0) ≃
    Fin (junctionSize bits H) :=
  (columnFreeEquiv bits H 0).symm.trans (junctionEnum bits H)

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I A : Type*} [Fintype I] [LinearOrder I] [Fintype A] [DecidableEq A]
  {X : I → Type*} [∀i,Fintype (X i)] {N : ℕ}

def finBlockPermEquiv : (∀i, Equiv.Perm (X i)) ≃
    (∀i, Equiv.Perm (Fin (Fintype.card (X i)))) :=
  Equiv.piCongrRight (fun i => (Fintype.equivFin (X i)).permCongr)

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridBoardAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Signed Irrep Representation

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A]

local instance instLinearOrderGridSlotRightBits : LinearOrder (GridSlot (rightBits bits)) := rowOrder bits
local instance instLinearOrderGridSlotLeftBits : LinearOrder (GridSlot (leftBits bits)) := columnOrder bits

def inputToJunction : FreeSlot H 0 ≃ Fin (junctionSize bits H) :=
  (rowReference bits H).trans (junctionEnum bits H)

def junctionTensorRep (p : A → Bool) :
    Representation ℂ (Equiv.Perm (FreeSlot H 0)) (TensorSpace A (junctionSize bits H)) :=
  (hilbertTensorRep p (junctionSize bits H)).comp
    (inputToJunction bits H).permCongrHom.toMonoidHom

def rowChildWeight (z : ℝ) (y : GridSlot (rightBits bits))
    (a : Equiv.Perm (Fin (Fintype.card (FreeSlot (rowFamily bits H y) 0)))) : ℂ :=
  conditionalGroupLaw (rowFamily bits H y) z ((Fintype.equivFin _).symm.permCongr a)

def columnChildWeight (z : ℝ) (x : GridSlot (leftBits bits))
    (a : Equiv.Perm (Fin (Fintype.card (FreeSlot (columnFamily bits H x) 0)))) : ℂ :=
  conditionalGroupLaw (columnFamily bits H x) z ((Fintype.equivFin _).symm.permCongr a)

def rowMatrix (p : A → Bool) (z : ℝ) :=
  groupedAverage (groupingOrder (rowGrouping bits H)) (groupingPerm (rowGrouping bits H)) p
    (rowChildWeight bits H z)

def columnMatrix (p : A → Bool) (z : ℝ) :=
  groupedAverage (groupingOrder (columnGrouping bits H)) (groupingPerm (columnGrouping bits H)) p
    (columnChildWeight bits H z)

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridProjectedMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed TraceHolder Density

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A]

def junctionAverage (p : A → Bool) (z : ℝ) :=
  sampleMatrix p (fun a => (conditionalGroupLaw H z a:ℂ)) (inputToJunction bits H).permCongr

def junctionFrame (p : A → Bool) :=
  actionMatrix p ((inputToJunction bits H).permCongr (framePermutation bits H))

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.Signed
open Irrep Representation TraceHolder

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [LinearOrder I] [Nonempty I] [Fintype J] [LinearOrder J]
  {n : I → ℕ} {m : J → ℕ} {N : ℕ}

def typeF {n : ℕ} (α : n.Partition) : ℝ := Real.log (Module.finrank ℂ (Young.PartitionHilbert α):ℝ)

def blockLogSize {I : Type*} [Fintype I] (n : I → ℕ) : ℝ := ∑i, Real.log (n i+1:ℝ)

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookHilbertOccurrence
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
open Representation Irrep Signed

variable {N p : ℕ} (α : N.Partition) (h : InHook (diagram α) p)

variable (μ : YoungDiagram) (hμ : InHook μ p) (e : Cell μ ≃ Fin N)
def hookHilbertMapAt : IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
    (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N) where
  toLinearMap := (coeffEquiv (Bool × Fin p) N).symm.toLinearMap.comp
    ((hookMap hμ e).toLinearMap.comp (spechtHilbertEquiv μ).symm.toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply (coeffEquiv (Bool × Fin p) N).injective
    change hookMap hμ e
      ((spechtHilbertEquiv μ).symm (((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) g v)) =
        tensorRep Prod.fst N g (hookMap hμ e ((spechtHilbertEquiv μ).symm v))
    have he := LinearMap.congr_fun ((hookMap hμ e).isIntertwining'
      (e.symm.permCongr g)) ((spechtHilbertEquiv μ).symm v)
    have hg : e.permCongr (e.symm.permCongr g)=g := by
      ext t; simp [Equiv.permCongr_apply]
    change hookMap hμ e
      ((spechtHilbertEquiv μ).symm ((spechtHilbertEquiv μ)
        (spechtRep μ (e.symm.permCongr g)
          ((spechtHilbertEquiv μ).symm v)))) = _
    rw [LinearEquiv.symm_apply_apply]
    change hookMap hμ e
      (spechtRep μ (e.symm.permCongr g)
        ((spechtHilbertEquiv μ).symm v)) =
      tensorRep Prod.fst N (e.permCongr (e.symm.permCongr g))
        (hookMap hμ e ((spechtHilbertEquiv μ).symm v)) at he
    rw [hg] at he
    exact he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridSplitCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed TraceHolder Density

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance instLinearOrderGridSlotRightBits_2 : LinearOrder (GridSlot (rightBits bits)) := rowOrder bits
local instance instLinearOrderGridSlotLeftBits_2 : LinearOrder (GridSlot (leftBits bits)) := columnOrder bits

def rowFreeSize (y : GridSlot (rightBits bits)) := Fintype.card (FreeSlot (rowFamily bits H y) 0)
def columnFreeSize (x : GridSlot (leftBits bits)) := Fintype.card (FreeSlot (columnFamily bits H x) 0)

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridDenseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace BinaryCoordinateSweeps

def inductionGap (s : ℝ) : ℝ := 1 / (20 * Real.sqrt (Real.log s))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_PhysicalHookInduced
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (μ : YoungDiagram) (p : ℕ) (e : Cell μ ≃ FreeSlot H 0)

def hookPlacementBasis : Cell (hookPart μ p) ⊕ Fin (Fintype.card (Cell (southeast μ p))) ≃ FreeSlot H 0 :=
  ((Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Cell (southeast μ p))).symm).trans
    (cutEquiv μ p)).trans e

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DenseAssembly
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Irrep Representation Young GridSplit Signed

def EnumeratedMomentBound (q : ℕ) {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) : Prop :=
  ∀ h : ℕ, ∀ H : PathFamily bits h, ∀ α : (Fintype.card (FreeSlot H 0)).Partition,
    evenMoment q (groupAverage (partitionHilbertRep α)
      (fun a => (conditionalGroupLaw H z ((Fintype.equivFin _).symm.permCongr a):ℂ))) ≤
      Real.exp (-cExponent (gridSize bits)*typeF α+
        eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H)

def diagramF (μ : YoungDiagram) : ℝ := Real.log (Module.finrank ℂ (SpechtSpace μ))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTranspose
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

def signTwist (ρ : Representation ℂ (G μ) V) : Representation ℂ (G μ) V where
  toFun g := signC μ g • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    rw [mul_comm]

def signTwistSubrep (ρ : Representation ℂ (G μ) V) :
    Subrepresentation ρ ≃o Subrepresentation (signTwist μ ρ) where
  toFun U := ⟨U.toSubmodule, fun g v hv => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv)⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.toSubmodule.smul_mem (signC μ g) (U.apply_mem_toSubmodule g hv)
    change signC μ g • (signC μ g • ρ g v) ∈ U.toSubmodule at h
    rwa [smul_smul, signC_sq, one_smul] at h⟩
  left_inv U := rfl
  right_inv U := rfl
  map_rel_iff' := Iff.rfl

instance signTwist_irreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G μ) V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := G μ) (V := V) (signTwist μ ρ) :=
  (signTwistSubrep μ ρ).isSimpleOrder_iff.mp inferInstance

def transposeCells : Cell μ ≃ Cell μ.transpose where
  toFun x := ⟨x.val.swap, YoungDiagram.mem_transpose.mpr (by simp)⟩
  invFun x := ⟨x.val.swap, YoungDiagram.mem_transpose.mp x.property⟩
  left_inv x := by apply Subtype.ext; exact Prod.swap_swap _
  right_inv x := by apply Subtype.ext; exact Prod.swap_swap _

def transposeRep : Representation ℂ (G μ) (SpechtSpace μ.transpose) :=
  (spechtRep μ.transpose).comp (transposeCells μ).permCongrHom.toMonoidHom

def transposeMap : SpechtSpace μ →ₗ[ℂ] SpechtSpace μ.transpose :=
  (fromTabloid μ (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (spechtPoly μ.transpose)).comp (spechtInclude μ)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.Young
open Irrep Signed

def minTail (μ : YoungDiagram) : ℕ := min (Fintype.card (Cell μ)-μ.rowLen 0)
  (Fintype.card (Cell μ)-μ.colLen 0)

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Filter

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxis
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

instance oneAxisOutsideEmpty : IsEmpty {i : Fin 1 // i ≠ 0} :=
  ⟨fun i => i.property (Subsingleton.elim _ _)⟩

noncomputable def oneAxisSlotEquiv (bits : Fin 1 → ℕ) : GridSlot bits ≃ Slot (bits 0) :=
  Equiv.piUnique _
noncomputable def oneAxisChoiceEquiv (bits : Fin 1 → ℕ) :
    GridChoices bits ≃ Equiv.Perm (Slot (bits 0)) :=
  (Equiv.piUnique _).trans (Equiv.funUnique _ _)
noncomputable def oneAxisSweepEquiv (bits : Fin 1 → ℕ) :
    GridChoices bits ≃ Equiv.Perm (GridSlot bits) :=
  (oneAxisChoiceEquiv bits).trans ((oneAxisSlotEquiv bits).symm.permCongr)

lemma oneAxisSweepEquiv_apply (bits : Fin 1 → ℕ) (g : GridChoices bits) :
    oneAxisSweepEquiv bits g = gridSweep bits g := by
  apply Equiv.ext
  intro x
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [gridSweep, List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  change _ = gridLayer bits g 0 x 0
  simp only [oneAxisSweepEquiv, oneAxisChoiceEquiv, oneAxisSlotEquiv, Equiv.trans_apply,
    Equiv.permCongr_apply, Equiv.piUnique_apply,
    Equiv.funUnique_apply, gridLayer, Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply,
    Equiv.piSplitAt_symm_apply, dite_true, eq_self]
  simp only [Equiv.symm_symm, Equiv.piUnique_symm_apply, Equiv.piUnique_apply]
  have aux (y : GridOutside bits default) (i : Fin 1) :
      uniqueElim (α := fun j => Slot (bits j)) ((g default y) (x default)) i =
      (g i (fun j => x j.val)) (x i) := by
    obtain rfl := Unique.eq_default i
    rw [uniqueElim_default]
    apply congrArg (fun y : GridOutside bits default => g default y (x default))
    funext j
    exact (j.property (Subsingleton.elim _ _)).elim
  exact aux _ 0

lemma oneAxis_pathEvent_iff {h : ℕ} {bits : Fin 1 → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : pathEvent H g ↔
      ∀ k, gridSweep bits g (H.position 0 k) = H.position (Fin.last 1) k := by
  constructor
  · exact fun hg k => gridSweep_path H g hg k
  · intro hg j k
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa [gridSweep, List.ofFn_succ] using hg k

def assignmentResidualEquiv {X I : Type*} [Fintype X] [Fintype I]
    (A B : I ↪ X) (c : {x : X // x ∉ Set.range A} ≃ {x : X // x ∉ Set.range B}) :
    {σ : Equiv.Perm X // Assigns A B σ} ≃ Equiv.Perm {x : X // x ∉ Set.range A} := by
  classical
  let eA := Equiv.ofInjective A A.injective
  let eB := Equiv.ofInjective B B.injective
  let e₀ : Set.range A ≃ Set.range B := eA.symm.trans eB
  let e : {σ : Equiv.Perm X // Assigns A B σ} ≃
      {σ : X ≃ X // ∀ x : Set.range A, σ x = e₀ x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro σ
      constructor
      · intro hs x
        obtain ⟨i, hi⟩ := x.property
        have hx : x = eA i := Subtype.ext hi.symm
        rw [hx]
        simpa [e₀, eA, eB] using hs i
      · intro hs i
        simpa [e₀, eA, eB] using hs (eA i))
  exact (e.trans (Equiv.Set.compl e₀)).trans (Equiv.equivCongr (Equiv.refl _) c.symm)

def oneAxisRemainingEquiv {h : ℕ} {bits : Fin 1 → ℕ} (H : PathFamily bits h) :
    {g : GridChoices bits // pathEvent H g} ≃ Equiv.Perm (FreeSlot H 0) := by
  let A : Fin h ↪ GridSlot bits := ⟨H.position 0, H.disjoint 0⟩
  let B : Fin h ↪ GridSlot bits := ⟨H.position (Fin.last 1), H.disjoint _⟩
  exact (Equiv.subtypeEquiv (oneAxisSweepEquiv bits) (by
    intro g
    simpa only [Assigns, oneAxisSweepEquiv_apply, A, B, Function.Embedding.coeFn_mk] using oneAxis_pathEvent_iff H g)).trans
      (assignmentResidualEquiv A B (freeIdentification H))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_OneAxisBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

def oneAxisRadius (r : ℕ) : ℝ :=
  (2 * (((2^(2*r) : ℕ).factorial : ℝ))^2)⁻¹

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseAmplitude
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

 def placementEndpointArray (xy : Placement H k 0 × Placement H k (Fin.last b)) :
    Fin k → GridSlot bits × GridSlot bits := fun i => ((xy.1 i).val,(xy.2 i).val)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

section
attribute [local instance] Classical.propDecidable
variable {b h h' k : ℕ} {bits : Fin b → ℕ} {H : PathFamily bits h} {H' : PathFamily bits h'}

variable (H)
def signedPlacementEntry (z : ℝ) (x : Placement H k 0) (y : Placement H k (Fin.last b)) : ℝ :=
  ∑g : ConditionalChoices H, if placementBijection H k g x=y then
    conditionalChoiceWeight H z g*realSign (remainingPerm H g.val g.property) else 0

end

open Young Irrep

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def signedCenteredHS (k : ℕ) (z : ℝ) : ℝ := ∑x : Placement H k 0, ∑y : Placement H k 0,
  ‖centeredMatrix (gridSize bits) (fun a => (conditionalGroupLaw H z a*realSign a:ℂ)) y x‖^2

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_FallingMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
open Polynomial

def fallingMoment (m h n : ℕ) : ℝ := (m:ℝ)^n / ((m-h).descFactorial n : ℝ)

@[simp] lemma fallingMoment_zero (m h : ℕ) : fallingMoment m h 0 = 1 := by
  simp [fallingMoment]

def lineMoment (m h : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => (fallingMoment m h n) • LinearMap.id)

def stein (m h : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (C ((m:ℝ)-h) * X)) -
    (LinearMap.mulLeft ℝ (X^2)).comp (Polynomial.derivative) -
    LinearMap.mulLeft ℝ (C (m:ℝ))

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def trackedLineCount (x : Placement H k 0) (g : ConditionalChoices H)
    (j : Fin b) (y : GridOutside bits j) : ℕ :=
  Fintype.card {i : Fin k // (fun a : {a : Fin b // a≠j} =>
    gridPartialSweep bits g.val j.castSucc (x i).val a)=y}

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_CenteredLineMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
open Polynomial

def centeredLineMoment (m h u v : ℕ) : ℝ :=
  lineMoment m h (X^v*(X-1)^u)

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_LightLineBound
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

variable {L : Type*} [Fintype L]

def multilineMoment (m h : L → ℕ) : MvPolynomial L ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials L ℝ).constr ℝ
    (fun n => ∏ l, fallingMoment (m l) (h l) (n l))

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_OccurrenceMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

def occurrences (f : A → L) (l : L) : ℕ := Fintype.card {a : A // f a = l}

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointValidity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ}

variable {I : Type*} [Fintype I] [DecidableEq I] (H : PathFamily bits h)

def EndpointValid (A : Finset I) (e : I → GridSlot bits × GridSlot bits) : Prop :=
  (∀t, ∀i∈A, ∀a∈A, independentPosition (e i) t=independentPosition (e a) t → i=a) ∧
  (∀t, ∀i∈A, ∀k, independentPosition (e i) t≠H.position t k)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointFactors
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

abbrev EndpointLineIndex (bits : Fin b → ℕ) := Σj, GridOutside bits j

def endpointPathLine {I : Type*} (e : I → GridSlot bits × GridSlot bits)
    (i : I) (j : Fin b) : EndpointLineIndex bits := ⟨j,endpointLine (e i) j⟩

def endpointLineCount {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) : ℕ :=
  Fintype.card {i : A // endpointLine (e i) j=y}

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I R : Type*} [DecidableEq I] [CommRing R]

def mobiusSum (U : Finset I) (f : Finset I → R) : R :=
  ∑A ∈ U.powerset, (-1:R)^(U.card-A.card)*f A

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathTelescope
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

section

variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

abbrev Suffixes {b : ℕ} (c : A → Fin b) := (a : A) × {j : Fin b // c a<j}

def centeredLine {b : ℕ} (f : A → Fin b → L) (c : A → Fin b) : A → L := fun a => f a (c a)

def suffixLine {b : ℕ} (f : A → Fin b → L) (c : A → Fin b) : Suffixes c → L :=
  fun a => f a.1 a.2

end

variable {L A B C : Type*} [Fintype L] [Fintype A] [Fintype B] [Fintype C]

variable {b : ℕ}

def telescopeInjection (c : A → Fin b) : A ⊕ (B ⊕ Suffixes c) → B ⊕ (A × Fin b)
  | .inl a => .inr (a,c a)
  | .inr (.inl k) => .inl k
  | .inr (.inr a) => .inr (a.1,a.2)

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathMomentMixed
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
variable {I : Type*} [Fintype I] [DecidableEq I]

def endpointPathPolynomial (e : I → GridSlot bits × GridSlot bits) (i : I) :
    MvPolynomial (EndpointLineIndex bits) ℝ := ∏j, MvPolynomial.X (endpointPathLine e i j)

def vertexIsolated (e : I → GridSlot bits × GridSlot bits) (i : I) : Prop :=
  (∀t a, independentPosition (e i) t≠H.position t a) ∧
  (∀t a, a≠i → independentPosition (e a) t≠independentPosition (e i) t)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointEntryBound
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def endpointLight (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits)
    (l : EndpointLineIndex bits) : Prop :=
  (lineHoles H l.1 l.2:ℝ)+endpointLineCount Finset.univ e l.1 l.2 ≤ (2^bits l.1:ℕ)*η

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SparseOccupancy
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω L : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable [Fintype L] [DecidableEq L]

def smallSetEncode {r : ℕ} (S : {S : Finset L // S.card ≤ r}) : Fin r → Option L :=
  fun i => if h : i.val < S.val.card then
    some ((Fintype.equivFin S.val).symm ⟨i.val,by simpa using h⟩).val else none

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointOccupancy
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def holeHeavyLines (j : Fin b) (η : ℝ) : Finset (GridOutside bits j) :=
  Finset.univ.filter (fun l => (2^bits j:ℕ)*η/2<(lineHoles H j l:ℝ))

def particleHeavyLines (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) (η : ℝ) :
    Finset (GridOutside bits j) :=
  Finset.univ.filter (fun l => (2^bits j:ℕ)*η/2<(endpointLineCount Finset.univ e j l:ℝ))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointGood
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def endpointVertexIncident (e : Fin k → GridSlot bits × GridSlot bits) : Finset (Fin k) :=
  incidentSet shareVertex (fun a => (H.position 0 a,H.position (Fin.last b) a)) e

def endpointGoodSet (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i∉endpointVertexIncident H e ∧
    ∀j, endpointLight H η e (endpointPathLine e i j))

def endpointHoleBad (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => endpointLine (e i) j∈holeHeavyLines H j η)

def endpointParticleBad (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => endpointLine (e i) j∈particleHeavyLines e j η)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_FewSparse
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps

instance finitePathFamily {b h : ℕ} {bits : Fin b → ℕ} : Finite (PathFamily bits h) :=
  Finite.of_injective PathFamily.position (by
    intro H J he
    cases H
    cases J
    cases he
    rfl)

def sparseEndpointBound {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (k : ℕ) (z : ℝ) : Prop :=
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) ≤
        Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000) ∧
    signedCenteredHS H k z ≤ Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_ManySparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse Young Irrep

def mainMomentPower : ℕ := 8000000000000

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_MainMomentInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep Representation Signed

def SpechtMomentBound (q : ℕ) {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) : Prop :=
  ∀h : ℕ, ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
  evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
    (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
    Real.exp (-cExponent (gridSize bits)*diagramF μ+
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_EmptyGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

def emptyPaths : PathFamily bits 0 where
  position _ k := k.elim0
  disjoint _ := fun k => k.elim0
  changes_only_stage _ k := k.elim0

def emptyFree (t : Fin (b+1)) : FreeSlot (emptyPaths bits) t ≃ GridSlot bits where
  toFun := Subtype.val
  invFun x := ⟨x,by rintro ⟨k,_⟩; exact k.elim0⟩
  left_inv _ := rfl
  right_inv _ := rfl

def emptyFrame : Equiv.Perm (GridSlot bits) :=
  (emptyFree bits (Fin.last b)).symm.trans
    ((freeIdentification (emptyPaths bits)).symm.trans (emptyFree bits 0))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Analytic_AnalyticTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped Topology
open Set Complex Complex.HadamardThreeLines

namespace BinaryCoordinateSweeps

def ellipseMap (v : ℝ) (z : ℂ) : ℂ := (v:ℂ)/2*(Complex.cosh z+1)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_FiniteLawAverage
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

def pushLaw {A B : Type*} [Fintype A] (p : A → ℝ) (f : A → B) (b : B) : ℝ :=
  ∑a, if f a=b then p a else 0

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_BoardLaw
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open GridSplit

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

abbrev BoardChoices (X Y : Type*) := (Y → Equiv.Perm X) × (X → Equiv.Perm Y)
def boardWeight (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ)
    (LR : BoardChoices X Y) : ℝ := (∏y,p (LR.1 y))*(∏x,q (LR.2 x))
def boardSweep (LR : BoardChoices X Y) : Equiv.Perm (X×Y) :=
  columnPerm LR.2 * rowPerm LR.1
def boardLaw (p : Equiv.Perm X → ℝ) (q : Equiv.Perm Y → ℝ) : Equiv.Perm (X×Y) → ℝ :=
  pushLaw (boardWeight p q) boardSweep

variable {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X'] [DecidableEq Y']

def boardChoicesEquiv (e : X ≃ X') (f : Y ≃ Y') : BoardChoices X Y ≃ BoardChoices X' Y' :=
  Equiv.prodCongr (f.arrowCongr e.permCongr) (e.arrowCongr f.permCongr)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinarySplitChoices
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.BinarySplit
variable {m n : ℕ}

def fillSlot {d : ℕ} (j : Fin d) (u : {i : Fin d // i≠j} → Bool) : Slot d :=
  (Equiv.piSplitAt j (fun _ => Bool)).symm (false,u)

lemma fillSlot_other {d : ℕ} (j : Fin d) (u : {i : Fin d // i≠j} → Bool)
    (i : Fin d) (hi : i≠j) : fillSlot j u i=u ⟨i,hi⟩ := by
  simp [fillSlot,Equiv.piSplitAt,hi]

def leftOutsideEquiv (j : Fin m) :
    ({i : Fin (m+n) // i≠j.castAdd n} → Bool) ≃ Slot n × ({i : Fin m // i≠j} → Bool) where
  toFun u := (fun i => u ⟨i.natAdd m,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.castAdd n,fun h => i.property (Fin.ext (congrArg (fun q:Fin (m+n) => q.val) h))⟩)
  invFun yu i := Fin.addCases (fillSlot j yu.2) yu.1 i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.castAdd n) h)
      simp only [Fin.addCases_left,fillSlot_other _ _ _ hij]
    | right i => intro hi; simp only [Fin.addCases_right]
  right_inv yu := by
    apply Prod.ext
    · funext i
      simp only [Fin.addCases_right]
    · funext i
      simp only [Fin.addCases_left,fillSlot_other _ _ _ i.property]

def rightOutsideEquiv (j : Fin n) :
    ({i : Fin (m+n) // i≠j.natAdd m} → Bool) ≃ Slot m × ({i : Fin n // i≠j} → Bool) where
  toFun u := (fun i => u ⟨i.castAdd n,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.natAdd m,fun h => i.property (Fin.ext (by have hh := congrArg (fun q:Fin (m+n) => q.val) h; simpa using hh))⟩)
  invFun xu i := Fin.addCases xu.1 (fillSlot j xu.2) i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i => intro hi; simp only [Fin.addCases_left]
    | right i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.natAdd m) h)
      simp only [Fin.addCases_right,fillSlot_other _ _ _ hij]
  right_inv xu := by
    apply Prod.ext
    · funext i
      simp only [Fin.addCases_left]
    · funext i
      simp only [Fin.addCases_right,fillSlot_other _ _ _ i.property]

def rowChoices (g : SweepCoins (m+n)) (y : Slot n) : SweepCoins m :=
  fun j u => g (j.castAdd n) ((leftOutsideEquiv j).symm (y,u))
def columnChoices (g : SweepCoins (m+n)) (x : Slot m) : SweepCoins n :=
  fun j u => g (j.natAdd m) ((rightOutsideEquiv j).symm (x,u))

def joinChoices (L : Slot n → SweepCoins m)
    (R : Slot m → SweepCoins n) : SweepCoins (m+n) :=
  Fin.addCases (fun j u => L ((leftOutsideEquiv j) u).1 j ((leftOutsideEquiv j) u).2)
    (fun j u => R ((rightOutsideEquiv j) u).1 j ((rightOutsideEquiv j) u).2)

def choicesEquiv : SweepCoins (m+n) ≃
    (Slot n → SweepCoins m) ×
    (Slot m → SweepCoins n) where
  toFun g := (rowChoices g,columnChoices g)
  invFun LR := joinChoices LR.1 LR.2
  left_inv g := by
    funext j u
    induction j using Fin.addCases with
    | left j => simp [joinChoices,rowChoices]
    | right j => simp [joinChoices,columnChoices]
  right_inv LR := by
    apply Prod.ext
    · funext y j u
      simp [rowChoices,joinChoices]
    · funext x j u
      simp [columnChoices,joinChoices]

end BinaryCoordinateSweeps.BinarySplit

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open GridSplit

def gridLaw {b : ℕ} (bits : Fin b → ℕ) : Equiv.Perm (GridSlot bits) → ℝ :=
  pushLaw (gridWeight bits 1) (gridSweep bits)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_LongRowDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

def longRowCells : Fin (μ.rowLen 0-μ.rowLen 1) ↪ Cell μ where
  toFun j := ⟨(0,μ.rowLen 1+j.val),YoungDiagram.mem_iff_lt_rowLen.mpr (by
    have hj := j.isLt
    have hm := μ.rowLen_anti 0 1 (by omega)
    omega)⟩
  inj' i j := by
    intro he
    apply Fin.ext
    have hh := congrArg (fun x : Cell μ => x.val.2) he
    dsimp at hh
    omega

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

def flatTail (μ : YoungDiagram) : ℕ := μ.card-max (μ.colLen 0) (μ.rowLen 0)
def longOriented (μ : YoungDiagram) : YoungDiagram :=
  if μ.colLen 0 ≤ μ.rowLen 0 then μ else μ.transpose

lemma rowLens_sum (μ : YoungDiagram) : μ.rowLens.sum=μ.card := by
  have h := card_cellsOfRowLens μ.rowLens
  change (YoungDiagram.ofRowLens μ.rowLens μ.rowLens_sorted).card=_ at h
  rw [YoungDiagram.ofRowLens_to_rowLens_eq_self] at h
  exact h.symm

lemma rowLens_head (μ : YoungDiagram) : μ.rowLens.headD 0=μ.rowLen 0 := by
  by_cases h : μ.colLen 0=0
  · have hr : μ.rowLen 0=0 := by
      by_contra hn
      have hm : (0,0)∈μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
      omega
    simp [YoungDiagram.rowLens,h,hr]
  · obtain ⟨a,ha⟩ : ∃a, μ.colLen 0=a+1 := ⟨μ.colLen 0-1,by omega⟩
    simp [YoungDiagram.rowLens,ha,List.range_succ_eq_map]

lemma rowLens_tail_sum (μ : YoungDiagram) : μ.rowLens.tail.sum=μ.card-μ.rowLen 0 := by
  have hh : μ.rowLens.headD 0+μ.rowLens.tail.sum=μ.rowLens.sum := by
    cases μ.rowLens <;> simp
  rw [rowLens_head,rowLens_sum] at hh
  omega

lemma longOriented_card (μ : YoungDiagram) : (longOriented μ).card=μ.card := by
  unfold longOriented
  split <;> simp_all

lemma longOriented_row (μ : YoungDiagram) :
    (longOriented μ).rowLen 0=max (μ.colLen 0) (μ.rowLen 0) := by
  unfold longOriented
  split <;> simp_all [YoungDiagram.rowLen_transpose,Nat.le_of_lt]

def tailCode {n k : ℕ} (p : {p : n.Partition // flatTail (diagram p)=k}) :
    Bool × Composition k :=
  (decide ((diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0),
    ⟨(longOriented (diagram p.val)).rowLens.tail,
      fun {i} hi => YoungDiagram.pos_of_mem_rowLens _ _ (List.mem_of_mem_tail hi),by
        rw [rowLens_tail_sum,longOriented_card,longOriented_row]
        exact p.property⟩)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_DimensionSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

def dimensionInv {n : ℕ} (p : n.Partition) : ℝ :=
  ((Module.finrank ℂ (PartitionHilbert p):ℝ)^8)⁻¹

def dimensionFiber (n k : ℕ) : ℝ := if k=0 then 0 else
  ∑p : {p : n.Partition // flatTail (diagram p)=k},dimensionInv p.val

def dimensionSeries (n : ℕ) : ℝ :=
  ∑p : n.Partition, if flatTail (diagram p)=0 then 0 else dimensionInv p

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Mixing_BinaryMixingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Young

def binarySlotsFin (d : ℕ) : Slot d ≃ Fin (2^d) :=
  Fintype.equivOfCardEq (by simp [Slot])

end BinaryCoordinateSweeps

end

namespace BinaryCoordinateSweeps

def BinaryMainTarget : Prop := BinaryContractionTarget ∧
    (∀ d : ℕ, 0 < d → ∑ g : Equiv.Perm (Slot d),
      binaryLaw d g * realSign g = 0) ∧ UniformSweepMixingTarget
end BinaryCoordinateSweeps

open scoped BigOperators Classical

end

end OAI
end


