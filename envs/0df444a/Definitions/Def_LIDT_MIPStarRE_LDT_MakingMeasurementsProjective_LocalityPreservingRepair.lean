-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:35:18.515241+00:00
-- url     : https://prove2.me/theorems/23ec6a89-7598-4d89-8e92-4e1d96e324ec
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / LocalityPreservingRepair
-- statement:
--   This bundle defines the marginal blocks and locality-preserving repair data for the projectivization construction. It supplies left and right marginal densities and states, diagonal blocks, scalar error absorption, and the repaired left-lifted measurement estimate.
--
--   Principal definitions:
--   - `diagBlock`: extracts the diagonal block associated with an outcome sector.
--   - `leftMarginalDensity`: the left marginal density obtained from the bipartite state.
--   - `leftMarginalState`: the corresponding left marginal state.
--   - `rightDiagBlock`: the right-side diagonal block.
--   - `rightMarginalDensity`: the right marginal density.
--   - `rightMarginalState`: the corresponding right marginal state.
--   - `projectivizationRepair_small_error_bound`: absorbs the scalar error terms in the repair estimate.
--   - `leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul`: gives the locality-preserving repair for a left-lifted measurement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean#L58-L760

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.MakingMeasurementsProjective
end MIPStarRE.LDT.MakingMeasurementsProjective
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the locality-preserving repair route for the late Section 5
`Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationStatement_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require the spectral truncation statement should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepair`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the direct output of that route under a normalized
bipartite state and the source almost-projective estimate for the left-lifted
measurement. It is stated directly in terms of this estimate, rather than in
terms of a separate repair-input assumption, and provides the unconditional
repair step used by the orthonormalization theorem.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

private def diagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (b : ιB) :
    MIPStarRE.Quantum.Op ιA :=
  M.submatrix (fun i => (i, b)) (fun j => (j, b))

private def leftMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιA :=
  ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ b : ιB, diagBlock ρ b

private lemma leftMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ leftMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ b : ιB, diagBlock ρ b := by
    refine Finset.sum_nonneg fun b _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [diagBlock] using hρpsd.submatrix (fun i => (i, b))
  have hcoeff : 0 ≤ ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [leftMarginalDensity] using smul_nonneg hcoeff hsum

private def leftMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιA where
  density := leftMarginalDensity ψ.density
  density_psd := by
    exact leftMarginalDensity_nonneg ψ.density_psd

private lemma leftTensor_eq_blockDiagonal_const {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA) :
    leftTensor (ι₂ := ιB) X = Matrix.blockDiagonal (fun _ : ιB => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [leftTensor, Matrix.blockDiagonal_apply]
  · simp [leftTensor, Matrix.blockDiagonal_apply, h]

private lemma trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA)
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ιB => X) * M) =
      ∑ b : ιB, Matrix.trace (X * diagBlock M b) := by
  classical
  let e : ((ιA × ιB) × ιA) ≃ (ιB × (ιA × ιA)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [diagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιB × (ιA × ιA) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

private lemma normalizedTrace_leftMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * leftTensor (ι₂ := ιB) X) := by
  have hcard : ((Fintype.card ιB : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace leftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ιB, Matrix.trace (diagBlock ρ b * X) =
        ∑ b : ιB, Matrix.trace (X * diagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap]
  rw [Matrix.trace_mul_comm]
  rw [leftTensor_eq_blockDiagonal_const]
  rw [trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

private lemma leftMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (leftMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [leftTensor_one] using
      normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ιA))
  simpa [leftMarginalState] using hnorm.trans hψ

private lemma leftMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    ev ψ (leftTensor (ι₂ := ιB) X) = ev (leftMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    leftMarginalState]

 def rightDiagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (a : ιA) :
    MIPStarRE.Quantum.Op ιB :=
  M.submatrix (fun i => (a, i)) (fun j => (a, j))

 def rightMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιB :=
  ((((Fintype.card ιA : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ a : ιA, rightDiagBlock ρ a

private lemma rightMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ rightMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ a : ιA, rightDiagBlock ρ a := by
    refine Finset.sum_nonneg fun a _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [rightDiagBlock] using hρpsd.submatrix (fun i => (a, i))
  have hcoeff : 0 ≤ ((((Fintype.card ιA : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [rightMarginalDensity] using smul_nonneg hcoeff hsum

 def rightMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιB where
  density := rightMarginalDensity ψ.density
  density_psd := rightMarginalDensity_nonneg ψ.density_psd









/-- Scalar absorption used inside the locality-preserving projectivization repair.

Paper origin: `references/ldt-paper/orthonormalization.tex:862-1194`, where the
local \(Q/X/\widehat X/P\) construction is combined by the triangle inequality
and then absorbed into the displayed \(84\zeta^{1/4}\) envelope.

**Faithful encoding:** This is an internal scalar estimate for the proved
locality-preserving construction, not an additional hypothesis of the source
orthonormalization theorem. -/
 lemma projectivizationRepair_small_error_bound {ζ : Error}
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  have htrunc : spectralTruncationError ζ ≤ zetaQuarterRoot ζ :=
    spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  have hround : roundingToProjectiveError ζ ≤ 12 * zetaQuarterRoot ζ := by
    dsimp [roundingToProjectiveError]
    gcongr
    simpa [spectralTruncationError, zetaQuarterRoot] using htrunc
  calc
    2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ)
        ≤ 2 * (12 * zetaQuarterRoot ζ + 30 * zetaQuarterRoot ζ) := by
            gcongr
    _ = orthonormalizationMainLemmaError ζ := by
          dsimp [orthonormalizationMainLemmaError, zetaQuarterRoot]
          ring

 lemma roundingToProjectiveError_le_orthonormalizationMainLemmaError {ζ : Error}
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    roundingToProjectiveError ζ ≤ orthonormalizationMainLemmaError ζ := by
  have htrunc : spectralTruncationError ζ ≤ zetaQuarterRoot ζ :=
    spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  calc
    roundingToProjectiveError ζ ≤ 12 * zetaQuarterRoot ζ := by
      dsimp [roundingToProjectiveError]
      gcongr
      simpa [spectralTruncationError, zetaQuarterRoot] using htrunc
    _ ≤ orthonormalizationMainLemmaError ζ := by
      dsimp [orthonormalizationMainLemmaError, zetaQuarterRoot]
      exact mul_le_mul_of_nonneg_right (by norm_num : (12 : Error) ≤ 84)
        (zetaQuarterRoot_nonneg hζ)

 lemma one_le_orthonormalizationMainLemmaError_of_quarter_lt {ζ : Error}
    (hquarter_lt : (1 / (4 : Error)) < ζ) :
    1 ≤ orthonormalizationMainLemmaError ζ := by
  have hq_rpow_le :
      Real.rpow (1 / (4 : Error)) (1 / (4 : Error)) ≤
        Real.rpow ζ (1 / (4 : Error)) := by
    exact Real.rpow_le_rpow (by positivity) (le_of_lt hquarter_lt) (by positivity)
  have hquarter_le_rpow :
      (1 / (4 : Error)) ≤ Real.rpow (1 / (4 : Error)) (1 / (4 : Error)) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (show (1 / (4 : Error)) ≤ 1 by norm_num)
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (by norm_num : (1 / (4 : Error)) ≤ 1))
  have hquarter_le : (1 / (4 : Error)) ≤ Real.rpow ζ (1 / (4 : Error)) :=
    le_trans hquarter_le_rpow hq_rpow_le
  have hscaled : (84 : Error) * (1 / (4 : Error)) ≤ orthonormalizationMainLemmaError ζ := by
    dsimp [orthonormalizationMainLemmaError]
    exact mul_le_mul_of_nonneg_left hquarter_le (by norm_num)
  have hone : (1 : Error) ≤ (84 : Error) * (1 / (4 : Error)) := by norm_num
  exact hone.trans hscaled

 lemma matrix_eq_zero_of_rank_eq_zero {m n : Type*}
    [Finite m] [Fintype n] (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  let _ : Fintype m := Fintype.ofFinite m
  classical
  have hrange : A.mulVecLin.range = ⊥ := by
    rw [Matrix.rank] at hA
    exact Submodule.finrank_eq_zero.mp hA
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ A.mulVecLin.range := ⟨Pi.single j 1, rfl⟩
  have hv0 : A.mulVecLin (Pi.single j 1) = 0 := by
    simpa [hrange] using hv
  have hentry := congrArg (fun w => w i) hv0
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_ite_eq,
    Pi.single_apply] using hentry

private lemma sddRel_of_leftPlaced_sddOpRel {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    {ψ : QuantumState (ιA × ιB)} {A : Measurement Outcome ιA}
    {R : OpFamily Outcome ιA}
    {P : ProjSubMeas Outcome ιA}
    {δ : Error}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
        (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) R)
        δ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
      δ := by
  refine ⟨?_⟩
  have herror :
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)) =
        sddErrorOp ψ (uniformDistribution Unit)
          (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
          (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) R) := by
    unfold sddError sddErrorOp
    refine avgOver_congr (uniformDistribution Unit) _ _ ?_
    intro u
    unfold qSDD qSDDOp qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [constSubMeasFamily, leftPlacedSubMeas, SubMeas.toOpFamily,
      OpFamily.leftPlacedOpFamily, hR a]
  rw [herror]
  exact hclose.squaredDistanceBound





/-- Locality-preserving `Q/X/XHat/P` repair for a left-lifted measurement at the
paper's `2ζ` source-defect scale.

This is the sharp Section 5 repair route needed in the proof of
`thm:orthonormalization`: if the left-lifted source almost-projective defect is
bounded by `2 * ζ`, then the final local projective submeasurement is still
obtained with the paper's `84 * ζ^(1/4)` envelope.

Paper origin: `references/ldt-paper/orthonormalization.tex:862-1194`, recorded
for the scalar constant repair in
`docs/paper-gaps/issue-1032-orthonormalization-constant.tex`.

**Faithful encoding:** This is the paper's locality-preserving construction at
the `2ζ` scale needed by the completion-to-measurement proof of
`thm:orthonormalization`. -/
theorem leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (ζ : Error) (hζ : 0 ≤ ζ)
    (hsource :
      ∑ a, ev ψ
        ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
          (leftLiftedMeasurement (ιB := ιB) A).outcome a *
            (leftLiftedMeasurement (ιB := ιB) A).outcome a) ≤ 2 * ζ) :
    ∃ P : ProjSubMeas Outcome ιA,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
        (orthonormalizationMainLemmaError ζ) := by
  classical
  let : DecidableEq Outcome := Classical.decEq Outcome
  rcases QuantumState.IsNormalized.nonempty (ι := ιA × ιB) hψ with ⟨⟨i, j⟩⟩
  let : Nonempty ιA := ⟨i⟩
  let : Nonempty ιB := ⟨j⟩
  let φ : QuantumState ιA := leftMarginalState ψ
  have hφ : φ.IsNormalized := leftMarginalState_isNormalized hψ
  have hterm : ∀ a : Outcome,
      ev ψ
        ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
          (leftLiftedMeasurement (ιB := ιB) A).outcome a *
            (leftLiftedMeasurement (ιB := ιB) A).outcome a) =
      ev φ (A.outcome a - A.outcome a * A.outcome a) := by
    intro a
    simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ) (X := A.outcome a - A.outcome a * A.outcome a))
  have hsourceLocal :
      ∑ a, ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ := by
    simpa [hterm] using hsource
  by_cases hζ_small : ζ ≤ 1 / (4 : Error)
  · have hprojective : projectiveNonMeasurement φ A ζ :=
      projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full
        φ A ζ hφ hsourceLocal
    obtain ⟨R, hR⟩ := hprojective
    have hSpectralLocal : SpectralTruncationStatement φ A ζ :=
      spectralTruncationStatement_of_witness φ A ζ R hR
    obtain ⟨qLayer, hRank⟩ :=
      projectiveLowRankSum_of_spectralTruncationStatement φ A ζ hφ hζ
        hζ_small hSpectralLocal hsourceLocal
    by_cases hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))
    · let := hsigma
      obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
        pQApprox_ofRankReductionSigmaRangePositiveGram φ A ζ hRank hφ hζ hζ_small
      have hAQ :
          SDDOpRel φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
            (constOpFamily data.qLayer.q) (roundingToProjectiveError ζ) := by
        simpa [hq] using hRank.toSigmaRangeQLayer.closeness
      have hAP_local :
          SDDOpRel φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
            (constOpFamily (PFamily data)) (orthonormalizationMainLemmaError ζ) := by
        exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
          (constOpFamily (PFamily data))
          (2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ))
          (orthonormalizationMainLemmaError ζ)
          (MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
            (constOpFamily data.qLayer.q)
            (constOpFamily (PFamily data))
            (roundingToProjectiveError ζ) (30 * zetaQuarterRoot ζ) hAQ hQP)
          (projectivizationRepair_small_error_bound hζ hζ_small)
      have hLifted :
          SDDOpRel ψ (uniformDistribution Unit)
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (PFamily data))
            (orthonormalizationMainLemmaError ζ) := by
        refine MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq
          (ιA := ιA) (ιB := ιB) ψ φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
          (constOpFamily (PFamily data))
          (orthonormalizationMainLemmaError ζ) ?_ hAP_local
        intro X
        exact leftMarginal_ev_eq ψ X
      exact ⟨qxpProjSubMeas data,
        sddRel_of_leftPlaced_sddOpRel
          (R := PFamily data) (P := qxpProjSubMeas data)
          (fun a => by
            rw [qxpProjSubMeas_outcome]
            rfl)
          hLifted⟩
    · have hQzero_rank : ∀ a : Outcome, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos : 0 < (qLayer.q.outcome a).rank := Nat.pos_of_ne_zero hrank
        have : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin Outcome a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hQzero : ∀ a : Outcome, qLayer.q.outcome a = 0 := by
        intro a
        exact matrix_eq_zero_of_rank_eq_zero (qLayer.q.outcome a) (hQzero_rank a)
      have hQ_lifted :
          SDDOpRel ψ (uniformDistribution Unit)
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) qLayer.q)
            (roundingToProjectiveError ζ) := by
        refine MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq
          (ιA := ιA) (ιB := ιB) ψ φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ιA))
          (constOpFamily qLayer.q) (roundingToProjectiveError ζ) ?_ hRank.closeness
        intro X
        exact leftMarginal_ev_eq ψ X
      exact ⟨zeroProjSubMeas (Outcome := Outcome) (ι := ιA),
        ⟨le_trans
          (sddRel_of_leftPlaced_sddOpRel
            (R := qLayer.q) (P := zeroProjSubMeas (Outcome := Outcome) (ι := ιA))
            hQzero hQ_lifted).squaredDistanceBound
          (roundingToProjectiveError_le_orthonormalizationMainLemmaError
            hζ hζ_small)⟩⟩
  · refine ⟨zeroProjSubMeas (Outcome := Outcome) (ι := ιA), ?_⟩
    have hzero :
        qSDD ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB)
            (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas) ≤ 1 :=
      qSDD_leftPlaced_zeroProjSubMeas_le_one ψ hψ A.toSubMeas
    have hbound : 1 ≤ orthonormalizationMainLemmaError ζ :=
      one_le_orthonormalizationMainLemmaError_of_quarter_lt (lt_of_not_ge hζ_small)
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily]
      using (le_trans hzero hbound)



/-- Square-register form of the locality-preserving repair theorem.

This is the specialization of
`leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul` to
the case where the two tensor factors have the same carrier.

Paper origin: `references/ldt-paper/orthonormalization.tex:862-1194`
(`\label{lem:P-Q-approx}` and the final projectivization-repair assembly).

**Faithful encoding:** This is the square-register specialization of the
source-faithful left-register construction above. -/
theorem leftLiftedProjectivizationRepair_of_sourceAlmostProjective_two_mul
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error) (hζ : 0 ≤ ζ)
    (hsource :
      ∑ a, ev ψ
        ((leftLiftedMeasurement (ιB := ι) A).outcome a -
          (leftLiftedMeasurement (ιB := ι) A).outcome a *
            (leftLiftedMeasurement (ιB := ι) A).outcome a) ≤ 2 * ζ) :
    ∃ P : ProjSubMeas Outcome ι,
      RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (ProjSubMeas.liftLeft P) (orthonormalizationMainLemmaError ζ) := by
  obtain ⟨P, hP⟩ :=
    leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
      (ψ := ψ) (hψ := hψ) (A := A) (ζ := ζ) hζ hsource
  refine ⟨P, ?_⟩
  constructor
  simpa [leftLiftedMeasurement, ProjSubMeas.liftLeft, SubMeas.liftLeft,
    leftPlacedSubMeas]
    using hP



end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


